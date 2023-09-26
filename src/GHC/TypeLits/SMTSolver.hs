{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module GHC.TypeLits.SMTSolver
  ( plugin )
where

import Control.Arrow ((***))
import Control.Monad ( (<=<), forM )
import Control.Monad.Extra ( partitionM )
import Control.Monad.Trans.Writer

import Data.Functor ( (<&>) )
import Data.List ( nub, intersect, stripPrefix )
import Data.Maybe ( mapMaybe, catMaybes )
import Text.Read ( readMaybe )

import GHC.Builtin.Types
  ( cTupleTyCon
  , naturalTy
  , promotedTrueDataCon
  , promotedFalseDataCon
  )
import GHC.Builtin.Types.Literals
  ( typeNatCmpTyCon
  , typeNatAddTyCon
  , typeNatSubTyCon
  , typeNatMulTyCon
  , typeNatExpTyCon
  )

import GHC.Core.Type ( typeKind )

import GHC.Data.FastString ( fsLit )
import GHC.Driver.Plugins ( Plugin (..), defaultPlugin )
import GHC.Plugins ( mkTcOcc )

import GHC.Core.Predicate ( classifyPredType, EqRel (NomEq), Pred (..) )
import GHC.Core.TyCon ( TyCon )
import GHC.Core.TyCo.Rep ( Type (..), TyLit(NumTyLit) )
import GHC.Types.Name ( getOccName, occNameString, getName, nameStableString )

import GHC.Tc.Plugin ( TcPluginM, tcPluginIO, tcLookupTyCon )
import GHC.Tc.Types ( TcPlugin (..), TcPluginSolveResult (..) )
import GHC.TcPluginM.Extra ( tracePlugin, lookupName, lookupModule, evByFiat )

import GHC.Tc.Types.Constraint ( Ct, ctEvidence, ctEvPred )
import GHC.Tc.Types.Evidence ( EvBindsVar, EvTerm )

import GHC.Types.Unique.FM ( emptyUFM )

import GHC.Tc.Utils.TcType

import GHC.Unit.Module ( mkModuleName )
import GHC.Utils.Outputable

import qualified SimpleSMT as SMT

plugin :: Plugin
plugin =
  defaultPlugin
  { tcPlugin = const $ Just $ smtSolverPlugin defaultOpts
    -- Using other solvers except cvc5 is not supported
    -- tcPlugin = fmap (smtSolverPlugin . foldr id defaultOpts) . traverse parseArgument
  }
  where
    parseArgument (readMaybe <=< stripPrefix "cmd=" -> Just cmd) =
      Just (\ opts -> opts { optsSolverCmd = cmd })
    parseArgument (readMaybe <=< stripPrefix "arg=" -> Just arg) =
      Just (\ opts@Opts{ optsSolverArgs = args } -> opts { optsSolverArgs = arg : args })
    parseArgument _ = Nothing

    defaultOpts = Opts { optsSolverCmd = "cvc5", optsSolverArgs = ["--incremental"] }

data Opts = Opts { optsSolverCmd :: String
                 , optsSolverArgs :: [String]
                 }

powerSymbol :: String
powerSymbol = "^"

verboseLevel :: Int
verboseLevel = 1

exp' :: SMT.SExpr -> SMT.SExpr -> SMT.SExpr
exp' x y = SMT.fun powerSymbol [x, y]

type TcS = (TyCon, TyCon)
data S = S
  { smtSolver :: SMT.Solver
  , _typeCons  :: TcS
  }

smtSolverPlugin :: Opts -> TcPlugin
smtSolverPlugin  opts = tracePlugin "SMTSolver"
  TcPlugin { tcPluginInit = smtSolverStart opts
           , tcPluginSolve = smtSolverSolve
           , tcPluginRewrite = const emptyUFM
           , tcPluginStop = smtSolverStop
           }

initSolver :: Opts -> TcPluginM SMT.Solver
initSolver opts@(Opts solver args) = tcPluginIO $ do
  logger <- SMT.newLogger verboseLevel
  solver <- SMT.newSolver solver args (Just logger)
  SMT.setLogic solver "QF_NIA"
  return solver

lookupTypeCons :: TcPluginM TcS
lookupTypeCons = do
    ordCondModule <- lookupModule ordModuleName basePackage
    ordCondT <- look ordCondModule "OrdCond"

    typeErrModule <- lookupModule typeErrModuleName basePackage
    assertT <- look typeErrModule "Assert"

    return (ordCondT, assertT)
  where
    look md s = tcLookupTyCon =<< lookupName md (mkTcOcc s)

    ordModuleName = mkModuleName "Data.Type.Ord"
    typeErrModuleName = mkModuleName "GHC.TypeError"
    basePackage = fsLit "base"

smtSolverStart :: Opts -> TcPluginM S
smtSolverStart opts = S <$> initSolver opts <*> lookupTypeCons

smtSolverStop :: S -> TcPluginM ()
smtSolverStop s = do
  -- cvc5 ignores (exit) command, so terminate by syntax error
  tcPluginIO $ SMT.command (smtSolver s) $ SMT.const "!"
  _exitCode <- tcPluginIO $ SMT.stop (smtSolver s)
  return ()

smtSolverSolve :: S -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
-- Ignore simplification of given constraints
smtSolverSolve _ _ _ [] = return $ TcPluginOk [] []

smtSolverSolve (S solver tcs) _ givens wanteds =
  let
    (givenSExprs,  vs)  = unzip $ mapMaybe (toSExpr tcs) givens
    (wantedSExprs, vs1) = unzip $ mapMaybe (toSExpr tcs) wanteds
    (vars, exprs) = (concat *** concat) $ unzip (vs ++ vs1)
  in tcPluginIO $ SMT.inNewScope solver $ do

    varDecls <- mapM (constructDeclaration solver) $ nub vars

    -- Assert that both variables and all the intermediate expressions are natural numbers (>= 0)
    mapM_ (assertNaturalness solver) varDecls
    mapM_ (assertNaturalness solver) exprs

    -- Assert given predicates
    mapM_ (SMT.assert solver . exprExpr) givenSExprs

    checkForAll solver wantedSExprs <&>
      \case (solved,[]) -> TcPluginOk (map (attachEvidence . exprCt) solved) []
            _ -> TcPluginOk [] []
  where
    constructDeclaration :: SMT.Solver -> String -> IO SMT.SExpr
    constructDeclaration s name = SMT.declare s name SMT.tInt

    assertNaturalness :: SMT.Solver -> SMT.SExpr -> IO ()
    assertNaturalness s sexpr = do
      SMT.assert s $ SMT.leq (SMT.int 0) sexpr
            
    checkForAll :: SMT.Solver -> [Expr] -> IO ([Expr], [Expr])
    checkForAll s wanteds = SMT.inNewScope s $
      -- for all x (P(x) => Q(x)) <=> not exists x P(x) ^ ¬Q(x)
      partitionM (\w -> (SMT.assert s (SMT.not $ exprExpr w) >> SMT.check s) <&> (SMT.Unsat ==)) wanteds

    attachEvidence :: Ct -> (EvTerm,Ct)
    attachEvidence ct = (evByFiat "SMTSolver" q q, ct)
      where q = TyConApp promotedTrueDataCon []

data Expr = Expr
  { exprCt :: Ct
  , exprExpr :: SMT.SExpr
  }

-- | Convert constraints to S-Expressions
--
-- (x - 2) * (4 * y) => (* (- x 2) (* 4 y))
-- With variables: x, y
--   and subexpressions: (- x 2), (* 4 y)
toSExpr :: TcS
        -- ^ Looked up type constructors for OrdCond and Assert
        -> Ct
        -- ^ Constraint to convert
        -> Maybe (Expr,([String],[SMT.SExpr]))
        -- ^ Resulting S-Expression with all the variables and sub-expressions
toSExpr (ordCondT, assertT) ct =
  case classifyPredType $ ctEvPred $ ctEvidence ct of
    EqPred NomEq t1 t2 -> go t1 t2
    IrredPred p        -> go2 p
    _                  -> Nothing
  where
    go (TyConApp tc xs) (TyConApp tc' ys)
      | tc == tc'
      , null ([tc, tc'] `intersect` [ typeNatAddTyCon, typeNatSubTyCon
                                    , typeNatMulTyCon, typeNatExpTyCon])
      = case filter (not . uncurry eqType) (zip xs ys) of
          [(x,y)]
            | isNatKind (typeKind x)
            , isNatKind (typeKind y)
            , let (x',(kv,uv)) = runWriter (termToSExpr x)
            , let (y',(kv1,uv1)) = runWriter (termToSExpr y)
            -> Just (Expr ct (SMT.eq x' y'), (kv ++ kv1, uv ++ uv1))
          _ -> Nothing
      | tc == ordCondT, [_, cmp, lt, eq, gt] <- xs
      , TyConApp tcCmpNat [x, y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt, TyConApp eqTc [] <- eq, TyConApp gtTc [] <- gt
      , ltTc == promotedTrueDataCon
      , eqTc == promotedTrueDataCon
      , gtTc == promotedFalseDataCon
      , let (x',(kv,uv)) = runWriter (termToSExpr x)
      , let (y',(kv1,uv1)) = runWriter (termToSExpr y)
      = case tc' of
          _ | tc' == promotedTrueDataCon
            -> Just (Expr ct (SMT.leq x' y'), (kv ++ kv1, uv ++ uv1))
          _ | tc' == promotedFalseDataCon
            -> Just (Expr ct (SMT.gt x' y'), (kv ++ kv1, uv ++ uv1))
          _ -> Nothing
      | tc == assertT
      , tc' == cTupleTyCon 0
      , [] <- ys, [TyConApp ordCondTc zs, _] <- xs
      , ordCondTc == ordCondT
      , [_, cmp, lt, eq, gt] <- zs
      , TyConApp tcCmpNat [x, y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt, TyConApp eqTc [] <- eq, TyConApp gtTc [] <- gt
      , ltTc == promotedTrueDataCon
      , eqTc == promotedTrueDataCon
      , gtTc == promotedFalseDataCon
      , let (x',(kv,uv)) = runWriter (termToSExpr x)
      , let (y',(kv1,uv1)) = runWriter (termToSExpr y)
      = Just (Expr ct (SMT.leq x' y'), (kv ++ kv1, uv ++ uv1))

    go x y
      | isNatKind (typeKind x)
      , isNatKind (typeKind y)
      , let (x',(kv,uv)) = runWriter (termToSExpr x)
      , let (y',(kv1,uv1)) = runWriter (termToSExpr y)
      = Just (Expr ct (SMT.eq x' y'), (kv ++ kv1, uv ++ uv1))
      | otherwise
      = Nothing

    go2 (TyConApp tc ys)
      | tc == assertT
      , [TyConApp ordCondTc xs, _] <- ys
      , ordCondTc == ordCondT
      , [_, cmp, lt, eq, gt] <- xs
      , TyConApp tcCmpNat [x, y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt, TyConApp eqTc [] <- eq, TyConApp gtTc [] <- gt
      , ltTc == promotedTrueDataCon
      , eqTc == promotedTrueDataCon
      , gtTc == promotedFalseDataCon
      , let (x',(kv,uv)) = runWriter (termToSExpr x)
      , let (y',(kv1,uv1)) = runWriter (termToSExpr y)
      = Just (Expr ct (SMT.leq x' y'), (kv ++ kv1, uv ++ uv1))

    go2 _ = Nothing

    isNatKind = (`eqType` naturalTy)

termToSExpr :: Type -> Writer ([String], [SMT.SExpr]) SMT.SExpr
termToSExpr ty | Just ty1 <- coreView ty = termToSExpr ty1
termToSExpr (LitTy (NumTyLit i)) = return n
  where n = SMT.int i
termToSExpr (TyVarTy v) =
  let cName = nameStableString $ getName v
      c     = SMT.const cName
  in tell ([cName],[]) >> return c
termToSExpr (TyConApp tc [x, y]) =
  do
    expr <- go tc <$> termToSExpr x <*> termToSExpr y
    tell ([],[expr])
    return expr
  where
    go :: TyCon -> SMT.SExpr -> SMT.SExpr -> SMT.SExpr
    go tc
      | tc == typeNatAddTyCon = SMT.add
      | tc == typeNatSubTyCon = SMT.sub
      | tc == typeNatMulTyCon = SMT.mul
      | tc == typeNatExpTyCon = exp'
termToSExpr t = error "Simplification inside type application is not supported"
