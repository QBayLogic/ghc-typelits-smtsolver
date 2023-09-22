{-# LANGUAGE TupleSections #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE LambdaCase #-}

module SMTSolver
  ( plugin )
where

import Control.Arrow ((***))
import Control.Monad ( (<=<), {- filterM -} )
import Control.Monad.Extra ( partitionM )

import Data.List ( nub, intersect, stripPrefix )
import Data.Maybe ( mapMaybe )
import Text.Read ( readMaybe )

import GHC.Builtin.Types ( cTupleTyCon )
import GHC.Builtin.Types ( naturalTy )
import GHC.Builtin.Types ( promotedTrueDataCon, promotedFalseDataCon )
import GHC.Builtin.Types.Literals
  ( typeNatCmpTyCon, typeNatAddTyCon, typeNatSubTyCon, typeNatMulTyCon, typeNatExpTyCon )

import GHC.Core.Type (typeKind)

import GHC.Data.FastString (fsLit)
import GHC.Driver.Plugins ( Plugin (..), defaultPlugin )
import GHC.Plugins (mkTcOcc)

import GHC.Core.Predicate ( classifyPredType, EqRel (NomEq), Pred (..) )
import GHC.Core.TyCon ( TyCon )
import GHC.Core.TyCo.Rep ( Type (..), TyLit(NumTyLit) )
import GHC.Types.Name ( getOccName, occNameString, getName, nameStableString )

import GHC.Tc.Plugin ( TcPluginM, tcPluginIO, {- tcPluginTrace, -} tcLookupTyCon )
import GHC.Tc.Types ( TcPlugin (..), TcPluginSolveResult (..) )
import GHC.TcPluginM.Extra ( tracePlugin, lookupName, lookupModule, evByFiat )

import GHC.Tc.Types.Constraint ( Ct, ctEvidence, ctEvPred )
import GHC.Tc.Types.Evidence ( EvBindsVar, EvTerm )

import GHC.Types.Unique.FM ( emptyUFM )

import GHC.Tc.Utils.TcType

import GHC.Unit.Module (mkModuleName)
import GHC.Utils.Outputable

import qualified SimpleSMT as SMT
import Data.List.Extra (intercalate)

plugin :: Plugin
plugin = defaultPlugin {
  tcPlugin = fmap (smtSolverPlugin . foldr id defaultOpts) . traverse parseArgument
  }
  where
    parseArgument (readMaybe <=< stripPrefix "cmd=" -> Just cmd)
      = Just (\ opts -> opts { solverCmd = cmd })
    parseArgument (readMaybe <=< stripPrefix "arg=" -> Just arg)
      = Just (\ opts@Opts{ solverArgs = args } -> opts { solverArgs = arg : args })
    parseArgument _ = Nothing

    defaultOpts = Opts { solverCmd = "z3", solverArgs = ["-smt2", "-in"], noExponent = False }

data Opts = Opts { solverCmd :: String
                 , solverArgs :: [String]
                 , noExponent :: Bool
                 }

powerSymbol :: String
powerSymbol = "^"

verboseLevel :: Int
verboseLevel = 0

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
initSolver opts = tcPluginIO $ do
  logger <- SMT.newLogger verboseLevel
  solver <- SMT.newSolver (solverCmd opts) (solverArgs opts) (Just logger)
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
smtSolverStart opts = do
    solver <- initSolver opts
    _power <- tcPluginIO $ intPowerFunc solver
    tcs <- lookupTypeCons
    return $ S solver tcs
  where intPowerFunc s = SMT.defineFunRec s powerSymbol [("base", SMT.tInt), ("exp", SMT.tInt)] SMT.tInt power
          where power func =
                  let base     = SMT.symbol "base"
                      exponent' = SMT.symbol "exp"
                      zero     = SMT.int 0
                      one      = SMT.int 1
                  in
                    -- if exponent == 0 then 1 else base * (base ^ exponent)
                    SMT.ite (SMT.eq exponent' zero) one (SMT.mul base (SMT.app func [base, (SMT.sub exponent' one)]))

smtSolverStop :: S -> TcPluginM ()
smtSolverStop s = do
  -- do something with the exit code
  -- cvc5 ignores 
  _exitCode <- tcPluginIO $ SMT.stop (smtSolver s)
  return ()

smtSolverSolve :: S -> EvBindsVar -> [Ct] -> [Ct] -> TcPluginM TcPluginSolveResult
smtSolverSolve _ _ _ [] = return $ TcPluginOk [] []
smtSolverSolve (S solver tcs) _ givens wanteds =
  let
    (givenSExprs, vs)   = unzip $ mapMaybe (toSExpr tcs) givens
    (wantedSExprs, vs1) = unzip $ mapMaybe (toSExpr tcs) wanteds
    (kv, uv) = (concat *** concat) $ unzip (vs ++ vs1)
  in tcPluginIO $ SMT.inNewScope solver $ do

    uvDecl <- mapM (conDecl solver) $ nub uv
    kvDecl <- mapM (conDecl solver) $ nub kv

    mapM_ (assertNaturalness solver . snd) $ uvDecl ++ kvDecl
    
    -- Assert given predicates
    mapM_ (SMT.assert solver . getExpr) givenSExprs

    -- TODO: also produce contradictions
    t <- getUnknownBindings solver (map getExpr wantedSExprs) (map snd uvDecl)
    case t of
      Right binds -> do
        mapM_ (SMT.assert solver . uncurry SMT.eq) $ map (\(expr, val) -> (expr, SMT.value val)) binds
        (solved, unsolved) <- (map getCt *** map getCt) <$> partitionM (checkConstraint solver) wantedSExprs
        case unsolved of
          [] -> return $ TcPluginOk
                (map ((,) <$> attachEvidence <*> id) solved)
                (mapMaybe (uncurry wantedsFromBinds . (fst *** id)) $ zip uvDecl binds)
          _ -> return $ TcPluginContradiction unsolved
      Left contradictionNames -> return $ TcPluginContradiction $ map getCt $ filter ((`elem` contradictionNames) . getName') (givenSExprs ++ wantedSExprs)
  where
    conDecl :: SMT.Solver -> Var -> IO (Type, SMT.SExpr)
    conDecl s (Var t n) = (t,) <$> SMT.declare s n SMT.tInt

    checkConstraint :: SMT.Solver -> Expr -> IO Bool
    checkConstraint s (Expr _ _ sexpr) = SMT.inNewScope s $ do
      SMT.assert s $ SMT.not sexpr
      fmap (== SMT.Unsat) $ SMT.check s

    wantedsFromBinds :: Type -> (SMT.SExpr, SMT.Value) -> Maybe Ct
    wantedsFromBinds _ _ = Nothing
    -- wantedsFromBinds (TyConApp tc xs) (_, val) = Just $ TyFamLHS tc xs

    assertNaturalness :: SMT.Solver -> SMT.SExpr -> IO ()
    assertNaturalness s sexpr = SMT.assert s $ SMT.leq (SMT.int 0) sexpr

    attachEvidence :: Ct -> EvTerm
    attachEvidence _ = evByFiat "SMTSolver" q q
      where q = (TyConApp promotedTrueDataCon [])

getUnknownBindings :: SMT.Solver -> [SMT.SExpr] -> [SMT.SExpr] -> IO (Either [String] [(SMT.SExpr, SMT.Value)])
getUnknownBindings _ _ []   = Right <$> return []
getUnknownBindings s wanteds vars = SMT.inNewScope s $ mapM (SMT.assert s) wanteds >> SMT.check s >>= \case
  SMT.Sat   -> Right <$> SMT.getExprs s vars
  SMT.Unsat -> Left  <$> SMT.getUnsatCore s
  _         -> Right <$> return []

data Expr = Expr { getCt :: Ct
                 , getName' :: String
                 , getExpr :: SMT.SExpr
                 }

data Var  = Var Type String

instance Eq Var where
  -- (Var t1 s1) == (Var t2 s2) = eqType t1 t2 && s1 == s2
  (Var t1 s1) == (Var t2 s2) = s1 == s2

toSExpr :: TcS -> Ct -> Maybe (Expr,([Var],[Var]))
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
            , let (x', (kv, uv)) = termToSExpr x
            , let (y', (kv1, uv1)) = termToSExpr y
            -> Just ((Expr ct "" (SMT.eq x' y')), (kv ++ kv1, uv ++ uv1))
          _ -> Nothing
      | tc == ordCondT, [_, cmp, lt, eq, gt] <- xs
      , TyConApp tcCmpNat [x, y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt, TyConApp eqTc [] <- eq, TyConApp gtTc [] <- gt
      , ltTc == promotedTrueDataCon
      , eqTc == promotedTrueDataCon
      , gtTc == promotedFalseDataCon
      , let (x',(kv,uv)) = termToSExpr x
      , let (y',(kv1,uv1)) = termToSExpr y
      = case tc' of
          _ | tc' == promotedTrueDataCon
            -> Just ((Expr ct "" (SMT.leq x' y')), (kv ++ kv1, uv ++ uv1))
          _ | tc' == promotedFalseDataCon
            -> Just ((Expr ct "" (SMT.gt x' y')), (kv ++ kv1, uv ++ uv1))
          _ -> Nothing
      | tc == assertT
      , tc' == (cTupleTyCon 0)
      , [] <- ys, [TyConApp ordCondTc zs, _] <- xs
      , ordCondTc == ordCondT
      , [_, cmp, lt, eq, gt] <- zs
      , TyConApp tcCmpNat [x, y] <- cmp
      , tcCmpNat == typeNatCmpTyCon
      , TyConApp ltTc [] <- lt, TyConApp eqTc [] <- eq, TyConApp gtTc [] <- gt
      , ltTc == promotedTrueDataCon
      , eqTc == promotedTrueDataCon
      , gtTc == promotedFalseDataCon
      , let (x',(kv,uv)) = termToSExpr x
      , let (y',(kv1,uv1)) = termToSExpr y
      = Just ((Expr ct "" (SMT.leq x' y')), (kv ++ kv1, uv ++ uv1))

    go x y
      | isNatKind (typeKind x)
      , isNatKind (typeKind y)
      , let (x', (kv,uv)) = termToSExpr x
      , let (y',(kv1,uv1)) = termToSExpr y
      = Just ((Expr ct "" (SMT.eq x' y')), (kv ++ kv1, uv ++ uv1))
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
      , let (x',(kv,uv)) = termToSExpr x
      , let (y',(kv1,uv1)) = termToSExpr y
      = Just ((Expr ct "" (SMT.leq x' y')), (kv ++ kv1, uv ++ uv1))

    go2 _ = Nothing

    isNatKind = (`eqType` naturalTy)

termToSExpr :: Type -> (SMT.SExpr, ([Var], [Var]))
termToSExpr ty | Just ty1 <- coreView ty = termToSExpr ty1
termToSExpr t@(TyVarTy v) = (c,([Var t cName],[]))
  where cName = nameStableString $ getName v
        c = SMT.const cName
termToSExpr (LitTy (NumTyLit i)) = (n, ([],[]))
  where n = SMT.int i
termToSExpr (TyConApp tc [x, y])
  | tc == typeNatAddTyCon = (SMT.add x' y', (kvs, uvs))
  | tc == typeNatSubTyCon = (SMT.sub x' y', (kvs, uvs))
  | tc == typeNatMulTyCon = (SMT.mul x' y', (kvs, uvs))
  | tc == typeNatExpTyCon = (exp'    x' y', (kvs, uvs))
    where (x', (kv,uv)) = termToSExpr x
          (y', (kv1,uv1)) = termToSExpr y
          kvs = kv ++ kv1
          uvs = uv ++ uv1
-- Generate symbol for yet not known Type Function
termToSExpr t = (s,([],[Var t sName]))
  where sName = showSDocUnsafe $ ppr t
        s = SMT.const sName

{-
import Data.Proxy
import GHC.TypeLits
import GHC.TypeNats

f :: (0 <= x) => Proxy x -> Proxy 0
f = id
-}
