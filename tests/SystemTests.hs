import Test.Tasty
import Test.Tasty.HUnit
  ( testCase
  , (@=?)
  )

import SoPSat.SoP
  ( SoPE(..)
  , OrdRel(..)
  , (|+|)
  , (|-|)
  , (|*|)
  , (|^|)
  )
import qualified SoPSat.SoP as SoP
import SoPSat.Satisfier
  ( SolverState
  , evalStatements
  , declare
  , assert
  , unify
  )
import Data.Monoid (Any)


type SolveTestCase   = SolverState String String Bool
type SolveTestResult = Maybe Bool

type UnifyTestCase   = SolverState String String [SoPE String String]
type UnifyTestResult = Maybe [SoPE String String]

equalityGiven1 :: SolveTestCase
equalityGiven1 =
  let
    one = SoP.int 1
    m   = SoP.cons "m"
    n   =  SoP.cons "n"
    n1  = SoP.cons "n1"
  in do
    declare (SoPE m (n1 |+| one) EqR)
    assert (SoPE (m |+| n) (n |+| n1 |+| one) EqR)

runEqualityGiven1 :: SolveTestResult
runEqualityGiven1 = evalStatements equalityGiven1

equalityGiven2 :: SolveTestCase
equalityGiven2 =
  let
    one = SoP.int 1
    m  = SoP.cons "m"
    n  = SoP.cons "n"
    n1 = SoP.cons "n1"
  in do
    declare (SoPE m (n1 |+| one) EqR)
    assert (SoPE (m |*| n) (n |+| n |*| n1) EqR)

runEqualityGiven2 :: SolveTestResult
runEqualityGiven2 = evalStatements equalityGiven2

equalityGiven3 :: SolveTestCase
equalityGiven3 =
  let
    one = SoP.int 1
    m  = SoP.cons "m"
    n  = SoP.cons "n"
    n1 = SoP.cons "n1"
  in do
    declare (SoPE m (n1 |+| one) EqR)
    assert (SoPE (n |^| m) (n |*| n |^| n1) EqR)

runEqualityGiven3 :: SolveTestResult
runEqualityGiven3 = evalStatements equalityGiven3

transitivity :: SolveTestCase
transitivity =
  let
    i = SoP.cons "i"
    j = SoP.cons "j"
    l = SoP.cons "l"
    k = SoP.cons "k"
  in do
    declare (SoPE i j LeR)
    declare (SoPE k l LeR)
    assert (SoPE (i |+| k) (j |+| l) LeR)
    -- assert (SoPE (i |+| k) (k |+| l) LeR)

runTransitivity :: SolveTestResult
runTransitivity = evalStatements transitivity

antisymmetryZero :: SolveTestCase
antisymmetryZero =
  let
    z = SoP.int 0
    x = SoP.cons "x"
  in do
    declare (SoPE x z LeR)
    assert (SoPE x z EqR)

runAntisymmetryZero :: SolveTestResult
runAntisymmetryZero = evalStatements antisymmetryZero

antisymmetryNonZero :: SolveTestCase
antisymmetryNonZero =
  let
    z = SoP.int 42
    x = SoP.cons "x"
  in do
    declare (SoPE x z LeR)
    declare (SoPE z x LeR)
    assert (SoPE x z EqR)

runAntisymmetryNonZero :: SolveTestResult
runAntisymmetryNonZero = evalStatements antisymmetryNonZero

lemma2 :: SolveTestCase
lemma2 =
  let
    o = SoP.int 1
    j = SoP.cons "j"
    n = SoP.cons "n"
  in do
    declare (SoPE j n LeR)
    declare (SoPE o (n |-| j) LeR)
    assert (SoPE (o |+| j) n LeR)

runLemma2 :: SolveTestResult
runLemma2 = evalStatements lemma2

trueInEq :: SolveTestCase
trueInEq =
  let
    two = SoP.int 2
    three = SoP.int 3
    four = SoP.int 4
    x = SoP.cons "x"
    inEq1 = two |^| x |+| three |*| x |^| two |+| three
    inEq2 = x |^| three |-| two |*| x |^| two |+| four
  in
    assert (SoPE inEq2 inEq1 LeR)

runTrueInEq :: SolveTestResult
runTrueInEq = evalStatements trueInEq

falseInEq :: SolveTestCase
falseInEq =
  let
    two = SoP.int 2
    three = SoP.int 3
    four = SoP.int 4
    x = SoP.cons "x"
    inEq1 = two |^| x |+| x |^| two |+| three
    inEq2 = x |^| three |-| two |*| x |^| two |+| four
  in
    assert (SoPE inEq1 inEq2 GeR)

runFalseInEq :: SolveTestResult
runFalseInEq = evalStatements falseInEq

falseInEq2 :: SolveTestCase
falseInEq2 =
  let
    one = SoP.int 1
    m   = SoP.cons "m"
    rp  = SoP.cons "rp"
  in do
    declare (SoPE one m LeR)
    declare (SoPE m rp LeR)
    assert (SoPE one (rp |-| m) LeR)

runFalseInEq2 :: SolveTestResult
runFalseInEq2 = evalStatements falseInEq2

overlapInEq :: SolveTestCase
overlapInEq =
  let
    t = SoP.int 2
    f = SoP.int 4
    x = SoP.cons "x"
  in do
    declare (SoPE f x LeR)
    declare (SoPE t x LeR)
    assert (SoPE t x LeR)

runOverlapInEq :: SolveTestResult
runOverlapInEq = evalStatements overlapInEq

eqSubst :: SolveTestCase
eqSubst =
  let
    o = SoP.int 1
    x = SoP.cons "x"
    m = SoP.cons "m"
    m1 = SoP.cons "m1"
    n1 = SoP.cons "n1"
    n2 = SoP.cons "n2"
  in do
    declare (SoPE (x |+| o) (n1 |+| m |+| o) EqR)
    declare (SoPE m n1 EqR)
    declare (SoPE n1 (n2 |+| m1 |+| o) EqR)
    assert (SoPE (o |+| n2 |+| m1) n1 EqR)

runEqSubst :: SolveTestResult
runEqSubst = evalStatements eqSubst

eqSubst2 :: SolveTestCase
eqSubst2 =
  let
    o = SoP.int 1
    t = SoP.int 2
    y = SoP.cons "y"
    x = SoP.cons "x"
  in do
    declare (SoPE o y LeR)
    declare (SoPE (o |+| x) (t |*| y) EqR)
    assert (SoPE (t |*| y |-| o) x EqR)

runEqSubst2 :: SolveTestResult
runEqSubst2 = evalStatements eqSubst2

multistep :: SolveTestCase
multistep =
  let
    o = SoP.int 1
    t = SoP.int 2
    n1 = SoP.cons "n1"
    n2 = SoP.cons "n2"
  in do
    declare (SoPE o n1 LeR)
    declare (SoPE (t |*| n2) n1 EqR)
    r1 <- assert (SoPE (t |*| n2 |-| o) (n1 |-| o) EqR)
    r2 <- assert (SoPE o n2 LeR)
    return (r1 && r2)

runMultistep :: SolveTestResult
runMultistep = evalStatements multistep

multistep2 :: SolveTestCase
multistep2 =
  let
    o = SoP.int 1
    m = SoP.cons "m"
    n = SoP.cons "n"
    n1 = SoP.cons "n1"
    n2 = SoP.cons "n2"
  in do
    declare (SoPE m (n1 |+| o) EqR)
    declare (SoPE (m |+| n) (n2 |+| o) EqR)
    assert (SoPE (n1 |+| n) n2 EqR)

runMultistep2 :: SolveTestResult
runMultistep2 = evalStatements multistep2

step3 :: SolveTestCase
step3 =
  let
    o = SoP.int 1
    t = SoP.int 2
    m = SoP.cons "m"
    n = SoP.cons "n"
    n1 = SoP.cons "n1"
  in do
    declare (SoPE (o |+| n) m EqR)
    declare (SoPE (o |+| n1) m EqR)
    r1 <- assert (SoPE n n1 EqR)
    r2 <- assert (SoPE (t |+| t |*| n) (t |*| m) EqR)
    return (r1 && r2)

runStep3 :: SolveTestResult
runStep3 = evalStatements step3

implication :: SolveTestCase
implication =
  let
    t = SoP.int 2
    m = SoP.cons "m"
    n = SoP.cons "n"
  in do
    declare (SoPE t (t |^| (n |+| m)) LeR)
    assert (SoPE t (t |^| (m |+| n)) LeR)

runImplication :: SolveTestResult
runImplication = evalStatements implication

func1 :: SolveTestCase
func1 =
  let
    a = SoP.cons "a"
    b = SoP.cons "b"
    c = SoP.cons "c"
    eq1 = a |+| SoP.func "max" [a |+| b, c]
    eq2 = SoP.func "max" [b |+| a, c] |+| a
  in assert (SoPE eq1 eq2 EqR)

runFunc1 :: SolveTestResult
runFunc1 = evalStatements func1

func2 :: SolveTestCase
func2 =
  let
    a = SoP.cons "a"
    b = SoP.cons "b"
    c = SoP.cons "c"
    eq1 = a |+| SoP.func "bar" [a |+| b, c]
    eq2 = SoP.func "bar" [c, b |+| a] |+| a
  in assert (SoPE eq1 eq2 EqR)

runFunc2 :: SolveTestResult
runFunc2 = evalStatements func2

func3 :: SolveTestCase
func3 =
  let
    a = SoP.cons "a"
    b = SoP.cons "b"
    c = SoP.cons "c"
  in assert (SoPE (SoP.func "foo" [a, b, a |^| c]) a GeR)

runFunc3 :: SolveTestResult
runFunc3 = evalStatements func3

func4 :: SolveTestCase
func4 =
  let
    x = SoP.cons "x"
    g = SoP.func "g" [x]
    f = SoP.func "f" [x]
  in do
    declare (SoPE (SoP.int 1) g LeR)
    assert (SoPE f (f |*| g) LeR)

runFunc4 :: SolveTestResult
runFunc4 = evalStatements func4

unifyExp :: UnifyTestCase
unifyExp =
  let
    t = SoP.int 2
    x1 = SoP.cons "x1"
    x2 = SoP.cons "x2"
  in do
    unify (SoPE ((t |^| x1) |*| (t |^| (x1 |+| x1))) ((t |^| x2) |*| (t |^| (x2 |+| x2))) EqR)

runUnifyExp :: UnifyTestResult
runUnifyExp = evalStatements unifyExp

main :: IO ()
main = defaultMain tests

tests :: TestTree
tests = testGroup "lib-tests"
  [ testGroup "Equality tests"
    [ testGroup "True"
      [ testCase "m = n1 + 1 implies n + m = n + n1 + 1" $
        Just True @=? runEqualityGiven1
      , testCase "m = n1 + 1 implies n * m = n + n * n1" $
        Just True @=? runEqualityGiven2
      , testCase "m = n1 + 1 implies n^m = n*n^n1" $
        Just True @=? runEqualityGiven3
      , testCase "n + 1 = n1 + m + 1 and m = n1 and n1 = n2 + m1 + 1 implies 1 + n2 + m1 = n1" $
        Just True @=? runEqSubst
      , testCase "1 <= y and x + 1 = 2 * y implies 2 * y - 1 = x" $
        Just True @=? runEqSubst2
      , testCase "Combined: 1 <= m and 2 * n = m implies 2 * n - 1 = m - 2 and 1 <= m" $
        Just True @=? runMultistep
      , testCase "Multistep: m = n1 + 1 and m + n = n2 + 1 implies n1 + n = n2" $
        Just True @=? runMultistep2
      , testCase "1 + a = c and 1 + b = c implies a = b and 2 + 2 * a = 2 * c" $
        Just True @=? runStep3
      , testGroup "Functions"
        [ testCase "a + max(a + b, c) = max(b + a, c) + a" $
          Just True @=? runFunc1
        ]
      , testGroup "Natural numbers"
        [ testCase "m = n - 1 implies m + 1 = n" $
          Nothing @=? evalStatements (declare (SoPE (SoP.cons "m") (SoP.cons "n" |-| SoP.int 1) EqR) >>
                                      assert (SoPE (SoP.cons "m" |+| SoP.int 1) (SoP.cons "n") EqR)
                                      :: SolveTestCase)
        ]
      ]
    , testGroup "False"
      [ testCase "x + 2 /= x + 3" $
        Just False @=?
        evalStatements (assert
                        (SoPE (SoP.cons "x" |+| SoP.int 2) (SoP.cons "x" |+| SoP.int 3) EqR)
                        :: SolveTestCase)
      , testCase "8 /= x + x + x" $
        Just False @=?
        evalStatements (assert
                        (SoPE (SoP.int 3 |*| SoP.cons "x") (SoP.int 8) EqR)
                        :: SolveTestCase)
      , testCase "7 /= 2*y+4" $
        Just False @=?
        evalStatements (assert
                        (SoPE (SoP.int 2 |*| SoP.cons "y" |+| SoP.int 4) (SoP.int 7) EqR)
                        :: SolveTestCase)
      , testGroup "Functions"
        [ testCase "a + bar(a + b, c) /= bar(c, b + a) + a" $
          Just False @=? runFunc2
        ]
      ]
    ]
  , testGroup "Inequality tests"
    [ testGroup "True"
      [ testCase "Transitivity: i <= j and j <= k implies i <= k" $
        Just True @=? runTransitivity
      , testCase "Antisymmetry with zero: x is Natural and x <= 0 implies x = 0" $
        Just True @=? runAntisymmetryZero
      , testCase "Antisymmetry with non-zero: x <= 5 and x >= 5 implies x = 5" $
        Just True @=? runAntisymmetryNonZero
      , testCase "Strongly greater: j <= n and 1 <= n - j imples 1 + j <= n" $
        Just True @=? runLemma2
      , testCase "Composite function: x^3-2x^2+4<=2^x+3x^2+3" $
        Just True @=? runTrueInEq
      , testCase "Overlapping ranges: 4 <= x implies 2 <= x" $
        Just True @=? runOverlapInEq
      , testGroup "Functions"
        [ testCase "g(x) >= 1 implies f(x) <= g(x) * f(x)" $
          Just True @=? runFunc4
        ]
      , testGroup "Trivial"
        [ testCase "a <= a + 1" $
          Just True @=?
          evalStatements (assert
                          (SoPE (SoP.cons "a") (SoP.cons "a" |+| SoP.int 1) LeR)
                          :: SolveTestCase)
        , testCase "1 <= 2^a" $
          Just True @=?
          evalStatements (assert
                          (SoPE (SoP.int 1) (SoP.int 2 |^| SoP.cons "a") LeR)
                          :: SolveTestCase)
        , testCase "2 <= 2^(n + m) implies 2 <= 2^(m + n)" $
          Just True @=? runImplication
        ]
      , testGroup "Implications"
        [ testCase "a = b - 1 implies b >= 1" $
          Nothing @=?
          evalStatements (declare
                          (SoPE (SoP.cons "a") (SoP.cons "b" |-| SoP.int 1) EqR)
                          >>
                          assert (SoPE (SoP.cons "b") (SoP.int 1) GeR)
                          :: SolveTestCase)
        ]
      ]
    , testGroup "False"
      [ testCase "Composite function x^3-2x^2+4<=2^x+x^2+3" $
        Just False @=? runFalseInEq
      , testCase "1 <= m and m <= rp implies 1 <= rp - m" $
        Just False @=? runFalseInEq2
      , testCase "4a <= 2a" $
        Just False @=?
        evalStatements (assert
                        (SoPE (SoP.int 4 |*| SoP.cons "a") (SoP.int 2 |*| SoP.cons "a") LeR)
                        :: SolveTestCase)
      , testCase "foo(a, b, a ^ c) >= a" $
        Just False @=? runFunc3
      ]
    ]
  , testGroup "Ranges"
    [ -- TODO: Add test cases for range narrowing consistency
    ]
  , testGroup "Unifiers"
    [ testCase "x = x always holds" $
      Just [] @=?
      evalStatements (unify (SoPE (SoP.cons "x") (SoP.cons "x") EqR) :: UnifyTestCase)
    , testCase "t = a + b does not produce unifiers" $
      Just [] @=?
      evalStatements (unify (SoPE (SoP.cons "t") (SoP.cons "a" |+| SoP.cons "b") EqR)
                     :: UnifyTestCase)
    , testCase "a + b = a + c if b = c" $
      Just [SoPE (SoP.cons "b") (SoP.cons "c") EqR] @=?
      evalStatements (unify (SoPE (SoP.cons "a" |+| SoP.cons "b")
                                  (SoP.cons "a" |+| SoP.cons "c")
                                  EqR)
                     :: UnifyTestCase)
    , testCase "n = n + d" $
      Just [] @=?
      evalStatements (unify (SoPE (SoP.cons "n")
                                  (SoP.cons "n" |+| SoP.cons "d")
                                  EqR)
                     :: UnifyTestCase)
    , testCase "c = n implies n = n + d never holds" $
      Just [] @=?
      evalStatements (declare (SoPE (SoP.cons "c") (SoP.cons "n") EqR) >>
                      unify (SoPE (SoP.cons "n" |+| SoP.cons "d")
                                  (SoP.cons "n")
                                  EqR)
                     :: UnifyTestCase)
    , testCase "9 = x + x + x if x = 3" $
      Just [SoPE (SoP.cons "x") (SoP.int 3) EqR] @=?
      evalStatements (unify
                       (SoPE (SoP.int 3 |*| SoP.cons "x") (SoP.int 9) EqR)
                       :: UnifyTestCase)
    , testCase "6 = 2 * y + 4 if x = 1" $
      Just [SoPE (SoP.cons "y") (SoP.int 1) EqR] @=?
      evalStatements (unify
                       (SoPE (SoP.int 2 |*| SoP.cons "y" |+| SoP.int 4) (SoP.int 6) EqR)
                       :: UnifyTestCase)
    , testCase "8 /= x + x + x never holds" $
      Just [] @=?
      evalStatements (unify
                       (SoPE (SoP.int 3 |*| SoP.cons "x") (SoP.int 8) EqR)
                       :: UnifyTestCase)
    , testCase "7 /= 2*y+4 never holds" $
      Just [] @=?
      evalStatements (unify
                      (SoPE (SoP.int 2 |*| SoP.cons "y" |+| SoP.int 4) (SoP.int 7) EqR)
                       :: UnifyTestCase)
    , testCase "a^b = a^c if b = c" $
      Just [SoPE (SoP.cons "b") (SoP.cons "c") EqR] @=?
      evalStatements (unify (SoPE (SoP.cons "a" |^| SoP.cons "b")
                                  (SoP.cons "a" |^| SoP.cons "c")
                                  EqR)
                     :: UnifyTestCase)
    , testCase "2^x1 * 2^(x1 + x1) = 2^x2 * 2^(x2 + x2) holds if x1 = x2" $
      Just [SoPE (SoP.cons "x1") (SoP.cons "x2") EqR] @=? runUnifyExp
    ]
  ]
