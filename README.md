# GHC.TypeLits.SMTSolver

A GHC type checker plugin that can solve _equalities_ and _inequalities_ using cvc5 SMT solver. No other solver is currently supported.

The plugin is capable of solving expressions of types of kind `Nat` containing addition, subtraction, multiplication, and partially exponentiation.

While solving the expressions with exponentiations like the following:
```
(2 <= x) => 2 ^ (x) * 2 ^ (x) = 2 * 2 ^ (2 * x - 1)
```
plugin can halt.

To use the plugin, add
```haskell
{-# OPTIONS_GHC -fplugin GHC.TypeLits.SMTSolver #-}
```
to the top of the file, or compile with `-fplugin GHC.TypeLits.SMTSolver` flag set.
