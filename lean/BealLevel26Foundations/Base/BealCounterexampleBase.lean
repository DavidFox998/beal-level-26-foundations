namespace BealLevel26Foundations.Base.BealCounterexampleBase

/-!
# v4.39.0 shared bases (no equation)

`BealCounterexampleBases` is only `A B C`.  No exponents, no
equation, no primitivity.  Frey and Forall both import this
file so `Frey/FreyCurve13.lean` does not import Forall.

This is not a Beal counterexample and not a Frey curve.
-/

/-- Shared bases only.  Not `BealCounterexample` (no equation). -/
structure BealCounterexampleBases where
  A : Nat
  B : Nat
  C : Nat

#check BealCounterexampleBases

end BealLevel26Foundations.Base.BealCounterexampleBase
