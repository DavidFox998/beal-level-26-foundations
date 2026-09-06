import BealLevel26Foundations.Base.BealCounterexampleBase
import BealLevel26Foundations.Chain.Beal13CaseToFalse
import BealLevel26Foundations.Frey.FreyConductor_26

namespace BealLevel26Foundations.Beal.BealForall

open BealLevel26Foundations.Base.BealCounterexampleBase
open BealLevel26Foundations.Chain.Beal13CaseToFalse
open BealLevel26Foundations.Frey.FreyConductor26
  (Is13Case)

/-!
# v4.49.0 Beal forall sketch from the 13-case

`Frey.FreyConductor26.Is13Case` is `13 ∣ A*B*C` on shared
bases.  Forall.`Is13Case` is `13 ∣ x*y*z` on a packed
witness.  This file does **not** import Forall (cycle).

`Is13CaseForcesGcdGt1Sketch` here is
`13 ∣ A*B*C → gcd(A,B,C) > 1` on bases.  Uninhabited:
a single factor 13 on one base is not a common factor.
Forall keeps the packed twin
`∀ w, Is13Case w → w.gcd > 1` (uninhabited; packed
`gcd = 1` by `primitive`).

`beal_forall_from_Is13Case_sketch` is the Beal statement
`∀ A B C m n p, 2 < m,n,p → A^m+B^n=C^p → gcd > 1`.
Valid type.  Uninhabited.  Level 26 only treats the
13-case via Tate + Ribet + `S₂(Γ₀(2)) = 0`.  Other primes
need levels `2p`.  The two 13-case sketches do not imply
this forall: `Is13Case → False` on bases is not Beal
(13 may divide one base), and mixed exponents stay open.

No new axiom.  No `False.elim`.  Not `∀ A B C` in the
kernel.  `beal_forall_from_ribet` stays the typed
four-cusp close.
-/

/-- `gcd(A, gcd(B, C))`.  Not a packed-witness field. -/
def gcd3 (A B C : Nat) : Nat :=
  Nat.gcd A (Nat.gcd B C)

/-- Uninhabited.  `13 ∣ A*B*C` does not force a common
factor.  Not Forall.`Is13CaseForcesGcdGt1Sketch`. -/
def Is13CaseForcesGcdGt1Sketch : Prop :=
  ∀ (w : BealCounterexampleBases),
    Is13Case w → gcd3 w.A w.B w.C > 1

/-- Beal conjecture as a Prop.  Valid type
`∀ A B C m n p`.  Uninhabited: needs Tate + Ribet + a
true gcd step, and the same for every prime `p ≥ 5`. -/
def beal_forall_from_Is13Case_sketch : Prop :=
  ∀ (A B C m n p : Nat),
    2 < m → 2 < n → 2 < p →
    A ^ m + B ^ n = C ^ p →
    gcd3 A B C > 1

/-- Same valid type, named for `#check`.  Uninhabited. -/
def beal_forall_from_Is13Case_sketch_valid_type : Prop :=
  ∀ (A B C m n p : Nat),
    2 < m → 2 < n → 2 < p →
    A ^ m + B ^ n = C ^ p →
    gcd3 A B C > 1

theorem beal_forall_from_Is13Case_sketch_type_eq :
    beal_forall_from_Is13Case_sketch =
      beal_forall_from_Is13Case_sketch_valid_type :=
  rfl

/-- Uninhabited.  The 13-case False sketch plus the bases
gcd sketch do not yield Beal: other primes need `2p`,
and `13 ∣ A*B*C → False` is not the Beal statement. -/
def beal_forall_from_Is13Case_composition : Prop :=
  Is13CaseForcesFalseSketchViaLevel2 →
    Is13CaseForcesGcdGt1Sketch →
      beal_forall_from_Is13Case_sketch

/-- Tautology on the composition Prop.  Does not inhabit
`beal_forall_from_Is13Case_sketch`. -/
theorem beal_forall_of_Is13Case_composition
    (hComp : beal_forall_from_Is13Case_composition)
    (hFalse : Is13CaseForcesFalseSketchViaLevel2)
    (hGcd : Is13CaseForcesGcdGt1Sketch) :
    beal_forall_from_Is13Case_sketch :=
  hComp hFalse hGcd

#check Is13Case
#check Is13CaseForcesGcdGt1Sketch
#check Is13CaseForcesFalseSketchViaLevel2
#check beal_forall_from_Is13Case_sketch
#check beal_forall_from_Is13Case_sketch_valid_type
#check (∀ (A B C m n p : Nat),
  2 < m → 2 < n → 2 < p →
  A ^ m + B ^ n = C ^ p →
  gcd3 A B C > 1)
#check beal_forall_from_Is13Case_composition
#print axioms beal_forall_from_Is13Case_sketch_type_eq
#print axioms beal_forall_of_Is13Case_composition

end BealLevel26Foundations.Beal.BealForall
