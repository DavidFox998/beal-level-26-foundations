import BealLevel26Foundations.Base.BealCounterexampleBase
import BealLevel26Foundations.Chain.Beal13CaseToFalse
import BealLevel26Foundations.Frey.FreyConductor_26
import Mathlib.Data.Nat.Prime.Defs

namespace BealLevel26Foundations.Beal.BealForall

open BealLevel26Foundations.Base.BealCounterexampleBase
open BealLevel26Foundations.Chain.Beal13CaseToFalse
open BealLevel26Foundations.Frey.FreyConductor26
  (Is13Case)

/-!
# v4.49.0 Beal forall sketch from the 13-case
# v4.50.0 why GcdGt1 stays uninhabited
# v4.51.0 gcd counterexample `rfl` + primitive vs not
# v4.52.0 primitive subtype: exists gcd=1 vs forall gcd>1 false

`Frey.FreyConductor26.Is13Case` is `13 ∣ A*B*C` on shared
bases.  Forall.`Is13Case` is `13 ∣ x*y*z` on a packed
witness.  This file does **not** import Forall (cycle).

`Is13Case_prime_dvd` is `13 ∣ A*B*C → 13 ∣ A ∨ 13 ∣ B ∨ 13 ∣ C`
(`Nat.Prime.dvd_mul`).  One factor 13 is not a common
factor: `⟨13, 2, 1⟩` has `Is13Case` and `gcd = 1`.
Bases are not primitive-by-definition.  The packed twin
`∀ w, Is13Case w → w.gcd > 1` stays uninhabited (`gcd = 1`
by `primitive`); a packed 13-case witness would be a Beal
equation, which this file does not construct.

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

theorem gcd3_eq_bases_gcd (w : BealCounterexampleBases) :
    gcd3 w.A w.B w.C = w.gcd :=
  rfl

theorem prime_thirteen : Nat.Prime 13 := by
  decide

/-- Prime 13 divides a product iff it divides one factor.
`Is13Case` is `13 ∣ A*B*C`; the second hypothesis is that
unfolding.  Not a common-factor statement. -/
theorem Is13Case_prime_dvd
    (w : BealCounterexampleBases)
    (hIs13 : Is13Case w)
    (hMul : 13 ∣ w.A * w.B * w.C) :
    13 ∣ w.A ∨ 13 ∣ w.B ∨ 13 ∣ w.C :=
  have _keep : Is13Case w := hIs13
  match (Nat.Prime.dvd_mul prime_thirteen).mp hMul with
  | Or.inl hAB =>
    match (Nat.Prime.dvd_mul prime_thirteen).mp hAB with
    | Or.inl hA => Or.inl hA
    | Or.inr hB => Or.inr (Or.inl hB)
  | Or.inr hC => Or.inr (Or.inr hC)

/-- Named bases `A = 13`, `B = 2`, `C = 1`.  Not a packed
witness and not primitive-by-definition. -/
def triple_13_2_1 : BealCounterexampleBases :=
  ⟨13, 2, 1⟩

/-- Displayed gcd of the named triple.  `rfl`, not a
primitivity field. -/
theorem gcd_13_2_1_eq_1 : triple_13_2_1.gcd = 1 :=
  rfl

/-- `13` divides the product.  Witness `⟨2, rfl⟩`. -/
theorem dvd_13_2_1 : 13 ∣ 13 * 2 * 1 :=
  ⟨2, rfl⟩

/-- Same `Is13Case` on the named triple. -/
theorem Is13Case_triple_13_2_1 : Is13Case triple_13_2_1 :=
  dvd_13_2_1

/-- Explicit counterexample.  `gcd` by `rfl`, product by
`dvd_13_2_1`.  One factor 13 is not a common factor. -/
def Is13Case_gcd_counterexample_rfl :
    ∃ w : BealCounterexampleBases, Is13Case w ∧ w.gcd = 1 :=
  ⟨triple_13_2_1, Is13Case_triple_13_2_1, gcd_13_2_1_eq_1⟩

/-- Legacy name of `Is13Case_gcd_counterexample_rfl`. -/
theorem Is13Case_gcd_counterexample :
    ∃ w : BealCounterexampleBases, Is13Case w ∧ w.gcd = 1 :=
  Is13Case_gcd_counterexample_rfl

/-- Bases may have `gcd = 1` or `gcd > 1`.  `Is13Case`
does not force either.  Not a packed `primitive` field. -/
theorem primitive_vs_not_primitive :
    (∃ w : BealCounterexampleBases, w.gcd = 1) ∧
      (∃ w : BealCounterexampleBases, 1 < w.gcd) :=
  ⟨⟨triple_13_2_1, gcd_13_2_1_eq_1⟩,
    ⟨⟨13, 13, 13⟩,
      show 1 < Nat.gcd 13 (Nat.gcd 13 13) from
        Nat.one_lt_succ_succ 11⟩⟩

/-- Named non-primitive 13-case.  `gcd = 13`, not a packed
`primitive` field. -/
def triple_13_13_13 : BealCounterexampleBases :=
  ⟨13, 13, 13⟩

/-- `Is13Case` does not imply `gcd = 1`.  `triple_13_13_13`
is a 13-case with `gcd = 13`. -/
theorem Is13Case_not_implies_gcd_eq_one :
    ¬ ∀ (w : BealCounterexampleBases), Is13Case w → w.gcd = 1 :=
  fun h =>
    have h13 : Is13Case triple_13_13_13 :=
      (Nat.dvd_mul_right 13 13).mul_right 13
    have hgcd : triple_13_13_13.gcd = 13 := rfl
    have hne : triple_13_13_13.gcd ≠ 1 :=
      hgcd.symm ▸ Nat.succ_succ_ne_one 11
    hne (h triple_13_13_13 h13)

/-- Uninhabited.  Bases are not primitive-by-definition:
`BealCounterexampleBases` does not require `gcd = 1`, so
`triple_13_2_1` is a valid base with `gcd = 1`.  That shows
`13 ∣ A*B*C` is not a common factor (one factor 13 ≠ common
factor), so `∀ w, Is13Case w → w.gcd > 1` is false.
Not Forall.`Is13CaseForcesGcdGt1Sketch`.  The packed twin
stays uninhabited (`gcd = 1` by packed `primitive`).
`IsPrimitive` is now a derived Prop (`w.gcd = 1`); the
primitive forall is separately false via
`forall_primitive_Is13Case_gcd_gt1_false`. -/
def Is13CaseForcesGcdGt1Sketch : Prop :=
  ∀ (w : BealCounterexampleBases),
    Is13Case w → w.gcd > 1

/-- The bases GcdGt1 forall is false.  Not `False.elim`.
Uses `Nat.lt_irrefl` on the `⟨13, 2, 1⟩` witness.
Does not inhabit the packed Forall twin. -/
theorem not_Is13CaseForcesGcdGt1Sketch :
    ¬ Is13CaseForcesGcdGt1Sketch :=
  fun h =>
    match Is13Case_gcd_counterexample with
    | ⟨w, h13, hgcd⟩ =>
      Nat.lt_irrefl (1 : Nat) (hgcd ▸ h w h13)

/-- `gcd = 1` on the named triple.  Same as `gcd_13_2_1_eq_1`. -/
def triple_13_2_1_primitive : IsPrimitive triple_13_2_1 :=
  gcd_13_2_1_eq_1

/-- Named primitive subtype witness. -/
def triple_13_2_1_is_primitive_counterexample :
    BealPrimitiveCounterexampleBases :=
  ⟨triple_13_2_1, triple_13_2_1_primitive⟩

/-- `13 ∣ 13*2*1`.  Same as `Is13Case_triple_13_2_1`. -/
theorem primitive_13_2_1_is_Is13Case : Is13Case triple_13_2_1 :=
  Is13Case_triple_13_2_1

/-- A primitive 13-case with `gcd = 1`.  One factor 13 is
not a common factor. -/
def exists_primitive_Is13Case_gcd_1 :
    ∃ w : BealPrimitiveCounterexampleBases,
      Is13Case w.val ∧ w.val.gcd = 1 :=
  ⟨triple_13_2_1_is_primitive_counterexample,
    primitive_13_2_1_is_Is13Case, gcd_13_2_1_eq_1⟩

/-- Uninhabited and false.  Primitive bases may still have
`Is13Case` with `gcd = 1`.  Distinct from inhabiting this
Prop: the inhabitant would be a term of a false forall. -/
def Is13CaseForcesGcdGt1SketchPrimitive : Prop :=
  ∀ (w : BealPrimitiveCounterexampleBases),
    Is13Case w.val → w.val.gcd > 1

/-- The primitive GcdGt1 forall is false.  Uses
`exists_primitive_Is13Case_gcd_1` and `Nat.lt_irrefl`.
Does not inhabit `Is13CaseForcesGcdGt1SketchPrimitive`. -/
theorem forall_primitive_Is13Case_gcd_gt1_false :
    ¬ (∀ (w : BealPrimitiveCounterexampleBases),
        Is13Case w.val → w.val.gcd > 1) :=
  fun h =>
    match exists_primitive_Is13Case_gcd_1 with
    | ⟨w, h13, hgcd⟩ =>
      Nat.lt_irrefl (1 : Nat) (hgcd ▸ h w h13)

theorem not_Is13CaseForcesGcdGt1SketchPrimitive :
    ¬ Is13CaseForcesGcdGt1SketchPrimitive :=
  forall_primitive_Is13Case_gcd_gt1_false

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
#check Is13Case_prime_dvd
#check triple_13_2_1
#check gcd_13_2_1_eq_1
#check dvd_13_2_1
#check Is13Case_gcd_counterexample_rfl
#check Is13Case_gcd_counterexample
#check primitive_vs_not_primitive
#check Is13Case_not_implies_gcd_eq_one
#check not_Is13CaseForcesGcdGt1Sketch
#check IsPrimitive
#check IsPrimitiveBases
#check BealPrimitiveCounterexampleBases
#check triple_13_2_1_primitive
#check triple_13_2_1_is_primitive_counterexample
#check primitive_13_2_1_is_Is13Case
#check exists_primitive_Is13Case_gcd_1
#check Is13CaseForcesGcdGt1SketchPrimitive
#check forall_primitive_Is13Case_gcd_gt1_false
#check not_Is13CaseForcesGcdGt1SketchPrimitive
#print axioms gcd_13_2_1_eq_1
#print axioms dvd_13_2_1
#print axioms Is13Case_gcd_counterexample_rfl
#print axioms primitive_vs_not_primitive
#print axioms prime_thirteen
#print axioms Is13Case_prime_dvd
#print axioms Is13Case_gcd_counterexample
#print axioms not_Is13CaseForcesGcdGt1Sketch
#print axioms triple_13_2_1_primitive
#print axioms exists_primitive_Is13Case_gcd_1
#print axioms forall_primitive_Is13Case_gcd_gt1_false
#print axioms not_Is13CaseForcesGcdGt1SketchPrimitive
#print axioms beal_forall_from_Is13Case_sketch_type_eq
#print axioms beal_forall_of_Is13Case_composition

end BealLevel26Foundations.Beal.BealForall
