import Beal.«Beal.General».Minimal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Preliminary invariant facts at 2. These are inputs to, not a replacement
for, the local minimal-model and Tate-algorithm computations required to
identify a Néron conductor. No conductor formula is asserted here.
-/

namespace Beal.General

/-- Symbols needed to state future Tate-algorithm results. This type is
only a vocabulary: no curve has been assigned a symbol by this definition. -/
inductive KodairaType where
  | I (n : ℕ)
  | II
  | III
  | IV
  | IStar (n : ℕ)
  | IVStar
  | IIIStar
  | IIStar
  deriving DecidableEq, Repr

/-- The unit-discriminant output a future correct Tate classifier must
prove. No classifier satisfying this requirement is supplied here. -/
def TateUnitCriterion
    (typeAtTwo : WeierstrassCurve ℤ_[2] → KodairaType) : Prop :=
  ∀ M, Padic.valuation (M.Δ : ℚ_[2]) = 0 → typeAtTwo M = KodairaType.I 0

/-- The corresponding good-reduction conductor rule. This is an
unsupplied requirement on a future actual local conductor exponent. -/
def ConductorUnitCriterion
    (f2 : WeierstrassCurve ℤ_[2] → ℕ) : Prop :=
  ∀ M, Padic.valuation (M.Δ : ℚ_[2]) = 0 → f2 M = 0

/-- Relative to a correct Tate classifier, a unit discriminant
precludes every positive-index multiplicative symbol. This does not
construct the classifier or assign any Kodaira symbol to a curve. -/
theorem I_positive_incompatible_with_unit
    (typeAtTwo : WeierstrassCurve ℤ_[2] → KodairaType)
    (hTate : TateUnitCriterion typeAtTwo)
    (M : WeierstrassCurve ℤ_[2])
    (hunit : Padic.valuation (M.Δ : ℚ_[2]) = 0)
    (n : ℕ) (hn : 0 < n) :
    typeAtTwo M ≠ KodairaType.I n := by
  have hzero := hTate M hunit
  intro hpositive
  rw [hzero] at hpositive
  cases hpositive
  omega

/-- A threshold scale-2 change has the good-reduction symbol *if*
the classifier's unit criterion has been proved. Its existence and
integrality are premises, not consequences of valuation four. -/
theorem threshold_type_I0_conditional (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 x y z p q r).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1)
    (hthreshold : padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) = 4)
    (typeAtTwo : WeierstrassCurve ℤ_[2] → KodairaType)
    (hTate : TateUnitCriterion typeAtTwo) :
    typeAtTwo M = KodairaType.I 0 := by
  exact hTate M
    ((high_parity_exactly_four x y z p q r hx hy M C hmodel hscale).mpr hthreshold)

/-- The local conductor exponent is zero *if* its genuine good-reduction
rule has been supplied. No general `f₂` is constructed by this theorem. -/
theorem threshold_f2_zero_conditional (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 x y z p q r).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1)
    (hthreshold : padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) = 4)
    (f2 : WeierstrassCurve ℤ_[2] → ℕ)
    (hgood : ConductorUnitCriterion f2) :
    f2 M = 0 := by
  exact hgood M
    ((high_parity_exactly_four x y z p q r hx hy M C hmodel hscale).mpr hthreshold)

private theorem odd_c4_factor (U V : ℕ) (h : Odd U ∨ Odd V) :
    Odd (U ^ 2 + U * V + V ^ 2) := by
  have hu : U % 2 = 0 ∨ U % 2 = 1 := by omega
  have hv : V % 2 = 0 ∨ V % 2 = 1 := by omega
  have hh : U % 2 = 1 ∨ V % 2 = 1 := by
    rcases h with h | h
    · exact Or.inl (Nat.odd_iff.mp h)
    · exact Or.inr (Nat.odd_iff.mp h)
  apply Nat.odd_iff.mpr
  rcases hu with hu | hu <;> rcases hv with hv | hv
  all_goals simp [Nat.add_mod, Nat.mul_mod, pow_two, hu, hv] at *

/-- Under primitive parity, the displayed integral model has
v₂(c₄)=4. It is not thereby known to be a minimal model. -/
theorem frey_c4_v2_of_parity (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (hparity : Odd (x ^ p) ∨ Odd (y ^ q)) :
    padicValInt 2 (freyWeierstrassGeneral x y z p q r).c₄ = 4 := by
  have hc4Nat :
      (freyWeierstrassGeneral x y z p q r).c₄ =
        ((16 * ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) : ℕ) : ℤ) := by
    rw [frey_c4]
    push_cast
    ring
  rw [hc4Nat]
  simp only [padicValInt, Int.natAbs_ofNat]
  have hS : (x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2 ≠ 0 := by positivity
  have h16 : padicValNat 2 16 = 4 := by
    change padicValNat 2 (2 ^ 4) = 4
    rw [padicValNat.pow 4 (by norm_num : (2 : ℕ) ≠ 0), padicValNat_self]
  have hSval :
      padicValNat 2 ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have hmod : ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd hd
    have hodd : ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) % 2 = 1 :=
      Nat.odd_iff.mp (odd_c4_factor (x ^ p) (y ^ q) hparity)
    rw [hodd] at hmod
    norm_num at hmod
  rw [padicValNat.mul (by norm_num : (16 : ℕ) ≠ 0) hS, h16, hSval]

/-- Coprime powered inputs cannot both be even. This still says
nothing about Kodaira type or the conductor exponent. -/
theorem frey_c4_v2_of_coprime (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (hcop : Nat.Coprime (x ^ p) (y ^ q)) :
    padicValInt 2 (freyWeierstrassGeneral x y z p q r).c₄ = 4 := by
  apply frey_c4_v2_of_parity x y z p q r hx hy
  rcases Nat.even_or_odd (x ^ p) with heU | hoU
  · rcases Nat.even_or_odd (y ^ q) with heV | hoV
    · exfalso
      rcases heU with ⟨u, hu⟩
      rcases heV with ⟨v, hv⟩
      have hdU : 2 ∣ x ^ p := ⟨u, by omega⟩
      have hdV : 2 ∣ y ^ q := ⟨v, by omega⟩
      have hgcd : 2 ∣ Nat.gcd (x ^ p) (y ^ q) := Nat.dvd_gcd hdU hdV
      have hcop' : Nat.gcd (x ^ p) (y ^ q) = 1 := hcop
      rw [hcop'] at hgcd
      norm_num at hgcd
    · exact Or.inr hoV
  · exact Or.inl hoU

/-- Coprimality of the original bases supplies the powered-input
c₄ hypothesis, provided both exponents are positive. -/
theorem frey_c4_v2_of_base_coprime (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (hp : 0 < p) (hq : 0 < q) (hcop : Nat.Coprime x y) :
    padicValInt 2 (freyWeierstrassGeneral x y z p q r).c₄ = 4 := by
  apply frey_c4_v2_of_coprime x y z p q r hx hy
  exact (Nat.coprime_pow_right_iff hq (x ^ p) y).mpr
    ((Nat.coprime_pow_left_iff hp x y).mpr hcop)

/-- The displayed model has singular reduction modulo 2;
this alone cannot determine a Néron conductor. -/
theorem frey_discriminant_even (x y z p q r : ℕ) :
    (2 : ℤ) ∣ (freyWeierstrassGeneral x y z p q r).Δ := by
  rw [frey_delta_raw]
  refine ⟨8 * ((x : ℤ) ^ p) ^ 2 * ((y : ℤ) ^ q) ^ 2 *
    ((x : ℤ) ^ p + (y : ℤ) ^ q) ^ 2, ?_⟩
  ring

/- TODO tate_classification_general: The three parity witnesses in Minimal have odd discriminant
*after* their particular scale-2 changes. They cannot be assigned
type I_{2*v₂(W)} by a correct classifier: its unit-discriminant rule
would force good reduction (I₀), not positive-index multiplicative Iₙ.
No actual Kodaira classifier, Tate algorithm, or local conductor
function and its good-reduction rule is constructed here. In other
high-congruence cases, minimal models and types remain unknown.
Prove the full Tate steps before an unconditional f₂, or any formula
N=2^?*rad(x*y*z), can be claimed. -/

#print axioms I_positive_incompatible_with_unit
#print axioms threshold_type_I0_conditional
#print axioms threshold_f2_zero_conditional
#print axioms frey_c4_v2_of_coprime
#print axioms frey_c4_v2_of_base_coprime
#print axioms frey_discriminant_even

end Beal.General