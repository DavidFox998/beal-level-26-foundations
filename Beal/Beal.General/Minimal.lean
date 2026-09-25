import Beal.«Beal.General».Frey
import Mathlib.NumberTheory.Padics.PadicIntegers
import Mathlib.NumberTheory.Padics.RingHoms
import Mathlib.AlgebraicGeometry.EllipticCurve.VariableChange
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
The low-valuation local minimality obstruction for the general Frey model.
The higher-valuation case is not classified here: the discriminant being
divisible by 2¹² is a necessary condition for a scale-2 change, not
sufficient evidence that such a change is integral or minimal.
-/

namespace Beal.General

private theorem q2_val_pow (x : ℚ_[2]) (hx : x ≠ 0) (n : ℕ) :
    Padic.valuation (x ^ n) = (n : ℤ) * Padic.valuation x := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, Padic.valuation_map_mul (pow_ne_zero n hx) hx, ih]
    push_cast
    ring

private theorem q2_val_inv (x : ℚ_[2]) (hx : x ≠ 0) :
    Padic.valuation x⁻¹ = -Padic.valuation x := by
  have h := Padic.valuation_map_mul (inv_ne_zero hx) hx
  rw [inv_mul_cancel₀ hx, Padic.valuation_one] at h
  omega

/-- A Z₂-integral model with discriminant valuation below 12 admits
no positive-scale Q₂ change to another Z₂-integral model. -/
theorem low_minimality_Q2
    (E : WeierstrassCurve ℤ_[2]) (hE : E.Δ ≠ 0)
    (hsmall : Padic.valuation (E.Δ : ℚ_[2]) < 12)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : (E.map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2])) :
    Padic.valuation (C.u : ℚ_[2]) ≤ 0 := by
  have he : (E.Δ : ℚ_[2]) ≠ 0 := (PadicInt.coe_ne_zero E.Δ).mpr hE
  have hu : (C.u : ℚ_[2]) ≠ 0 := Units.ne_zero C.u
  have hdelta := congrArg WeierstrassCurve.Δ hmodel
  simp only [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hdelta
  have hval := congrArg Padic.valuation hdelta
  rw [Padic.valuation_map_mul (pow_ne_zero 12 (inv_ne_zero hu)) he,
    q2_val_pow _ (inv_ne_zero hu) 12, q2_val_inv _ hu] at hval
  have hnonneg : 0 ≤ Padic.valuation (M.Δ : ℚ_[2]) :=
    PadicInt.valuation_nonneg M.Δ
  omega

private theorem q2_val_coe_rat {q : ℚ} (hq : q ≠ 0) :
    Padic.valuation (q : ℚ_[2]) = padicValRat 2 q := by
  have hx : (q : ℚ_[2]) ≠ 0 := Rat.cast_ne_zero.mpr hq
  have hp_pos : (0 : ℝ) < 2 := by norm_num
  have hp_ne : (2 : ℝ) ≠ 1 := by norm_num
  have hnorm : ‖(q : ℚ_[2])‖ = (padicNorm 2 q : ℝ) :=
    padicNormE.eq_padicNorm q
  have hpow : padicNorm 2 q = (2 : ℚ) ^ (-padicValRat 2 q) :=
    padicNorm.eq_zpow_of_nonzero hq
  have hcast :
      Rat.cast ((2 : ℚ) ^ (-padicValRat 2 q)) =
        (2 : ℝ) ^ (-padicValRat 2 q) :=
    map_zpow₀ (Rat.castHom ℝ) (2 : ℚ) (-padicValRat 2 q)
  have hL : (2 : ℝ) ^ (-Padic.valuation (q : ℚ_[2])) = ‖(q : ℚ_[2])‖ := by
    have := Padic.norm_eq_pow_val hx
    exact_mod_cast this.symm
  have hR : (2 : ℝ) ^ (-padicValRat 2 q) = ‖(q : ℚ_[2])‖ := by
    rw [hnorm, hpow]
    exact hcast.symm
  exact neg_injective ((zpow_inj hp_pos hp_ne).mp (hL.trans hR.symm))

/-- Valuation of a nonzero natural number embedded in Q₂. -/
theorem q2_val_nat (n : ℕ) (hn : n ≠ 0) :
    Padic.valuation (n : ℚ_[2]) = (padicValNat 2 n : ℤ) := by
  have hq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hcast : ((n : ℚ) : ℚ_[2]) = (n : ℚ_[2]) := by simp
  have hrat := q2_val_coe_rat hq
  rw [hcast] at hrat
  simpa [padicValRat.of_nat] using hrat

/-- Base change of the general integral Frey model to Z₂. -/
noncomputable def freyZ2 (x y z p q r : ℕ) : WeierstrassCurve ℤ_[2] :=
  (freyWeierstrassGeneral x y z p q r).map (Int.castRingHom ℤ_[2])

private theorem freyZ2_delta (x y z p q r : ℕ) :
    (freyZ2 x y z p q r).Δ =
      ((16 * (x ^ p) ^ 2 * (y ^ q) ^ 2 *
        (x ^ p + y ^ q) ^ 2 : ℕ) : ℤ_[2]) := by
  have hd :
      (freyWeierstrassGeneral x y z p q r).Δ =
        ((16 * (x ^ p) ^ 2 * (y ^ q) ^ 2 *
          (x ^ p + y ^ q) ^ 2 : ℕ) : ℤ) := by
    rw [frey_delta_raw]
    push_cast
    ring
  rw [freyZ2, WeierstrassCurve.map_Δ, hd]
  simp

theorem freyZ2_delta_v2 (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q) :
    Padic.valuation ((freyZ2 x y z p q r).Δ : ℚ_[2]) =
      4 + 2 * (padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) : ℤ) := by
  rw [freyZ2_delta]
  have hprod : x ^ p * y ^ q * (x ^ p + y ^ q) ≠ 0 := by positivity
  have hdisc : 16 * (x ^ p) ^ 2 * (y ^ q) ^ 2 *
      (x ^ p + y ^ q) ^ 2 ≠ 0 := by positivity
  have hfactor : 16 * (x ^ p) ^ 2 * (y ^ q) ^ 2 *
      (x ^ p + y ^ q) ^ 2 =
      16 * (x ^ p * y ^ q * (x ^ p + y ^ q)) ^ 2 := by ring
  rw [PadicInt.coe_natCast, q2_val_nat _ hdisc, hfactor,
    padicValNat.mul (by decide : (16 : ℕ) ≠ 0) (pow_ne_zero 2 hprod),
    padicValNat.pow 2 hprod]
  have h16 : padicValNat 2 16 = 4 := by
    change padicValNat 2 (2 ^ 4) = 4
    rw [padicValNat.pow 4 (by decide : (2 : ℕ) ≠ 0), padicValNat_self]
  rw [h16]
  norm_cast

/-- A proven low-valuation case for all powered inputs, with all Q₂
changes to Z₂-integral models quantified over. -/
theorem frey_low_minimal_Q2 (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (hsmall : padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) < 4)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 x y z p q r).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2])) :
    Padic.valuation (C.u : ℚ_[2]) ≤ 0 := by
  have hdisc : 16 * (x ^ p) ^ 2 * (y ^ q) ^ 2 *
      (x ^ p + y ^ q) ^ 2 ≠ 0 := by positivity
  have hdiscQ : ((freyZ2 x y z p q r).Δ : ℚ_[2]) ≠ 0 := by
    rw [freyZ2_delta, PadicInt.coe_natCast]
    exact Nat.cast_ne_zero.mpr hdisc
  have hE : (freyZ2 x y z p q r).Δ ≠ 0 :=
    (PadicInt.coe_ne_zero _).mp hdiscQ
  have hval : Padic.valuation ((freyZ2 x y z p q r).Δ : ℚ_[2]) < 12 := by
    rw [freyZ2_delta_v2 x y z p q r hx hy]
    omega
  exact low_minimality_Q2 (freyZ2 x y z p q r) hE hval M C hmodel

/-- Necessary, not sufficient: positive two-adic scale for this
displayed model can occur only at high discriminant valuation. -/
theorem high_required_for_positive_scale (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 x y z p q r).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2]))
    (hpositive : 0 < Padic.valuation (C.u : ℚ_[2])) :
    4 ≤ padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) := by
  by_contra hnot
  have hsmall : padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) < 4 := by omega
  have hnonpositive := frey_low_minimal_Q2 x y z p q r hx hy hsmall M C hmodel
  omega

/-- An integral scale-2 change can have odd discriminant only at
the exact threshold `v₂(UV(U+V))=4`, not at every valuation ≥4. -/
theorem unit_delta_after_scale_two_requires_threshold (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 x y z p q r).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1)
    (hunit : Padic.valuation (M.Δ : ℚ_[2]) = 0) :
    padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) = 4 := by
  have hdisc : 16 * (x ^ p) ^ 2 * (y ^ q) ^ 2 *
      (x ^ p + y ^ q) ^ 2 ≠ 0 := by positivity
  have hdiscQ : ((freyZ2 x y z p q r).Δ : ℚ_[2]) ≠ 0 := by
    rw [freyZ2_delta, PadicInt.coe_natCast]
    exact Nat.cast_ne_zero.mpr hdisc
  have hu : (C.u : ℚ_[2]) ≠ 0 := Units.ne_zero C.u
  have hdelta := congrArg WeierstrassCurve.Δ hmodel
  simp only [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hdelta
  have hval := congrArg Padic.valuation hdelta
  rw [Padic.valuation_map_mul (pow_ne_zero 12 (inv_ne_zero hu)) hdiscQ,
    q2_val_pow _ (inv_ne_zero hu) 12, q2_val_inv _ hu,
    freyZ2_delta_v2 x y z p q r hx hy] at hval
  omega

/-- The twelfth-power discriminant scaling, with no assumption that the
changed model has unit discriminant. Integrality is an explicit premise. -/
theorem unit_disc_iff_v2_eq_12 (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 x y z p q r).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1) :
    Padic.valuation (M.Δ : ℚ_[2]) = 0 ↔
      Padic.valuation ((freyZ2 x y z p q r).Δ : ℚ_[2]) = 12 := by
  have hdisc : 16 * (x ^ p) ^ 2 * (y ^ q) ^ 2 *
      (x ^ p + y ^ q) ^ 2 ≠ 0 := by positivity
  have hdiscQ : ((freyZ2 x y z p q r).Δ : ℚ_[2]) ≠ 0 := by
    rw [freyZ2_delta, PadicInt.coe_natCast]
    exact Nat.cast_ne_zero.mpr hdisc
  have hu : (C.u : ℚ_[2]) ≠ 0 := Units.ne_zero C.u
  have hdelta := congrArg WeierstrassCurve.Δ hmodel
  simp only [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hdelta
  have hval := congrArg Padic.valuation hdelta
  rw [Padic.valuation_map_mul (pow_ne_zero 12 (inv_ne_zero hu)) hdiscQ,
    q2_val_pow _ (inv_ne_zero hu) 12, q2_val_inv _ hu] at hval
  constructor <;> intro h <;> omega

/-- The displayed Frey model itself has discriminant valuation twelve
exactly at the four-valuation threshold. -/
theorem frey_disc_v2_twelve_iff_threshold (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q) :
    Padic.valuation ((freyZ2 x y z p q r).Δ : ℚ_[2]) = 12 ↔
      padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) = 4 := by
  rw [freyZ2_delta_v2 x y z p q r hx hy]
  constructor <;> intro h <;> omega

/-- For *any* positive powered inputs, among integral scale-2 changes,
unit discriminant is equivalent to valuation exactly four. This does
not assert existence of a scale-2 change in any parity class. -/
theorem high_parity_exactly_four (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 x y z p q r).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1) :
    Padic.valuation (M.Δ : ℚ_[2]) = 0 ↔
      padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) = 4 := by
  exact (unit_disc_iff_v2_eq_12 x y z p q r hx hy M C hmodel hscale).trans
    (frey_disc_v2_twelve_iff_threshold x y z p q r hx hy)

/-- The three mutually exclusive parity shapes of primitive inputs.
This is only parity bookkeeping, not a minimal-model classification. -/
theorem coprime_parity_cases (U V : ℕ) (hcop : Nat.Coprime U V) :
    (Odd U ∧ Odd V) ∨ (Even U ∧ Odd V) ∨ (Odd U ∧ Even V) := by
  rcases Nat.even_or_odd U with hu | hu
  · rcases Nat.even_or_odd V with hv | hv
    · exfalso
      rcases hu with ⟨u, hu⟩
      rcases hv with ⟨v, hv⟩
      have h2u : 2 ∣ U := ⟨u, by omega⟩
      have h2v : 2 ∣ V := ⟨v, by omega⟩
      have h2g : 2 ∣ Nat.gcd U V := Nat.dvd_gcd h2u h2v
      have hg : Nat.gcd U V = 1 := hcop
      rw [hg] at h2g
      norm_num at h2g
    · exact Or.inr (Or.inl ⟨hu, hv⟩)
  · rcases Nat.even_or_odd V with hv | hv
    · exact Or.inr (Or.inr ⟨hu, hv⟩)
    · exact Or.inl ⟨hu, hv⟩

/-- A change with scale two and the translation indicated by `r`. -/
private noncomputable def highChangeTwo (r : ℚ_[2]) :
    WeierstrassCurve.VariableChange ℚ_[2] where
  u := Units.mk0 (2 : ℚ_[2]) (by norm_num)
  r := r
  s := 1
  t := 0

/-- A candidate first change with fixed scale two but unrestricted
Q₂ translation and shear parameters. No integrality is asserted. -/
noncomputable def candidateScaleTwoChange (r s t : ℚ_[2]) :
    WeierstrassCurve.VariableChange ℚ_[2] where
  u := Units.mk0 (2 : ℚ_[2]) (by norm_num)
  r := r
  s := s
  t := t

/-- Every candidate in this search has positive scale valuation one. -/
theorem candidateScaleTwoChange_val (r s t : ℚ_[2]) :
    Padic.valuation ((candidateScaleTwoChange r s t).u : ℚ_[2]) = 1 := by
  change Padic.valuation (2 : ℚ_[2]) = 1
  simpa using (Padic.valuation_p (p := 2))

/-- The remaining first-change search at fixed scale `u=2`.
It permits other translations, shears, and target Z₂ models; its
existence is not inferred from a discriminant valuation. -/
def FirstScaleTwoSearch (U V : ℕ) : Prop :=
  ∃ (r s t : ℚ_[2]) (M : WeierstrassCurve ℤ_[2]),
    ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange
      (candidateScaleTwoChange r s t) =
        M.map (algebraMap ℤ_[2] ℚ_[2])

/-- Necessary coefficient equations for a general scale-2 candidate.
Unlike `TateScaleTwoStep`, the translation and shears are arbitrary
Q₂ elements, and no transformed coefficient is forced to be zero. -/
structure ScaleTwoCoefficientConditions (U V : ℕ) (r s t : ℚ_[2])
    (M : WeierstrassCurve ℤ_[2]) : Prop where
  a₁ : s = (M.a₁ : ℚ_[2])
  a₃ : t = 4 * (M.a₃ : ℚ_[2])
  a₂ : (2 : ℚ_[2])⁻¹ ^ 2 *
      ((V : ℚ_[2]) - (U : ℚ_[2]) + 3 * r - s ^ 2) = (M.a₂ : ℚ_[2])
  a₄ : (2 : ℚ_[2])⁻¹ ^ 4 *
      (-((U : ℚ_[2]) * (V : ℚ_[2])) + 2 * r * ((V : ℚ_[2]) - (U : ℚ_[2])) +
        3 * r ^ 2 - 2 * s * t) = (M.a₄ : ℚ_[2])
  a₆ : (2 : ℚ_[2])⁻¹ ^ 6 *
      (r * (-((U : ℚ_[2]) * (V : ℚ_[2]))) +
        r ^ 2 * ((V : ℚ_[2]) - (U : ℚ_[2])) + r ^ 3 - t ^ 2) =
      (M.a₆ : ℚ_[2])

/-- Any integral target in the unrestricted fixed-scale search must
satisfy all five explicit coefficient conditions. No converse or
existence in the opposite residue classes is asserted. -/
theorem first_scale_two_search_coefficient_conditions (U V : ℕ)
    (h : FirstScaleTwoSearch U V) :
    ∃ (r s t : ℚ_[2]) (M : WeierstrassCurve ℤ_[2]),
      ScaleTwoCoefficientConditions U V r s t M := by
  obtain ⟨r, s, t, M, hmodel⟩ := h
  refine ⟨r, s, t, M, ⟨?_, ?_, ?_, ?_, ?_⟩⟩
  · have h1 := congrArg WeierstrassCurve.a₁ hmodel
    simpa [freyZ2, freyWeierstrassGeneral, candidateScaleTwoChange,
      WeierstrassCurve.variableChange, WeierstrassCurve.map,
      PadicInt.algebraMap_apply] using h1
  · have h3 := congrArg WeierstrassCurve.a₃ hmodel
    simp [freyZ2, freyWeierstrassGeneral, candidateScaleTwoChange,
      WeierstrassCurve.variableChange, WeierstrassCurve.map,
      PadicInt.algebraMap_apply] at h3
    have hfactor : (4 : ℚ_[2]) * (2 ^ 3 : ℚ_[2])⁻¹ * 2 = 1 := by norm_num
    calc
      t = ((4 : ℚ_[2]) * (2 ^ 3 : ℚ_[2])⁻¹ * 2) * t := by rw [hfactor, one_mul]
      _ = 4 * ((2 ^ 3 : ℚ_[2])⁻¹ * (2 * t)) := by ring
      _ = 4 * (M.a₃ : ℚ_[2]) := by rw [h3]
  · have h2 := congrArg WeierstrassCurve.a₂ hmodel
    simpa [freyZ2, freyWeierstrassGeneral, candidateScaleTwoChange,
      WeierstrassCurve.variableChange, WeierstrassCurve.map,
      PadicInt.algebraMap_apply] using h2
  · have h4 := congrArg WeierstrassCurve.a₄ hmodel
    simpa [freyZ2, freyWeierstrassGeneral, candidateScaleTwoChange,
      WeierstrassCurve.variableChange, WeierstrassCurve.map,
      PadicInt.algebraMap_apply] using h4
  · have h6 := congrArg WeierstrassCurve.a₆ hmodel
    simpa [freyZ2, freyWeierstrassGeneral, candidateScaleTwoChange,
      WeierstrassCurve.variableChange, WeierstrassCurve.map,
      PadicInt.algebraMap_apply] using h6

/-- Three is a unit in the 2-adic integers. -/
private theorem unit_three_z2 : IsUnit (3 : ℤ_[2]) := by
  apply PadicInt.isUnit_iff.mpr
  apply le_antisymm (PadicInt.norm_le_one _)
  apply not_lt.mp
  change ¬ ‖((3 : ℤ) : ℤ_[2])‖ < 1
  rw [PadicInt.norm_intCast_eq_padic_norm, padicNormE.norm_int_lt_one_iff_dvd]
  norm_num

/-- The integral `a₁` and `a₂` of any target force the allegedly
unrestricted Q₂ translation to lie in Z₂: its coefficient is the unit
three. No restriction on the target's `a₆` is used. -/
theorem scale_two_conditions_integral_translation (U V : ℕ)
    (r s t : ℚ_[2]) (M : WeierstrassCurve ℤ_[2])
    (h : ScaleTwoCoefficientConditions U V r s t M) :
    ∃ R : ℤ_[2], r = (R : ℚ_[2]) := by
  obtain ⟨b, hb⟩ : (3 : ℤ_[2]) ∣ 1 := isUnit_iff_dvd_one.mp unit_three_z2
  let A : ℤ_[2] := 4 * M.a₂ - (V : ℤ_[2]) + (U : ℤ_[2]) + M.a₁ ^ 2
  have h2Q : (V : ℚ_[2]) - (U : ℚ_[2]) + 3 * r - s ^ 2 =
      4 * (M.a₂ : ℚ_[2]) := by
    have hraw := h.a₂
    have hf : (4 : ℚ_[2]) * (2 : ℚ_[2])⁻¹ ^ 2 = 1 := by norm_num
    calc
      _ = (4 * (2 : ℚ_[2])⁻¹ ^ 2) *
            ((V : ℚ_[2]) - (U : ℚ_[2]) + 3 * r - s ^ 2) := by rw [hf, one_mul]
      _ = 4 * ((2 : ℚ_[2])⁻¹ ^ 2 *
            ((V : ℚ_[2]) - (U : ℚ_[2]) + 3 * r - s ^ 2)) := by ring
      _ = 4 * (M.a₂ : ℚ_[2]) := by rw [hraw]
  have heq : (3 : ℚ_[2]) * r = (A : ℚ_[2]) := by
    change (3 : ℚ_[2]) * r = 4 * (M.a₂ : ℚ_[2]) - (V : ℚ_[2]) +
      (U : ℚ_[2]) + (M.a₁ : ℚ_[2]) ^ 2
    rw [h.a₁] at h2Q
    linear_combination h2Q
  have hunitQ : (3 : ℚ_[2]) * (b : ℚ_[2]) = 1 := by
    have hh := congrArg (fun z : ℤ_[2] => (z : ℚ_[2])) hb.symm
    simpa only [PadicInt.coe_mul, PadicInt.coe_natCast, map_one] using hh
  refine ⟨b * A, ?_⟩
  calc
    r = (b : ℚ_[2]) * ((3 : ℚ_[2]) * r) := by
      rw [← mul_assoc, mul_comm (b : ℚ_[2]) 3, hunitQ, one_mul]
    _ = (b : ℚ_[2]) * (A : ℚ_[2]) := by rw [heq]
    _ = ((b * A : ℤ_[2]) : ℚ_[2]) := rfl

/-- Clear the `a₂` and `a₆` denominators for any genuine Q₂
coefficient witness. The `t²` term is retained, and `a₆` need not
vanish. These are equalities in Z₂, not a finite-search heuristic. -/
theorem scale_two_conditions_integral_numerators (U V : ℕ)
    (r s t : ℚ_[2]) (M : WeierstrassCurve ℤ_[2])
    (h : ScaleTwoCoefficientConditions U V r s t M) :
    ∃ R : ℤ_[2], r = (R : ℚ_[2]) ∧
      ((V : ℤ_[2]) - (U : ℤ_[2]) + 3 * R - M.a₁ ^ 2 = 4 * M.a₂) ∧
      (R * (-((U : ℤ_[2]) * (V : ℤ_[2]))) +
        R ^ 2 * ((V : ℤ_[2]) - (U : ℤ_[2])) + R ^ 3 -
          (4 * M.a₃) ^ 2 = 64 * M.a₆) := by
  obtain ⟨R, hr⟩ := scale_two_conditions_integral_translation U V r s t M h
  have h2Q : (V : ℚ_[2]) - (U : ℚ_[2]) + 3 * r - s ^ 2 =
      4 * (M.a₂ : ℚ_[2]) := by
    have hraw := h.a₂
    have hf : (4 : ℚ_[2]) * (2 : ℚ_[2])⁻¹ ^ 2 = 1 := by norm_num
    calc
      _ = (4 * (2 : ℚ_[2])⁻¹ ^ 2) *
            ((V : ℚ_[2]) - (U : ℚ_[2]) + 3 * r - s ^ 2) := by rw [hf, one_mul]
      _ = 4 * ((2 : ℚ_[2])⁻¹ ^ 2 *
            ((V : ℚ_[2]) - (U : ℚ_[2]) + 3 * r - s ^ 2)) := by ring
      _ = 4 * (M.a₂ : ℚ_[2]) := by rw [hraw]
  have h6Q : r * (-((U : ℚ_[2]) * (V : ℚ_[2]))) +
      r ^ 2 * ((V : ℚ_[2]) - (U : ℚ_[2])) + r ^ 3 - t ^ 2 =
      64 * (M.a₆ : ℚ_[2]) := by
    have hraw := h.a₆
    have hf : (64 : ℚ_[2]) * (2 : ℚ_[2])⁻¹ ^ 6 = 1 := by norm_num
    calc
      _ = (64 * (2 : ℚ_[2])⁻¹ ^ 6) *
            (r * (-((U : ℚ_[2]) * (V : ℚ_[2]))) +
              r ^ 2 * ((V : ℚ_[2]) - (U : ℚ_[2])) + r ^ 3 - t ^ 2) := by
                rw [hf, one_mul]
      _ = 64 * ((2 : ℚ_[2])⁻¹ ^ 6 *
            (r * (-((U : ℚ_[2]) * (V : ℚ_[2]))) +
              r ^ 2 * ((V : ℚ_[2]) - (U : ℚ_[2])) + r ^ 3 - t ^ 2)) := by ring
      _ = 64 * (M.a₆ : ℚ_[2]) := by rw [hraw]
  refine ⟨R, hr, ?_, ?_⟩
  · apply Subtype.coe_injective
    change (V : ℚ_[2]) - (U : ℚ_[2]) + 3 * (R : ℚ_[2]) -
      (M.a₁ : ℚ_[2]) ^ 2 = 4 * (M.a₂ : ℚ_[2])
    simpa only [hr, h.a₁] using h2Q
  · apply Subtype.coe_injective
    change (R : ℚ_[2]) * (-((U : ℚ_[2]) * (V : ℚ_[2]))) +
      (R : ℚ_[2]) ^ 2 * ((V : ℚ_[2]) - (U : ℚ_[2])) +
      (R : ℚ_[2]) ^ 3 - (4 * (M.a₃ : ℚ_[2])) ^ 2 = 64 * (M.a₆ : ℚ_[2])
    simpa only [hr, h.a₃] using h6Q

private def highIntegral (a2 a4 : ℤ) : WeierstrassCurve ℤ where
  a₁ := 1
  a₂ := a2
  a₃ := 0
  a₄ := a4
  a₆ := 0

private noncomputable def highZ2 (a2 a4 : ℤ) : WeierstrassCurve ℤ_[2] :=
  (highIntegral a2 a4).map (Int.castRingHom ℤ_[2])

/-- One concrete first Tate-algorithm integrality test for the Frey
family: scale `u=2`, shear `s=1`, `t=0`, and an integral translation
`r`. The equalities are exactly the divisibility tests for the new
`a₂`, `a₄`, and `a₆=0`. This is neither a Kodaira classifier nor an
assertion that every high-valuation pair passes this test. -/
structure TateScaleTwoStep (U V : ℕ) where
  r : ℤ
  a₂ : ℤ
  a₄ : ℤ
  a₂_condition : 4 * a₂ = (V : ℤ) - (U : ℤ) + 3 * r - 1
  a₄_condition :
    16 * a₄ = -(U : ℤ) * (V : ℤ) +
      2 * r * ((V : ℤ) - (U : ℤ)) + 3 * r ^ 2
  a₆_condition :
    r * (-((U : ℤ) * (V : ℤ))) +
      r ^ 2 * ((V : ℤ) - (U : ℤ)) + r ^ 3 = 0

/-- A successful coefficient test really gives a Z₂-integral
scale-2 model of the curve with powered inputs `U,V`. -/
theorem tate_scale_two_step_model (U V : ℕ) (step : TateScaleTwoStep U V) :
    ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange
      (highChangeTwo (step.r : ℚ_[2])) =
        (highZ2 step.a₂ step.a₄).map (algebraMap ℤ_[2] ℚ_[2]) := by
  have haQ : (4 : ℚ_[2]) * (step.a₂ : ℚ_[2]) =
      (V : ℚ_[2]) - (U : ℚ_[2]) + 3 * step.r - 1 := by
    exact_mod_cast step.a₂_condition
  have hbQ : (16 : ℚ_[2]) * (step.a₄ : ℚ_[2]) =
      -((U : ℚ_[2]) * (V : ℚ_[2])) +
        2 * step.r * ((V : ℚ_[2]) - (U : ℚ_[2])) + 3 * step.r ^ 2 := by
    have h := congrArg (fun t : ℤ => (t : ℚ_[2])) step.a₄_condition
    simpa only [Int.cast_mul, Int.cast_neg, Int.cast_add, Int.cast_sub,
      Int.cast_pow, Int.cast_natCast, Int.cast_ofNat, Nat.cast_mul, neg_mul] using h
  have hcQ : (step.r : ℚ_[2]) * (-((U : ℚ_[2]) * (V : ℚ_[2]))) +
      step.r ^ 2 * ((V : ℚ_[2]) - (U : ℚ_[2])) + step.r ^ 3 = 0 := by
    have h := congrArg (fun t : ℤ => (t : ℚ_[2])) step.a₆_condition
    simpa only [Int.cast_mul, Int.cast_neg, Int.cast_add, Int.cast_sub,
      Int.cast_pow, Int.cast_natCast, Int.cast_ofNat, Nat.cast_mul, neg_mul] using h
  ext <;> simp only [freyZ2, freyWeierstrassGeneral, highChangeTwo, highZ2, highIntegral,
    WeierstrassCurve.variableChange, WeierstrassCurve.map,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val, Units.val_mk0,
    map_zero, map_one, pow_one, mul_zero, zero_mul, add_zero, zero_add,
    sub_zero, one_mul, mul_one, map_sub, map_neg, map_mul, map_natCast,
    map_intCast, PadicInt.coe_sub, PadicInt.coe_neg, PadicInt.coe_mul,
    PadicInt.coe_natCast, PadicInt.coe_intCast, one_pow, zero_pow (by norm_num : (2:ℕ) ≠ 0)]
  case a₁ => norm_num
  case a₂ =>
    rw [← haQ]
    calc
      (2 : ℚ_[2])⁻¹ ^ 2 * (4 * (step.a₂ : ℚ_[2])) =
          (4 : ℚ_[2])⁻¹ * (4 * step.a₂) := by
        rw [inv_pow]
        norm_num
      _ = step.a₂ := by
        rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (4 : ℚ_[2]) ≠ 0), one_mul]
  case a₄ =>
    rw [← hbQ]
    calc
      (2 : ℚ_[2])⁻¹ ^ 4 * (16 * (step.a₄ : ℚ_[2])) =
          (16 : ℚ_[2])⁻¹ * (16 * step.a₄) := by
        rw [inv_pow]
        norm_num
      _ = step.a₄ := by
        rw [← mul_assoc, inv_mul_cancel₀ (by norm_num : (16 : ℚ_[2]) ≠ 0), one_mul]
  case a₆ =>
    rw [show (step.r : ℚ_[2]) * (-((U : ℚ_[2]) * (V : ℚ_[2]))) +
      step.r ^ 2 * ((V : ℚ_[2]) - (U : ℚ_[2])) + step.r ^ 3 = 0 from hcQ]
    ring

/-- Every proved restricted first step supplies a witness to the
broader scale-2 search. The converse is not claimed. -/
theorem tate_step_in_first_scale_two_search (U V : ℕ)
    (step : TateScaleTwoStep U V) : FirstScaleTwoSearch U V :=
  ⟨(step.r : ℚ_[2]), 1, 0, highZ2 step.a₂ step.a₄,
    tate_scale_two_step_model U V step⟩

/-- An even/odd subfamily passes the actual scale-2 coefficient test:
the even input is divisible by 16 and the odd one is 1 modulo 4. -/
theorem tate_step_even_odd (U V : ℕ) (hU : 16 ∣ U) (hV : V % 4 = 1) :
    Nonempty (TateScaleTwoStep U V) := by
  obtain ⟨v, hv⟩ : ∃ v : ℕ, V = 4 * v + 1 := ⟨V / 4, by omega⟩
  rcases hU with ⟨u, rfl⟩
  rw [hv]
  refine ⟨{
    r := 0
    a₂ := (v : ℤ) - 4 * (u : ℤ)
    a₄ := -((u : ℤ) * (4 * (v : ℤ) + 1))
    a₂_condition := ?_
    a₄_condition := ?_
    a₆_condition := ?_
  }⟩
  · push_cast
    ring
  · push_cast
    ring
  · ring

/-- An odd/even subfamily passes the same coefficient test when
the odd input is 3 modulo 4 and the even input is divisible by 16. -/
theorem tate_step_odd_even (U V : ℕ) (hU : U % 4 = 3) (hV : 16 ∣ V) :
    Nonempty (TateScaleTwoStep U V) := by
  obtain ⟨u, hu⟩ : ∃ u : ℕ, U = 4 * u + 3 := ⟨U / 4, by omega⟩
  rcases hV with ⟨v, rfl⟩
  rw [hu]
  refine ⟨{
    r := 0
    a₂ := 4 * (v : ℤ) - (u : ℤ) - 1
    a₄ := -((4 * (u : ℤ) + 3) * (v : ℤ))
    a₂_condition := ?_
    a₄_condition := ?_
    a₆_condition := ?_
  }⟩
  · push_cast
    ring
  · push_cast
    ring
  · ring

/-- An odd/odd subfamily passes the coefficient test when their sum
is divisible by 16 and `U` is 1 modulo 4. Translation by `U`
rather than zero is essential for this particular test. -/
theorem tate_step_odd_odd (U V : ℕ)
    (hU : U % 4 = 1) (hW : 16 ∣ U + V) :
    Nonempty (TateScaleTwoStep U V) := by
  obtain ⟨u, hu⟩ : ∃ u : ℕ, U = 4 * u + 1 := ⟨U / 4, by omega⟩
  obtain ⟨w, hw⟩ := hW
  have hUZ : (U : ℤ) = 4 * (u : ℤ) + 1 := by exact_mod_cast hu
  have hWZ : (U : ℤ) + (V : ℤ) = 16 * (w : ℤ) := by exact_mod_cast hw
  refine ⟨{
    r := (U : ℤ)
    a₂ := 4 * (w : ℤ) + (u : ℤ)
    a₄ := (U : ℤ) * (w : ℤ)
    a₂_condition := ?_
    a₄_condition := ?_
    a₆_condition := ?_
  }⟩
  · omega
  · calc
      16 * ((U : ℤ) * (w : ℤ)) = (U : ℤ) * (16 * (w : ℤ)) := by ring
      _ = (U : ℤ) * ((U : ℤ) + (V : ℤ)) := by rw [← hWZ]
      _ = -(U : ℤ) * (V : ℤ) + 2 * (U : ℤ) *
            ((V : ℤ) - (U : ℤ)) + 3 * (U : ℤ) ^ 2 := by ring
  · ring

/-- With `16 ∣ U` and `V ≡ 3 (mod 4)`, the `r=0, s=1, t=0`
first step fails its `a₂` divisibility test. Other changes have
not been excluded. -/
theorem tate_step_even_odd_r0_obstructed (U V : ℕ)
    (hU : 16 ∣ U) (hV : V % 4 = 3) :
    ¬ ∃ step : TateScaleTwoStep U V, step.r = 0 := by
  rintro ⟨step, hr⟩
  obtain ⟨u, hu⟩ := hU
  have ha := step.a₂_condition
  rw [hr] at ha
  omega

/-- With `16 ∣ V` and `U ≡ 1 (mod 4)`, the same `r=0`
first step cannot be integral. This is not an all-change obstruction. -/
theorem tate_step_odd_even_r0_obstructed (U V : ℕ)
    (hU : U % 4 = 1) (hV : 16 ∣ V) :
    ¬ ∃ step : TateScaleTwoStep U V, step.r = 0 := by
  rintro ⟨step, hr⟩
  obtain ⟨v, hv⟩ := hV
  have ha := step.a₂_condition
  rw [hr] at ha
  omega

/-- With `16 ∣ U+V` and `U ≡ 3 (mod 4)`, translation by `r=U`
fails the `a₂` test. A different first-step choice remains open. -/
theorem tate_step_odd_odd_rU_obstructed (U V : ℕ)
    (hU : U % 4 = 3) (hW : 16 ∣ U + V) :
    ¬ ∃ step : TateScaleTwoStep U V, step.r = (U : ℤ) := by
  rintro ⟨step, hr⟩
  obtain ⟨w, hw⟩ := hW
  have ha := step.a₂_condition
  rw [hr] at ha
  omega

/-- Because this restricted first step has `a₆=0`, its integral
translation can only be a root of `r(r-U)(r+V)`. This does not
restrict the general Q₂ search with nonzero transformed `a₆`. -/
theorem tate_step_translation_roots (U V : ℕ) (step : TateScaleTwoStep U V) :
    step.r = 0 ∨ step.r = (U : ℤ) ∨ step.r = -(V : ℤ) := by
  have hpoly : step.r * (step.r - (U : ℤ)) * (step.r + (V : ℤ)) = 0 := by
    calc
      _ = step.r * (-((U : ℤ) * (V : ℤ))) +
          step.r ^ 2 * ((V : ℤ) - (U : ℤ)) + step.r ^ 3 := by ring
      _ = 0 := step.a₆_condition
  rcases mul_eq_zero.mp hpoly with hleft | hright
  · rcases mul_eq_zero.mp hleft with h0 | hU
    · exact Or.inl h0
    · exact Or.inr (Or.inl (sub_eq_zero.mp hU))
  · exact Or.inr (Or.inr (by omega))

/-- Three opposite residue cases not covered by the restricted
constructors. This is not a complete partition of all inputs. -/
def RemainingResidueClass (U V : ℕ) : Prop :=
  (16 ∣ U ∧ V % 4 = 3) ∨
  (U % 4 = 1 ∧ 16 ∣ V) ∨
  (U % 4 = 3 ∧ 16 ∣ U + V)

/-- In the opposite residue classes, *none* of the three possible
integer translations passes this particular `s=1,t=0,a₆=0`
coefficient test. The broader `FirstScaleTwoSearch` remains open. -/
theorem remaining_residue_classes_open (U V : ℕ)
    (h : RemainingResidueClass U V) :
    ¬ Nonempty (TateScaleTwoStep U V) := by
  rintro ⟨step⟩
  rcases tate_step_translation_roots U V step with hr | hr | hr
  · rcases h with ⟨hU, hV⟩ | ⟨hU, hV⟩ | ⟨hU, hV⟩
    · exact tate_step_even_odd_r0_obstructed U V hU hV ⟨step, hr⟩
    · exact tate_step_odd_even_r0_obstructed U V hU hV ⟨step, hr⟩
    · obtain ⟨w, hw⟩ := hV
      have ha := step.a₂_condition
      rw [hr] at ha
      omega
  · rcases h with ⟨hU, hV⟩ | ⟨hU, hV⟩ | ⟨hU, hV⟩
    · obtain ⟨u, hu⟩ := hU
      have ha := step.a₂_condition
      rw [hr] at ha
      omega
    · obtain ⟨v, hv⟩ := hV
      have ha := step.a₂_condition
      rw [hr] at ha
      omega
    · exact tate_step_odd_odd_rU_obstructed U V hU hV ⟨step, hr⟩
  · rcases h with ⟨hU, hV⟩ | ⟨hU, hV⟩ | ⟨hU, hV⟩
    · obtain ⟨u, hu⟩ := hU
      have ha := step.a₂_condition
      rw [hr] at ha
      omega
    · obtain ⟨v, hv⟩ := hV
      have ha := step.a₂_condition
      rw [hr] at ha
      omega
    · obtain ⟨w, hw⟩ := hV
      have ha := step.a₂_condition
      rw [hr] at ha
      omega

/-- For these residue cases the old restricted constructor is
impossible. Any solution of the broader Q₂ search must instead
satisfy the unrestricted coefficient equations above. This theorem
does *not* decide whether such a solution exists. -/
theorem existence_search_open (U V : ℕ)
    (hcase : RemainingResidueClass U V) :
    ¬ Nonempty (TateScaleTwoStep U V) ∧
      (FirstScaleTwoSearch U V →
        ∃ (r s t : ℚ_[2]) (M : WeierstrassCurve ℤ_[2]),
          ScaleTwoCoefficientConditions U V r s t M) :=
  ⟨remaining_residue_classes_open U V hcase,
    first_scale_two_search_coefficient_conditions U V⟩

/-- The finite mod-four calculation used below. In each opposite
residue pattern, the `a₂` and `a₆` tests together exclude even shear.
This calculation is over `ZMod 4`, not a claim about arbitrary Q₂
parameters. -/
private theorem mod4_remaining_residues :
    ∀ (u v r s : ZMod 4),
      ((u = 0 ∧ v = 3) ∨ (u = 1 ∧ v = 0) ∨ (u = 3 ∧ u + v = 0)) →
      (v - u + 3 * r - s ^ 2 = 0) →
      (r * (-(u * v)) + r ^ 2 * (v - u) + r ^ 3 = 0) →
      (s = 1 ∨ s = 3) := by decide

/-- A mod-four obstruction for *integral* candidate parameters:
the shear must be odd in every opposite residue pattern. Both the
`a₂` and `a₆` integrality equations are needed. The separate
integrality bridge above permits applying it to the Q₂ search. -/
theorem mod4_remaining (U V : ℕ) (hcase : RemainingResidueClass U V)
    (r s t a₂ a₆ : ℤ_[2])
    (h2 : (V : ℤ_[2]) - (U : ℤ_[2]) + 3 * r - s ^ 2 = 4 * a₂)
    (h6 : r * (-((U : ℤ_[2]) * (V : ℤ_[2]))) +
      r ^ 2 * ((V : ℤ_[2]) - (U : ℤ_[2])) + r ^ 3 - (4 * t) ^ 2 = 64 * a₆) :
    PadicInt.toZModPow 2 s = 1 ∨ PadicInt.toZModPow 2 s = 3 := by
  let f : ℤ_[2] →+* ZMod 4 := PadicInt.toZModPow 2
  have hc : ((U : ZMod 4) = 0 ∧ (V : ZMod 4) = 3) ∨
      ((U : ZMod 4) = 1 ∧ (V : ZMod 4) = 0) ∨
      ((U : ZMod 4) = 3 ∧ (U : ZMod 4) + (V : ZMod 4) = 0) := by
    rcases hcase with ⟨hU, hV⟩ | ⟨hU, hV⟩ | ⟨hU, hW⟩
    · left
      constructor
      · exact (ZMod.natCast_zmod_eq_zero_iff_dvd U 4).2
          (dvd_trans (by norm_num : 4 ∣ 16) hU)
      · calc
          (V : ZMod 4) = ((V % 4 : ℕ) : ZMod 4) := by simp
          _ = 3 := by rw [hV]; norm_num
    · right; left
      constructor
      · calc
          (U : ZMod 4) = ((U % 4 : ℕ) : ZMod 4) := by simp
          _ = 1 := by rw [hU]; norm_num
      · exact (ZMod.natCast_zmod_eq_zero_iff_dvd V 4).2
          (dvd_trans (by norm_num : 4 ∣ 16) hV)
    · right; right
      constructor
      · calc
          (U : ZMod 4) = ((U % 4 : ℕ) : ZMod 4) := by simp
          _ = 3 := by rw [hU]; norm_num
      · have hw : ((U + V : ℕ) : ZMod 4) = 0 :=
          (ZMod.natCast_zmod_eq_zero_iff_dvd (U + V) 4).2
            (dvd_trans (by norm_num : 4 ∣ 16) hW)
        simpa using hw
  have hh2 : (V : ZMod 4) - (U : ZMod 4) + 3 * f r - (f s) ^ 2 = 0 := by
    have h := congrArg f h2
    simpa only [map_add, map_sub, map_mul, map_pow, map_natCast, map_ofNat,
      show (4 : ZMod 4) = 0 by decide, zero_mul] using h
  have hh6 : f r * (-((U : ZMod 4) * (V : ZMod 4))) +
      (f r) ^ 2 * ((V : ZMod 4) - (U : ZMod 4)) + (f r) ^ 3 = 0 := by
    have h := congrArg f h6
    simpa only [map_add, map_sub, map_mul, map_pow, map_natCast, map_neg, map_ofNat,
      show (4 : ZMod 4) = 0 by decide, show (64 : ZMod 4) = 0 by decide,
      zero_mul, zero_pow (by norm_num : (2 : ℕ) ≠ 0), sub_zero] using h
  have hn := mod4_remaining_residues (f (U : ℤ_[2])) (f (V : ℤ_[2])) (f r) (f s)
  have hcastU : f (U : ℤ_[2]) = (U : ZMod 4) := by simp [f]
  have hcastV : f (V : ℤ_[2]) = (V : ZMod 4) := by simp [f]
  exact hn (by simpa only [hcastU, hcastV] using hc)
    (by simpa only [hcastU, hcastV] using hh2)
    (by simpa only [hcastU, hcastV] using hh6)

/-- Even with unrestricted Q₂ translation, shears and nonzero target
`a₆`, any scale-two integral target in an opposite residue class has
odd `a₁` modulo four. This rules out the even-shear subcase but not
the whole first-change search. -/
theorem mod4_remaining_search (U V : ℕ)
    (hcase : RemainingResidueClass U V) (hsearch : FirstScaleTwoSearch U V) :
    ∃ M : WeierstrassCurve ℤ_[2],
      PadicInt.toZModPow 2 M.a₁ = 1 ∨ PadicInt.toZModPow 2 M.a₁ = 3 := by
  obtain ⟨r, s, t, M, h⟩ :=
    first_scale_two_search_coefficient_conditions U V hsearch
  obtain ⟨R, _, h2, h6⟩ :=
    scale_two_conditions_integral_numerators U V r s t M h
  exact ⟨M, mod4_remaining U V hcase R M.a₁ M.a₃ M.a₂ M.a₆ h2 h6⟩

private theorem highChangeTwo_val (r : ℚ_[2]) :
    Padic.valuation ((highChangeTwo r).u : ℚ_[2]) = 1 := by
  change Padic.valuation (2 : ℚ_[2]) = 1
  simpa using (Padic.valuation_p (p := 2))

/-- A successful first Tate step supplies an actual integral
scale-2 model. It does not by itself classify the reduction type. -/
theorem tate_step_integral_model (U V : ℕ) (step : TateScaleTwoStep U V) :
    ∃ (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2]),
      ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
        M.map (algebraMap ℤ_[2] ℚ_[2]) ∧
      Padic.valuation (C.u : ℚ_[2]) = 1 :=
  ⟨highZ2 step.a₂ step.a₄, highChangeTwo (step.r : ℚ_[2]),
    tate_scale_two_step_model U V step, highChangeTwo_val _⟩

/-- Exact discriminant valuation after a successful scale-2 step.
This is invariant arithmetic, not a Kodaira-type classification. -/
theorem tate_step_delta_valuation (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (step : TateScaleTwoStep U V) :
    Padic.valuation ((highZ2 step.a₂ step.a₄).Δ : ℚ_[2]) =
      2 * ((padicValNat 2 (U * V * (U + V)) : ℤ) - 4) := by
  have hdisc : 16 * U ^ 2 * V ^ 2 * (U + V) ^ 2 ≠ 0 := by positivity
  have hraw : ((freyZ2 U V 0 1 1 0).Δ : ℚ_[2]) ≠ 0 := by
    rw [freyZ2_delta, PadicInt.coe_natCast]
    exact Nat.cast_ne_zero.mpr (by simpa only [pow_one] using hdisc)
  have hu : ((highChangeTwo (step.r : ℚ_[2])).u : ℚ_[2]) ≠ 0 := Units.ne_zero _
  have hdelta := congrArg WeierstrassCurve.Δ (tate_scale_two_step_model U V step)
  simp only [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hdelta
  have hval := congrArg Padic.valuation hdelta
  rw [Padic.valuation_map_mul (pow_ne_zero 12 (inv_ne_zero hu)) hraw,
    q2_val_pow _ (inv_ne_zero hu) 12, q2_val_inv _ hu,
    highChangeTwo_val, freyZ2_delta_v2 U V 0 1 1 0
      (by simpa using hU) (by simpa using hV)] at hval
  simp only [pow_one] at hval
  omega

/-- In any of the congruence subfamilies above, the constructed
integral model has unit discriminant exactly at the valuation-four
threshold. No existence assertion is made for other residue classes. -/
theorem tate_step_unit_iff_threshold (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (step : TateScaleTwoStep U V) :
    ∃ (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2]),
      ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
        M.map (algebraMap ℤ_[2] ℚ_[2]) ∧
      Padic.valuation (C.u : ℚ_[2]) = 1 ∧
      (Padic.valuation (M.Δ : ℚ_[2]) = 0 ↔
        padicValNat 2 (U * V * (U + V)) = 4) := by
  obtain ⟨M, C, hmodel, hscale⟩ := tate_step_integral_model U V step
  refine ⟨M, C, hmodel, hscale, ?_⟩
  simpa using high_parity_exactly_four U V 0 1 1 0
    (by simpa using hU) (by simpa using hV) M C hmodel hscale

/-- At the exact threshold, any successful first step supplies a
model whose discriminant is a unit in Z₂. This is the algebraic
good-reduction certificate, not a completed Tate classifier. -/
theorem tate_step_threshold_unit (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (step : TateScaleTwoStep U V)
    (hthreshold : padicValNat 2 (U * V * (U + V)) = 4) :
    ∃ (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2]),
      ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
        M.map (algebraMap ℤ_[2] ℚ_[2]) ∧
      Padic.valuation (C.u : ℚ_[2]) = 1 ∧ IsUnit M.Δ := by
  obtain ⟨M, C, hmodel, hscale, hiff⟩ :=
    tate_step_unit_iff_threshold U V hU hV step
  have hunitVal : Padic.valuation (M.Δ : ℚ_[2]) = 0 := hiff.mpr hthreshold
  have hdisc : 16 * U ^ 2 * V ^ 2 * (U + V) ^ 2 ≠ 0 := by positivity
  have hraw : ((freyZ2 U V 0 1 1 0).Δ : ℚ_[2]) ≠ 0 := by
    rw [freyZ2_delta, PadicInt.coe_natCast]
    exact Nat.cast_ne_zero.mpr (by simpa only [pow_one] using hdisc)
  have hu : (C.u : ℚ_[2]) ≠ 0 := Units.ne_zero C.u
  have hdelta := congrArg WeierstrassCurve.Δ hmodel
  simp only [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hdelta
  have hM : (M.Δ : ℚ_[2]) ≠ 0 := by
    rw [← hdelta]
    exact mul_ne_zero (pow_ne_zero 12 (inv_ne_zero hu)) hraw
  refine ⟨M, C, hmodel, hscale, ?_⟩
  rw [PadicInt.isUnit_iff, PadicInt.norm_def, Padic.norm_eq_pow_val hM, hunitVal]
  norm_num

/-- In the three congruence subfamilies, a successful step at the
exact threshold also gives a Q₂-minimal integral model: a further
positive-scale change would make its unit discriminant nonintegral. -/
theorem tate_step_threshold_minimal (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (step : TateScaleTwoStep U V)
    (hthreshold : padicValNat 2 (U * V * (U + V)) = 4) :
    ∃ (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2]),
      ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
        M.map (algebraMap ℤ_[2] ℚ_[2]) ∧
      Padic.valuation (C.u : ℚ_[2]) = 1 ∧ IsUnit M.Δ ∧
      ∀ (N : WeierstrassCurve ℤ_[2]) (D : WeierstrassCurve.VariableChange ℚ_[2]),
        (M.map (algebraMap ℤ_[2] ℚ_[2])).variableChange D =
          N.map (algebraMap ℤ_[2] ℚ_[2]) →
        Padic.valuation (D.u : ℚ_[2]) ≤ 0 := by
  obtain ⟨M, C, hmodel, hscale, hunit⟩ :=
    tate_step_threshold_unit U V hU hV step hthreshold
  have hval : Padic.valuation (M.Δ : ℚ_[2]) = 0 :=
    (high_parity_exactly_four U V 0 1 1 0
      (by simpa using hU) (by simpa using hV) M C hmodel hscale).mpr
      (by simpa using hthreshold)
  refine ⟨M, C, hmodel, hscale, hunit, ?_⟩
  intro N D hnext
  apply low_minimality_Q2 M hunit.ne_zero ?_ N D hnext
  rw [hval]
  norm_num

/-- When valuation exceeds four, the integral first-step model, if
constructed, cannot have unit discriminant. Its further reduction
type still requires Tate-algorithm work. -/
theorem tate_step_above_threshold_nonunit (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (step : TateScaleTwoStep U V)
    (hhigh : 4 < padicValNat 2 (U * V * (U + V))) :
    ∃ (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2]),
      ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
        M.map (algebraMap ℤ_[2] ℚ_[2]) ∧
      Padic.valuation (C.u : ℚ_[2]) = 1 ∧
      Padic.valuation (M.Δ : ℚ_[2]) ≠ 0 := by
  obtain ⟨M, C, hmodel, hscale, hiff⟩ :=
    tate_step_unit_iff_threshold U V hU hV step
  refine ⟨M, C, hmodel, hscale, ?_⟩
  intro hunit
  have hthreshold := hiff.mp hunit
  omega

/-- An integral model with nonzero `c₄` of valuation zero cannot be
scaled positively to another integral model: `c₄` scales by `u⁻⁴`.
Unlike the discriminant obstruction, this applies at *every*
positive discriminant valuation. -/
theorem c4_unit_prevents_positive_scale
    (M : WeierstrassCurve ℤ_[2])
    (hc4 : (M.c₄ : ℚ_[2]) ≠ 0)
    (hc4val : Padic.valuation (M.c₄ : ℚ_[2]) = 0)
    (N : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : (M.map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      N.map (algebraMap ℤ_[2] ℚ_[2])) :
    Padic.valuation (C.u : ℚ_[2]) ≤ 0 := by
  have hu : (C.u : ℚ_[2]) ≠ 0 := Units.ne_zero C.u
  have hc := congrArg WeierstrassCurve.c₄ hmodel
  simp only [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.map_c₄,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hc
  have hval := congrArg Padic.valuation hc
  rw [Padic.valuation_map_mul (pow_ne_zero 4 (inv_ne_zero hu)) hc4,
    q2_val_pow _ (inv_ne_zero hu) 4, q2_val_inv _ hu, hc4val] at hval
  have hnonneg : 0 ≤ Padic.valuation (N.c₄ : ℚ_[2]) :=
    PadicInt.valuation_nonneg N.c₄
  omega

/-- Any hypothetical *integral* scale-2 change would lower the
valuation of `c₄` by four. When the starting valuation is zero,
this contradicts integrality of the target. -/
theorem scale_two_c4_valuation_if_integral
    (M N : WeierstrassCurve ℤ_[2])
    (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hc4 : (M.c₄ : ℚ_[2]) ≠ 0)
    (hmodel : (M.map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      N.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1) :
    Padic.valuation (N.c₄ : ℚ_[2]) =
      Padic.valuation (M.c₄ : ℚ_[2]) - 4 := by
  have hu : (C.u : ℚ_[2]) ≠ 0 := Units.ne_zero C.u
  have hc := congrArg WeierstrassCurve.c₄ hmodel
  simp only [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.map_c₄,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hc
  have hval := congrArg Padic.valuation hc
  rw [Padic.valuation_map_mul (pow_ne_zero 4 (inv_ne_zero hu)) hc4,
    q2_val_pow _ (inv_ne_zero hu) 4, q2_val_inv _ hu, hscale] at hval
  omega

/-- A *hypothetical* second scale-2 change would lower the
discriminant valuation by twelve. This is only a scaling law:
no second integral model is constructed here. -/
theorem second_scale_two_delta_if_integral
    (M N : WeierstrassCurve ℤ_[2])
    (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hM : (M.Δ : ℚ_[2]) ≠ 0)
    (hmodel : (M.map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      N.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1) :
    Padic.valuation (N.Δ : ℚ_[2]) =
      Padic.valuation (M.Δ : ℚ_[2]) - 12 := by
  have hu : (C.u : ℚ_[2]) ≠ 0 := Units.ne_zero C.u
  have hd := congrArg WeierstrassCurve.Δ hmodel
  simp only [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hd
  have hval := congrArg Padic.valuation hd
  rw [Padic.valuation_map_mul (pow_ne_zero 12 (inv_ne_zero hu)) hM,
    q2_val_pow _ (inv_ne_zero hu) 12, q2_val_inv _ hu, hscale] at hval
  omega

/-- Exact valuation *if* an additional scale-2 change of the constructed
first-step model is integral. This does not assert that such a change
exists; it is impossible in the coprime subfamilies (see Conductor). -/
theorem tate_step_second_delta_if_integral (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (step : TateScaleTwoStep U V)
    (N : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((highZ2 step.a₂ step.a₄).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      N.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1) :
    Padic.valuation (N.Δ : ℚ_[2]) =
      2 * ((padicValNat 2 (U * V * (U + V)) : ℤ) - 4) - 12 := by
  have hdisc : 16 * U ^ 2 * V ^ 2 * (U + V) ^ 2 ≠ 0 := by positivity
  have hraw : ((freyZ2 U V 0 1 1 0).Δ : ℚ_[2]) ≠ 0 := by
    rw [freyZ2_delta, PadicInt.coe_natCast]
    exact Nat.cast_ne_zero.mpr (by simpa only [pow_one] using hdisc)
  have hu : ((highChangeTwo (step.r : ℚ_[2])).u : ℚ_[2]) ≠ 0 := Units.ne_zero _
  have hd := congrArg WeierstrassCurve.Δ (tate_scale_two_step_model U V step)
  simp only [WeierstrassCurve.variableChange_Δ, WeierstrassCurve.map_Δ,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hd
  have hM : ((highZ2 step.a₂ step.a₄).Δ : ℚ_[2]) ≠ 0 := by
    rw [← hd]
    exact mul_ne_zero (pow_ne_zero 12 (inv_ne_zero hu)) hraw
  rw [second_scale_two_delta_if_integral _ N C hM hmodel hscale,
    tate_step_delta_valuation U V hU hV step]

/-- The next positive-scale change is an explicit proposition, not
a placeholder value or an automatically available Tate step. -/
def SecondScaleTwoAttempt (M : WeierstrassCurve ℤ_[2]) : Prop :=
  ∃ (N : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2]),
    (M.map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      N.map (algebraMap ℤ_[2] ℚ_[2]) ∧
    Padic.valuation (C.u : ℚ_[2]) = 1

/-- A unit `c₄` rules out the second scale-2 attempt altogether. -/
theorem no_second_scale_two_of_unit_c4
    (M : WeierstrassCurve ℤ_[2])
    (hc4 : (M.c₄ : ℚ_[2]) ≠ 0)
    (hc4val : Padic.valuation (M.c₄ : ℚ_[2]) = 0) :
    ¬ SecondScaleTwoAttempt M := by
  rintro ⟨N, C, hmodel, hscale⟩
  have hbound := c4_unit_prevents_positive_scale M hc4 hc4val N C hmodel
  omega

private theorem cast14 : ((14 : ℤ_[2]) : ℚ_[2]) = 14 := rfl
private theorem cast4 : ((4 : ℤ_[2]) : ℚ_[2]) = 4 := rfl
private theorem cast15 : ((15 : ℤ_[2]) : ℚ_[2]) = 15 := rfl
private theorem cast16 : ((16 : ℤ_[2]) : ℚ_[2]) = 16 := rfl
private theorem cast48 : ((48 : ℤ_[2]) : ℚ_[2]) = 48 := rfl
private theorem cast13 : ((13 : ℤ_[2]) : ℚ_[2]) = 13 := rfl
private theorem cast3 : ((3 : ℤ_[2]) : ℚ_[2]) = 3 := rfl

private theorem threshold_changes :
    ((freyZ2 1 15 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange
      (highChangeTwo 1) = (highZ2 4 1).map (algebraMap ℤ_[2] ℚ_[2]) ∧
    ((freyZ2 16 1 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange
      (highChangeTwo 0) = (highZ2 (-4) (-1)).map (algebraMap ℤ_[2] ℚ_[2]) ∧
    ((freyZ2 3 16 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange
      (highChangeTwo 0) = (highZ2 3 (-3)).map (algebraMap ℤ_[2] ℚ_[2]) := by
  constructor
  · ext <;> norm_num [freyZ2, freyWeierstrassGeneral, highChangeTwo,
      highZ2, highIntegral, WeierstrassCurve.variableChange,
      WeierstrassCurve.map, PadicInt.algebraMap_apply] <;>
      norm_num [cast14, cast4, cast15, cast16, cast48, cast13, cast3]
  constructor
  · ext <;> norm_num [freyZ2, freyWeierstrassGeneral, highChangeTwo,
      highZ2, highIntegral, WeierstrassCurve.variableChange,
      WeierstrassCurve.map, PadicInt.algebraMap_apply] <;>
      norm_num [cast14, cast4, cast15, cast16, cast48, cast13, cast3]
  · ext <;> norm_num [freyZ2, freyWeierstrassGeneral, highChangeTwo,
      highZ2, highIntegral, WeierstrassCurve.variableChange,
      WeierstrassCurve.map, PadicInt.algebraMap_apply] <;>
      norm_num [cast14, cast4, cast15, cast16, cast48, cast13, cast3]

private theorem threshold_deltas :
    (highZ2 4 1).Δ = (225 : ℤ_[2]) ∧
    (highZ2 (-4) (-1)).Δ = (289 : ℤ_[2]) ∧
    (highZ2 3 (-3)).Δ = (3249 : ℤ_[2]) := by
  norm_num [highZ2, highIntegral, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, WeierstrassCurve.map]

private theorem odd_delta_low (n : ℕ) (hn : Odd n) :
    Padic.valuation (n : ℚ_[2]) < 12 := by
  have hn0 : n ≠ 0 := by
    have ho := Nat.odd_iff.mp hn
    omega
  rw [q2_val_nat n hn0]
  have hv : padicValNat 2 n = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have ho : n % 2 = 1 := Nat.odd_iff.mp hn
    omega
  simp [hv]

/-- Computation of the factor 16 against any odd positive factor. -/
private theorem v2_sixteen_times_odd (n : ℕ) (hn : Odd n) :
    padicValNat 2 (16 * n) = 4 := by
  have hn0 : n ≠ 0 := by
    have ho := Nat.odd_iff.mp hn
    omega
  have hv : padicValNat 2 n = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have ho : n % 2 = 1 := Nat.odd_iff.mp hn
    omega
  have h16 : padicValNat 2 16 = 4 := by
    change padicValNat 2 (2 ^ 4) = 4
    rw [padicValNat.pow 4 (by decide : (2 : ℕ) ≠ 0), padicValNat_self]
  rw [padicValNat.mul (by decide : (16 : ℕ) ≠ 0) hn0, h16, hv]

/-- Three individual witnesses lie at the exact threshold. Their
parity patterns alone do not imply this for other inputs. -/
theorem threshold_witnesses_exactly_four :
    padicValNat 2 (1 * 15 * (1 + 15)) = 4 ∧
    padicValNat 2 (16 * 1 * (16 + 1)) = 4 ∧
    padicValNat 2 (3 * 16 * (3 + 16)) = 4 := by
  constructor
  · change padicValNat 2 (16 * 15) = 4
    exact v2_sixteen_times_odd 15 (by decide)
  constructor
  · change padicValNat 2 (16 * 17) = 4
    exact v2_sixteen_times_odd 17 (by decide)
  · change padicValNat 2 (16 * 57) = 4
    exact v2_sixteen_times_odd 57 (by decide)

/-- Each witness's *raw* discriminant has valuation twelve; the
separate integral changes above give 225, 289, and 3249 respectively. -/
theorem threshold_witnesses_raw_delta_v2 :
    Padic.valuation ((freyZ2 1 15 0 1 1 0).Δ : ℚ_[2]) = 12 ∧
    Padic.valuation ((freyZ2 16 1 0 1 1 0).Δ : ℚ_[2]) = 12 ∧
    Padic.valuation ((freyZ2 3 16 0 1 1 0).Δ : ℚ_[2]) = 12 := by
  constructor
  · exact (frey_disc_v2_twelve_iff_threshold 1 15 0 1 1 0
      (by norm_num) (by norm_num)).mpr threshold_witnesses_exactly_four.1
  constructor
  · exact (frey_disc_v2_twelve_iff_threshold 16 1 0 1 1 0
      (by norm_num) (by norm_num)).mpr threshold_witnesses_exactly_four.2.1
  · exact (frey_disc_v2_twelve_iff_threshold 3 16 0 1 1 0
      (by norm_num) (by norm_num)).mpr threshold_witnesses_exactly_four.2.2

private theorem threshold_low_1 :
    Padic.valuation ((highZ2 4 1).Δ : ℚ_[2]) < 12 := by
  rw [threshold_deltas.1]
  change Padic.valuation (225 : ℚ_[2]) < 12
  exact odd_delta_low 225 (by decide)

private theorem threshold_low_2 :
    Padic.valuation ((highZ2 (-4) (-1)).Δ : ℚ_[2]) < 12 := by
  rw [threshold_deltas.2.1]
  change Padic.valuation (289 : ℚ_[2]) < 12
  exact odd_delta_low 289 (by decide)

private theorem threshold_low_3 :
    Padic.valuation ((highZ2 3 (-3)).Δ : ℚ_[2]) < 12 := by
  rw [threshold_deltas.2.2]
  change Padic.valuation (3249 : ℚ_[2]) < 12
  exact odd_delta_low 3249 (by decide)

/-- Odd/odd threshold witness only: `(U,V)=(1,15)`.
This does not quantify over all odd/odd high-valuation inputs. -/
theorem high_minimal_odd_odd :
    ((freyZ2 1 15 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange
      (highChangeTwo 1) = (highZ2 4 1).map (algebraMap ℤ_[2] ℚ_[2]) ∧
    Padic.valuation ((highChangeTwo 1).u : ℚ_[2]) = 1 ∧
    (highZ2 4 1).Δ = (225 : ℤ_[2]) ∧
    ∀ (N : WeierstrassCurve ℤ_[2]) (D : WeierstrassCurve.VariableChange ℚ_[2]),
      ((highZ2 4 1).map (algebraMap ℤ_[2] ℚ_[2])).variableChange D =
        N.map (algebraMap ℤ_[2] ℚ_[2]) →
      Padic.valuation (D.u : ℚ_[2]) ≤ 0 := by
  refine ⟨threshold_changes.1, highChangeTwo_val 1, threshold_deltas.1, ?_⟩
  intro N D hmodel
  apply low_minimality_Q2 (highZ2 4 1) ?_ threshold_low_1 N D hmodel
  rw [threshold_deltas.1]
  norm_num

/-- Even/odd threshold witness only: `(U,V)=(16,1)`. -/
theorem high_minimal_even_odd :
    ((freyZ2 16 1 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange
      (highChangeTwo 0) = (highZ2 (-4) (-1)).map (algebraMap ℤ_[2] ℚ_[2]) ∧
    Padic.valuation ((highChangeTwo 0).u : ℚ_[2]) = 1 ∧
    (highZ2 (-4) (-1)).Δ = (289 : ℤ_[2]) ∧
    ∀ (N : WeierstrassCurve ℤ_[2]) (D : WeierstrassCurve.VariableChange ℚ_[2]),
      ((highZ2 (-4) (-1)).map (algebraMap ℤ_[2] ℚ_[2])).variableChange D =
        N.map (algebraMap ℤ_[2] ℚ_[2]) →
      Padic.valuation (D.u : ℚ_[2]) ≤ 0 := by
  refine ⟨threshold_changes.2.1, highChangeTwo_val 0, threshold_deltas.2.1, ?_⟩
  intro N D hmodel
  apply low_minimality_Q2 (highZ2 (-4) (-1)) ?_ threshold_low_2 N D hmodel
  rw [threshold_deltas.2.1]
  norm_num

/-- Odd/even threshold witness only: `(U,V)=(3,16)`. -/
theorem high_minimal_odd_even :
    ((freyZ2 3 16 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange
      (highChangeTwo 0) = (highZ2 3 (-3)).map (algebraMap ℤ_[2] ℚ_[2]) ∧
    Padic.valuation ((highChangeTwo 0).u : ℚ_[2]) = 1 ∧
    (highZ2 3 (-3)).Δ = (3249 : ℤ_[2]) ∧
    ∀ (N : WeierstrassCurve ℤ_[2]) (D : WeierstrassCurve.VariableChange ℚ_[2]),
      ((highZ2 3 (-3)).map (algebraMap ℤ_[2] ℚ_[2])).variableChange D =
        N.map (algebraMap ℤ_[2] ℚ_[2]) →
      Padic.valuation (D.u : ℚ_[2]) ≤ 0 := by
  refine ⟨threshold_changes.2.2, highChangeTwo_val 0, threshold_deltas.2.2, ?_⟩
  intro N D hmodel
  apply low_minimality_Q2 (highZ2 3 (-3)) ?_ threshold_low_3 N D hmodel
  rw [threshold_deltas.2.2]
  norm_num

/- TODO first_change_residue_classes / high_parity_general:
The opposite residue cases have no TateScaleTwoStep at all: its
a₆=0 forces r=0,U,-V, and all three fail the a₂ test there.
Determine FirstScaleTwoSearch using other coefficients, or rule
it out, and handle further congruence cases. Neither outcome
follows from the restricted obstruction alone.

TODO first_change_search: The unrestricted Q₂ candidate has integral
translation, and its target has odd a₁ in these opposite residue
classes. This eliminates even shear only; existence and impossibility
of FirstScaleTwoSearch with odd shear remain open.

TODO mod16_remaining: With odd shear, use `a₂` to restrict the
translation modulo 4, then test the full `a₆` numerator modulo 16.
Use the proved integrality bridge, not a finite check of rational
integer representatives, to transfer the obstruction to Q₂.

TODO mod64_remaining: Retain the `t²` contribution modulo 64,
and incorporate the `a₄` equation. Prove any remaining obstructions
over Z₂; the search is not settled by the restricted `a₆=0` form.

TODO later_non_scaling_Tate / second_step_alternative: Above valuation four a successful
first-step model has nonunit discriminant. For coprime inputs its
c₄ is a unit, forbidding another positive-scale integral change.
The subsequent non-scaling Tate tests and reduction type still
need proof; do not divide its discriminant by 2¹² again. -/

#print axioms freyZ2_delta_v2
#print axioms frey_low_minimal_Q2
#print axioms high_required_for_positive_scale
#print axioms unit_delta_after_scale_two_requires_threshold
#print axioms unit_disc_iff_v2_eq_12
#print axioms frey_disc_v2_twelve_iff_threshold
#print axioms high_parity_exactly_four
#print axioms tate_scale_two_step_model
#print axioms candidateScaleTwoChange_val
#print axioms first_scale_two_search_coefficient_conditions
#print axioms scale_two_conditions_integral_translation
#print axioms scale_two_conditions_integral_numerators
#print axioms tate_step_in_first_scale_two_search
#print axioms tate_step_even_odd
#print axioms tate_step_odd_even
#print axioms tate_step_odd_odd
#print axioms tate_step_even_odd_r0_obstructed
#print axioms tate_step_odd_even_r0_obstructed
#print axioms tate_step_odd_odd_rU_obstructed
#print axioms tate_step_translation_roots
#print axioms remaining_residue_classes_open
#print axioms existence_search_open
#print axioms mod4_remaining
#print axioms mod4_remaining_search
#print axioms tate_step_delta_valuation
#print axioms tate_step_threshold_unit
#print axioms tate_step_threshold_minimal
#print axioms tate_step_above_threshold_nonunit
#print axioms c4_unit_prevents_positive_scale
#print axioms scale_two_c4_valuation_if_integral
#print axioms second_scale_two_delta_if_integral
#print axioms tate_step_second_delta_if_integral
#print axioms no_second_scale_two_of_unit_c4
#print axioms threshold_witnesses_exactly_four
#print axioms threshold_witnesses_raw_delta_v2
#print axioms high_minimal_odd_odd
#print axioms high_minimal_even_odd
#print axioms high_minimal_odd_even

end Beal.General