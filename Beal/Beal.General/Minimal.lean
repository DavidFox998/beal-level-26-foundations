import Beal.«Beal.General».Frey
import Mathlib.NumberTheory.Padics.PadicIntegers
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

private theorem q2_val_nat (n : ℕ) (hn : n ≠ 0) :
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

/- TODO: Classifying high-valuation minimal models requires checking
integrality and minimality for each parity/congruence case over Q₂.
The necessary condition above does not supply a uniform coordinate
change or a Tate reduction type. -/

#print axioms freyZ2_delta_v2
#print axioms frey_low_minimal_Q2
#print axioms high_required_for_positive_scale

end Beal.General