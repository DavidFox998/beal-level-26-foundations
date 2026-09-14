/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Lake's LEAN_PATH puts the relocated kernel's `Beal/`
  prefix first, so `Beal.Matveev.*` cannot be imported from siblings.
  Do **not** import `Beal.Matveev.MatveevThm14General`.
-/
import Mathlib
import BealKraus
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

/-!
# Gaussian / Zsigmondy / Thue no-go (not a `B ≤ 10⁶` close)

Successor of `b6b426a` (`v24-v24x-final-Kraus-nogo`).
`A⁴ + B⁴ = N(A² + i B²)` in `ℤ[i]`, and on a gap-3 solution this
norm is `(B+3)¹³`. If unique factorization produced
`A² + i B² = ε (u+iv)¹³` with `u²+v² = B+3`, the argument form
would satisfy `|sin(13θ)| = B² / C^{13/2}`, equivalently after
squaring `B⁴ / C¹³`. A Matveev-style lower bound
`exp(−C1 log C log 13)` beats that upper bound only for
`C1 < 5 / log 13 < 2`. Every constant we actually have —
`C1_floor`, the jet `242`, even `C1 = 2` — is too large, so the
lower bound is strictly smaller than `B⁴ / C¹³` on `B ≥ B0`.

Zsigmondy primitive divisors and Mihăilescu / Catalan are not in
Mathlib 4.12. The Gaussian thirteenth-power factorization stays
`def Prop`. `baker_bound_gap3` stays uninhabited. Not v25.
`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

open Real
open GaussianInt

namespace BealMatveevBeal.BealKrausZsig

open BealMatveevBeal.BealKraus
open BealLevel26Foundations.BealGap3BakerUpperBound

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_kraus :
    C1_floor = BealMatveevBeal.BealKraus.C1_floor := rfl

theorem B0_nat_eq_kraus :
    B0_nat = BealMatveevBeal.BealKraus.B0_nat := rfl

/-! ## `log 13 > 5/2`, so `C1 ≥ 2` is already too large -/

theorem exp_half_le_seven_div_four :
    exp (1 / 2) ≤ (7 / 4 : ℝ) := by
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  have hx : |(1 / 2 : ℝ)| ≤ 1 := by
    rw [abs_of_pos hpos]
    norm_num
  have h := abs_exp_sub_one_sub_id_le hx
  have hle : exp (1 / 2) - 1 - 1 / 2 ≤ (1 / 2 : ℝ) ^ 2 :=
    (abs_le.mp h).2
  have : (1 / 2 : ℝ) + 1 ≤ exp (1 / 2) := add_one_le_exp (1 / 2)
  linarith

theorem exp_two_eq_exp_one_sq :
    exp 2 = exp 1 ^ 2 := by
  have h : (2 : ℝ) = (2 : ℕ) * (1 : ℝ) := by norm_num
  rw [h, Real.exp_nat_mul]

theorem exp_two_lt_exp_one_d9_sq :
    exp 2 < (2.7182818286 : ℝ) ^ 2 := by
  rw [exp_two_eq_exp_one_sq]
  exact pow_lt_pow_left Real.exp_one_lt_d9 (exp_pos _).le (by decide : (2 : ℕ) ≠ 0)

theorem exp_five_div_two_eq :
    exp (5 / 2) = exp 2 * exp (1 / 2) := by
  rw [← exp_add]
  norm_num

theorem exp_five_div_two_lt_thirteen :
    exp (5 / 2) < (13 : ℝ) := by
  have hmul : exp 2 * exp (1 / 2) <
      (2.7182818286 : ℝ) ^ 2 * (7 / 4 : ℝ) :=
    mul_lt_mul exp_two_lt_exp_one_d9_sq exp_half_le_seven_div_four
      (exp_pos _) (sq_nonneg _)
  have hnum : (2.7182818286 : ℝ) ^ 2 * (7 / 4 : ℝ) < 13 := by
    norm_num
  have h := lt_trans hmul hnum
  rwa [← exp_five_div_two_eq] at h

theorem log_thirteen_gt_five_div_two :
    (5 / 2 : ℝ) < log (13 : ℝ) := by
  have hpos : (0 : ℝ) < (13 : ℝ) := by norm_num
  exact (Real.lt_log_iff_exp_lt hpos).2 exp_five_div_two_lt_thirteen

/-- Cutoff for this comparison: need `C1 < 5 / log 13 < 2`. -/
theorem five_div_log_thirteen_lt_two :
    (5 : ℝ) / log (13 : ℝ) < 2 := by
  have hlog := log_thirteen_gt_five_div_two
  have hpos : (0 : ℝ) < log (13 : ℝ) := lt_trans (by norm_num) hlog
  have : (5 : ℝ) < 2 * log (13 : ℝ) := by linarith [hlog]
  exact (div_lt_iff hpos).2 (by linarith)

theorem C1_floor_gt_two : (2 : ℝ) < (C1_floor : ℝ) := by
  rw [C1_floor_eq]
  norm_num

theorem two_forty_two_gt_two : (2 : ℝ) < (242 : ℝ) := by
  norm_num

/-! ## Gaussian integers: `A⁴ + B⁴ = N(A² + i B²)` -/

/-- `A² + i B²` in `ℤ[i]`. -/
def gaussianAlpha (A B : ℕ) : GaussianInt :=
  ⟨(A : ℤ) ^ 2, (B : ℤ) ^ 2⟩

theorem gaussianAlpha_norm (A B : ℕ) :
    (gaussianAlpha A B).norm = (A : ℤ) ^ 4 + (B : ℤ) ^ 4 := by
  simp [gaussianAlpha, Zsqrtd.norm]
  ring

theorem gaussianAlpha_norm_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (gaussianAlpha A B).norm = ((B + 3 : ℕ) : ℤ) ^ 13 := by
  rw [gaussianAlpha_norm]
  exact_mod_cast hsol

theorem gaussianAlpha_mul_star (A B : ℕ) :
    gaussianAlpha A B * star (gaussianAlpha A B) =
      ((gaussianAlpha A B).norm : GaussianInt) :=
  (Zsqrtd.norm_eq_mul_conj (gaussianAlpha A B)).symm

/-- Imaginary part of `(u + i v)¹³`. -/
def imPow13 (u v : ℤ) : ℤ :=
  ((⟨u, v⟩ : GaussianInt) ^ 13).im

theorem imPow13_eq (u v : ℤ) :
    imPow13 u v = ((⟨u, v⟩ : GaussianInt) ^ 13).im :=
  rfl

/-- A common Gaussian divisor of `α` and `ᾱ` divides `2 A²`
    (real part) and `2 B²` (imaginary part). -/
theorem gaussianAlpha_add_star (A B : ℕ) :
    gaussianAlpha A B + star (gaussianAlpha A B) =
      ⟨2 * (A : ℤ) ^ 2, 0⟩ := by
  ext
  · simp [gaussianAlpha]; ring
  · simp [gaussianAlpha]

theorem gaussianAlpha_sub_star (A B : ℕ) :
    gaussianAlpha A B - star (gaussianAlpha A B) =
      ⟨0, 2 * (B : ℤ) ^ 2⟩ := by
  ext
  · simp [gaussianAlpha]
  · simp [gaussianAlpha]; ring

/-- A common Gaussian divisor of `α` and `ᾱ` divides `2 A²` and `2 B²`.
    This is not coprimeness in `ℤ[i]`; UFD factorization stays `def Prop`. -/
theorem gaussian_common_dvd {d : GaussianInt} {A B : ℕ}
    (hα : d ∣ gaussianAlpha A B)
    (hstar : d ∣ star (gaussianAlpha A B)) :
    d ∣ (⟨2 * (A : ℤ) ^ 2, 0⟩ : GaussianInt) ∧
      d ∣ (⟨0, 2 * (B : ℤ) ^ 2⟩ : GaussianInt) := by
  constructor
  · rw [← gaussianAlpha_add_star]
    exact dvd_add hα hstar
  · rw [← gaussianAlpha_sub_star]
    exact dvd_sub hα hstar

/-! ## Squared argument-form comparison `B⁴ / C¹³` -/

theorem B_add_three_le_two_mul_B {B : ℕ} (hB : 3 ≤ B) :
    ((B + 3 : ℕ) : ℝ) ≤ 2 * (B : ℝ) := by
  have : (3 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB
  have h : ((B + 3 : ℕ) : ℝ) = (B : ℝ) + 3 := by
    rw [Nat.cast_add, Nat.cast_ofNat]
  linarith

theorem eight_B_pow_three_lt_B_pow_four {B : ℕ} (hB : 8 < B) :
    (8 : ℝ) * (B : ℝ) ^ 3 < (B : ℝ) ^ 4 := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by
    exact_mod_cast (Nat.zero_lt_of_lt hB)
  have hpow : (0 : ℝ) < (B : ℝ) ^ 3 := pow_pos hBpos 3
  have : (8 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  calc
    (8 : ℝ) * (B : ℝ) ^ 3 < (B : ℝ) * (B : ℝ) ^ 3 :=
      (mul_lt_mul_right hpow).mpr this
    _ = (B : ℝ) ^ 4 := by ring

theorem C_pow_three_lt_B_pow_four {B : ℕ} (hB0 : B0_nat ≤ B) :
    ((B + 3 : ℕ) : ℝ) ^ 3 < (B : ℝ) ^ 4 := by
  have hB8 : 8 < B :=
    Nat.lt_of_lt_of_le (by decide : 8 < 1000000)
      (by simpa [B0_nat_eq] using hB0)
  have hB3 : 3 ≤ B :=
    Nat.le_trans (by decide : 3 ≤ 8) (Nat.le_of_lt hB8)
  have hC : ((B + 3 : ℕ) : ℝ) ≤ 2 * (B : ℝ) :=
    B_add_three_le_two_mul_B hB3
  have hCpos : (0 : ℝ) ≤ ((B + 3 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.zero_le _)
  have hle : ((B + 3 : ℕ) : ℝ) ^ 3 ≤ (2 * (B : ℝ)) ^ 3 :=
    pow_le_pow_left hCpos hC 3
  have hrw : (2 * (B : ℝ)) ^ 3 = 8 * (B : ℝ) ^ 3 := by ring
  have hlt := eight_B_pow_three_lt_B_pow_four hB8
  exact lt_of_le_of_lt (hle.trans_eq hrw) hlt

/-- For `C1 ≥ 2` the squared Matveev-style argument bound is
    strictly below `B⁴ / C¹³` on `B ≥ B0`. This is the comparison
    `|sin(13θ)| = B² / C^{13/2}` after squaring. -/
theorem baker_bound_gap3_gaussian_nogo
    {C1 : ℝ} (hC1 : 2 ≤ C1)
    {B : ℕ} (hB0 : B0_nat ≤ B) :
    exp (-C1 * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 := by
  set C : ℝ := ((B + 3 : ℕ) : ℝ)
  have hCgt1 : (1 : ℝ) < C := by
    have h4 : (4 : ℕ) ≤ B + 3 :=
      Nat.add_le_add_right
        (Nat.le_trans (by decide : 1 ≤ 1000000)
          (by simpa [B0_nat_eq] using hB0)) 3
    have : (1 : ℕ) < B + 3 :=
      Nat.lt_of_lt_of_le (by decide : (1 : ℕ) < 4) h4
    have : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) := by exact_mod_cast this
    simpa [C] using this
  have hCpos : (0 : ℝ) < C := lt_trans (by norm_num) hCgt1
  have hlogC : (0 : ℝ) < log C := Real.log_pos hCgt1
  have hlog13 := log_thirteen_gt_five_div_two
  have hC13pos : (0 : ℝ) < C ^ 13 := pow_pos hCpos 13
  have hexp2 : exp (-C1 * log C * log (13 : ℝ)) ^ 2 =
      exp ((2 : ℕ) * (-C1 * log C * log (13 : ℝ))) :=
    (Real.exp_nat_mul (-C1 * log C * log (13 : ℝ)) 2).symm
  have hprod :
      exp ((2 : ℕ) * (-C1 * log C * log (13 : ℝ))) * C ^ 13 =
        exp ((13 - 2 * C1 * log (13 : ℝ)) * log C) := by
    have hCpow : exp ((13 : ℕ) * log C) = C ^ 13 := by
      rw [Real.exp_nat_mul, Real.exp_log hCpos]
    have hCpow' : C ^ 13 = exp ((13 : ℕ) * log C) := hCpow.symm
    rw [hCpow', ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hexp : (13 : ℝ) - 2 * C1 * log (13 : ℝ) < 3 := by
    have : (10 : ℝ) < 2 * C1 * log (13 : ℝ) := by
      have h4 : (4 : ℝ) * log (13 : ℝ) ≤ 2 * C1 * log (13 : ℝ) := by
        have : (4 : ℝ) ≤ 2 * C1 := by linarith [hC1]
        exact mul_le_mul_of_nonneg_right this
          (le_of_lt (lt_trans (by norm_num) hlog13))
      have h10 : (10 : ℝ) < 4 * log (13 : ℝ) := by
        linarith [hlog13]
      exact lt_of_lt_of_le h10 h4
    linarith
  have hlt3 :
      exp ((13 - 2 * C1 * log (13 : ℝ)) * log C) < C ^ 3 := by
    have h3 : exp ((3 : ℕ) * log C) = C ^ 3 := by
      rw [Real.exp_nat_mul, Real.exp_log hCpos]
    have h3' : C ^ 3 = exp ((3 : ℕ) * log C) := h3.symm
    have hmul : ((13 : ℝ) - 2 * C1 * log (13 : ℝ)) * log C <
        (3 : ℕ) * log C := by
      have : ((13 : ℝ) - 2 * C1 * log (13 : ℝ)) * log C <
          (3 : ℝ) * log C :=
        (mul_lt_mul_right hlogC).mpr hexp
      simpa using this
    have := Real.exp_lt_exp.mpr hmul
    rwa [h3']
  have hB4 := C_pow_three_lt_B_pow_four hB0
  have hchain :
      exp (-C1 * log C * log (13 : ℝ)) ^ 2 * C ^ 13 < (B : ℝ) ^ 4 := by
    have h1 : exp (-C1 * log C * log (13 : ℝ)) ^ 2 * C ^ 13 =
        exp ((13 - 2 * C1 * log (13 : ℝ)) * log C) := by
      rw [hexp2, hprod]
    have h2 := lt_trans hlt3 hB4
    rwa [h1]
  have hdiv : exp (-C1 * log C * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / C ^ 13 :=
    (lt_div_iff hC13pos).2 (by simpa [mul_comm] using hchain)
  simpa [C] using hdiv

theorem C1_floor_gaussian_nogo {B : ℕ} (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 :=
  baker_bound_gap3_gaussian_nogo (le_of_lt C1_floor_gt_two) hB0

theorem two_forty_two_gaussian_nogo {B : ℕ} (hB0 : B0_nat ≤ B) :
    exp (-(242 : ℝ) * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 :=
  baker_bound_gap3_gaussian_nogo (le_of_lt two_forty_two_gt_two) hB0

theorem two_gaussian_nogo {B : ℕ} (hB0 : B0_nat ≤ B) :
    exp (-(2 : ℝ) * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 :=
  baker_bound_gap3_gaussian_nogo (le_refl (2 : ℝ)) hB0

/-- Requested successor name: Gaussian / Thue argument form still
    needs `C1 < 2`, which none of the displayed constants satisfy. -/
theorem baker_bound_gap3_z_i_nogo
    {C1 : ℝ} (hC1 : 2 ≤ C1)
    {B : ℕ} (hB0 : B0_nat ≤ B) :
    exp (-C1 * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 :=
  baker_bound_gap3_gaussian_nogo hC1 hB0

/-- Re-export: `13 ∣ 26` so `C` is a Ribet-lowering candidate. -/
theorem thirteen_dvd_twenty_six_reexport : 13 ∣ 26 :=
  BealMatveevBeal.BealKraus.thirteen_dvd_twenty_six

/-- Re-export: `13 ∤ 8` so primes in `A` need not lower. -/
theorem not_thirteen_dvd_eight_reexport : ¬ 13 ∣ 8 :=
  BealMatveevBeal.BealKraus.not_thirteen_dvd_eight

/-! ## Locked uninhabited Props -/

def baker_bound_gap3 : Prop :=
  BealLevel26Foundations.BealGap3BakerUpperBound.baker_bound_gap3

def wuestholz_product_theorem_exp : Prop :=
  BealMatveevBeal.BealKraus.wuestholz_product_theorem_exp

def baker_davenport_reduction : Prop :=
  BealMatveevBeal.BealKraus.baker_davenport_reduction

def bugeaud_LLL_reduction_proof : Prop :=
  BealMatveevBeal.BealKraus.bugeaud_LLL_reduction_proof

def darmon_merel_signature_44p : Prop :=
  BealMatveevBeal.BealKraus.darmon_merel_signature_44p

def kraus_uniform_residual_level : Prop :=
  BealMatveevBeal.BealKraus.kraus_uniform_residual_level

def ribet_level_lowering : Prop :=
  BealMatveevBeal.BealKraus.ribet_level_lowering

/-- `A² + i B²` is a unit times a thirteenth power in `ℤ[i]`.
    Needs UFD + coprimeness + units. Not in this file as a theorem. -/
def gaussian_associate_thirteenth_power : Prop :=
  ∀ A B : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13 → 0 < B →
    ∃ u v : ℤ, u ^ 2 + v ^ 2 = ((B + 3 : ℕ) : ℤ) ∧
      ∃ ε : GaussianInt, IsUnit ε ∧
        gaussianAlpha A B = ε * (⟨u, v⟩ : GaussianInt) ^ 13

/-- Zsigmondy primitive prime divisor of `αⁿ − βⁿ` in `ℤ[i]`.
    Not in Mathlib 4.12. -/
def zsigmondy_gaussian_primitive_divisor : Prop :=
  ∀ (α β : GaussianInt) (n : ℕ), 1 < n →
    ∃ p : GaussianInt, Prime p ∧ p ∣ α ^ n - β ^ n ∧
      ∀ k < n, ¬ p ∣ α ^ k - β ^ k

/-- Mihăilescu / Catalan: the only solution of `X^a − Y^b = 1` in
    naturals with `a,b > 1` is `3² − 2³`. Not in Mathlib 4.12.
    Gap-3 is `C¹³ − B⁴ = A⁴`, not Catalan shape. -/
def mihailescu_catalan : Prop :=
  ∀ X Y a b : ℕ, 1 < a → 1 < b → X ^ a + 1 = Y ^ b →
    X = 2 ∧ a = 3 ∧ Y = 3 ∧ b = 2 ∨ X = 0

#check C1_floor_eq
#check B0_nat_eq
#check log_thirteen_gt_five_div_two
#check five_div_log_thirteen_lt_two
#check gaussianAlpha_norm_of_sol
#check gaussianAlpha_mul_star
#check imPow13
#check gaussian_common_dvd
#check baker_bound_gap3_gaussian_nogo
#check baker_bound_gap3_z_i_nogo
#check C1_floor_gaussian_nogo
#check two_forty_two_gaussian_nogo
#check two_gaussian_nogo
#check baker_bound_gap3
#check gaussian_associate_thirteenth_power
#check zsigmondy_gaussian_primitive_divisor
#check mihailescu_catalan
#print axioms log_thirteen_gt_five_div_two
#print axioms gaussianAlpha_norm_of_sol
#print axioms baker_bound_gap3_gaussian_nogo
#print axioms baker_bound_gap3_z_i_nogo
#print axioms C1_floor_gaussian_nogo
#print axioms five_div_log_thirteen_lt_two
#print axioms gaussian_common_dvd

end BealMatveevBeal.BealKrausZsig
