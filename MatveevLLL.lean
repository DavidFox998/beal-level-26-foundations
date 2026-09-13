/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Importable copy of `Beal/Matveev/MatveevLLL.lean`.
  Lake's LEAN_PATH puts the relocated kernel's `Beal/` prefix first, so
  `Beal.Matveev.*` cannot be imported from other modules. This root
  module is the same namespace `BealMatveevBeal.MatveevLLL`.
-/
import Mathlib
import MatveevThm14Proof
import BealLevel26Foundations.Beal.FullProof.BealMatveevConstants
import BealLevel26Foundations.Beal.FullProof.BealMatveevInequality
import BealLevel26Foundations.Beal.FullProof.BealMatveevThm14
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

/-!
# Elementary continued-fraction lemmas toward Bugeaud / LLL

Bugeaud's LLL step (C = 10³⁰ lattice on `(1,0)` and
`(⌊C log A⌋, ⌊C log(B+3)⌋)`) is **not** in Mathlib 4.12. This file
does **not** inhabit Level 26 `baker_bound_gap3` and does **not**
close unrestricted `matveev_theorem_1_4_gap3_target`.

What it **does** prove, with axioms only
`[propext, Classical.choice, Quot.sound]`:

* `|log(B+3)/log A − 4/13| = |Λ| / (13 log A)`
  `≤ (B⁴/A⁴) / (13 log A)` on a gap-3 solution;
* `B⁴/A⁴ < 1/((B+3)⁹ − 1)`;
* the error is `< 1/(2 · 13²)`, so Legendre's theorem gives that
  `4/13` is a convergent of the log ratio (expected: `A⁴ ≈ (B+3)¹³`);
* the integer gap `1/(B+3)¹³ < B⁴/A⁴` never contradicts the
  `log(1+x) ≤ x` upper bound, so `matveev_thm14_n2_explicit_of_nat`
  does **not** force `B ≤ 10⁶`.

`bugeaud_LLL_reduction_proof` and the implication-form
`baker_bound_gap3_from_ratio` stay uninhabited `def Prop`. Inhabiting
either one would inhabit Level 26 `baker_bound_gap3` (no solutions
for `B > 10⁶`) via the already-proved `|Λ| ≤ B⁴/A⁴`. That is v25, and
it is still open. Not a minted v25 tag.
-/

noncomputable section

open Real
open BealLevel26Foundations.BealMatveevConstants
open BealLevel26Foundations.BealMatveevInequality
open BealLevel26Foundations.BealMatveevThm14
open BealLevel26Foundations.BealGap3BakerUpperBound

namespace BealMatveevBeal.MatveevLLL

/-- Baker census cutoff; same numeral as Level 26 `baker_B0`. -/
def B0_nat : ℕ := 1000000

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem B0_nat_eq_ten_pow_six : B0_nat = Nat.pow 10 6 := by
  decide

theorem B0_nat_eq_baker_B0 : B0_nat = baker_B0 := rfl

/-- Displayed Bugeaud scaling. Mathlib 4.12 has no LLL theorem that
    turns this lattice into `B ≤ B0_nat`. -/
def LLL_C_nat : ℕ := 10 ^ 30

theorem LLL_C_nat_eq : LLL_C_nat = 10 ^ 30 := rfl

def LLL_C_real : ℝ := (LLL_C_nat : ℝ)

/-- First displayed basis vector `(1, 0)`. -/
def LLL_e1 : ℤ × ℤ := (1, 0)

theorem LLL_e1_eq : LLL_e1 = (1, 0) := rfl

/-- Second displayed basis vector `(⌊C log A⌋, ⌊C log(B+3)⌋)`. -/
def LLL_e2 (A B : ℕ) : ℤ × ℤ :=
  (⌊LLL_C_real * log (A : ℝ)⌋, ⌊LLL_C_real * log ((B + 3 : ℕ) : ℝ)⌋)

/-- Implication form of Baker `B ≤ 10⁶` from the ratio upper bound.
    Equivalent (via the proved `|Λ| ≤ B⁴/A⁴`) to “every gap-3 solution
    has `B ≤ B0_nat`”, which is Level 26 `baker_bound_gap3`.
    Stays a `def Prop`. -/
def baker_bound_gap3_from_ratio : Prop :=
  ∀ A B : ℕ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
      0 < B →
        |4 * log (A : ℝ) - 13 * log (B + 3 : ℝ)| ≤
            (B : ℝ) ^ 4 / (A : ℝ) ^ 4 →
          B ≤ B0_nat

/-- Requested Bugeaud/LLL close. Uninhabited: the CF lemmas below do
    not force `B ≤ B0_nat`. Not a theorem. -/
def bugeaud_LLL_reduction_proof : Prop := baker_bound_gap3_from_ratio

noncomputable def log_ratio (A B : ℕ) : ℝ :=
  log ((B + 3 : ℕ) : ℝ) / log (A : ℝ)

noncomputable def Lambda (A B : ℕ) : ℝ :=
  4 * log (A : ℝ) - 13 * log ((B + 3 : ℕ) : ℝ)

theorem Lambda_eq_matveev_log_form (A B : ℕ) :
    Lambda A B = matveev_log_form A B := by
  unfold Lambda matveev_log_form
  rfl

theorem Lambda_eq_expanded (A B : ℕ) :
    Lambda A B = 4 * log (A : ℝ) - 13 * log (B + 3 : ℝ) := by
  unfold Lambda
  have hcast : ((B + 3 : ℕ) : ℝ) = (B + 3 : ℝ) := by
    rw [Nat.cast_add, Nat.cast_ofNat]
  rw [hcast]

lemma four_div_thirteen_int : (4 / 13 : ℚ) = ((4 : ℤ) / (13 : ℤ) : ℚ) := by
  norm_cast

lemma four_coprime_thirteen : Nat.Coprime (Int.natAbs 4) (Int.natAbs 13) := by
  decide

lemma four_div_thirteen_num : (4 / 13 : ℚ).num = 4 := by
  have h := Rat.num_div_eq_of_coprime (by decide : (0 : ℤ) < 13) four_coprime_thirteen
  rw [four_div_thirteen_int]
  exact h

lemma four_div_thirteen_den_nat : (4 / 13 : ℚ).den = 13 := by
  have h : (((4 : ℤ) / (13 : ℤ) : ℚ).den : ℤ) = 13 :=
    Rat.den_div_eq_of_coprime (by decide : (0 : ℤ) < 13) four_coprime_thirteen
  rw [four_div_thirteen_int]
  exact_mod_cast h

lemma four_div_thirteen_den : ((4 / 13 : ℚ).den : ℝ) = 13 := by
  rw [four_div_thirteen_den_nat]
  norm_num

lemma four_div_thirteen_cast : ((4 / 13 : ℚ) : ℝ) = (4 / 13 : ℝ) := by
  rw [Rat.cast_def, four_div_thirteen_num, four_div_thirteen_den_nat]
  norm_num

/-- `|log(B+3)/log A − 4/13| = |Λ| / (13 log A)`. -/
theorem abs_log_ratio_sub_four_thirteenths
    (A B : ℕ) (hA : 1 < A) :
    |log_ratio A B - (4 / 13 : ℝ)| =
      |Lambda A B| / (13 * log (A : ℝ)) := by
  have hA1 : (1 : ℝ) < A := by exact_mod_cast hA
  have hlogA : (0 : ℝ) < log (A : ℝ) := Real.log_pos hA1
  have h13log : (0 : ℝ) < (13 : ℝ) * log (A : ℝ) :=
    mul_pos (by norm_num) hlogA
  have hcalc :
      log_ratio A B - (4 / 13 : ℝ) =
        (13 * log ((B + 3 : ℕ) : ℝ) - 4 * log (A : ℝ)) /
          (13 * log (A : ℝ)) := by
    unfold log_ratio
    field_simp [hlogA.ne']
    ring
  rw [hcalc, abs_div, abs_of_pos h13log]
  unfold Lambda
  rw [abs_sub_comm]

/-- On a solution, `|Λ| ≤ B⁴/A⁴` gives the CF error bound. -/
theorem abs_log_ratio_le_ratio_div
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    |log_ratio A B - (4 / 13 : ℝ)| ≤
      ((B : ℝ) ^ 4 / (A : ℝ) ^ 4) / (13 * log (A : ℝ)) := by
  have hgt := MatveevThm14Proof.gap3_A_gt_one A B hsol hB
  have hid := abs_log_ratio_sub_four_thirteenths A B hgt.1
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hle := matveev_gap3_abs_lambda_le_ratio hpow
  have hA1 : (1 : ℝ) < A := by exact_mod_cast hgt.1
  have hlogA : (0 : ℝ) < log (A : ℝ) := Real.log_pos hA1
  have hden : (0 : ℝ) < 13 * log (A : ℝ) :=
    mul_pos (by norm_num) hlogA
  have hΛ : |Lambda A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
    rw [Lambda_eq_matveev_log_form]
    exact hle
  rw [hid]
  exact div_le_div_of_nonneg_right hΛ (le_of_lt hden)

/-- `B⁴/A⁴ < 1/((B+3)⁹ − 1)` because `B < B+3` and
    `A⁴ = (B+3)¹³ − B⁴ > (B+3)⁴((B+3)⁹ − 1)`. -/
theorem ratio_lt_inv_B3_pow_nine
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (B : ℝ) ^ 4 / (A : ℝ) ^ 4 <
      1 / (((B + 3 : ℕ) : ℝ) ^ 9 - 1) := by
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hA4 := matveev_gap3_A_pow_eq_B3_pow_sub_B_pow hpow
  have hBlt : (B : ℝ) < ((B + 3 : ℕ) : ℝ) := by
    have : B < B + 3 := Nat.lt_add_of_pos_right (by decide : 0 < 3)
    exact_mod_cast this
  have hBnonneg : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hB4lt : (B : ℝ) ^ 4 < ((B + 3 : ℕ) : ℝ) ^ 4 :=
    pow_lt_pow_left hBlt hBnonneg (by decide : (4 : ℕ) ≠ 0)
  have hB3pos : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) := by
    have : 0 < B + 3 := Nat.add_pos_right B (by decide : 0 < 3)
    exact_mod_cast this
  have hB3_4_pos : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 4 := pow_pos hB3pos 4
  have hB3_gt1 : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) := by
    have : 1 < B + 3 :=
      Nat.lt_of_lt_of_le (by decide : 1 < 4)
        (Nat.add_le_add_right (Nat.succ_le_of_lt hB) 3)
    exact_mod_cast this
  have h9 : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 9 :=
    one_lt_pow hB3_gt1 (by decide : (9 : ℕ) ≠ 0)
  have h9sub : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 9 - 1 := by linarith
  have hpow13 :
      ((B + 3 : ℕ) : ℝ) ^ 13 =
        ((B + 3 : ℕ) : ℝ) ^ 4 * ((B + 3 : ℕ) : ℝ) ^ 9 := by
    rw [← pow_add]
  have hfact :
      ((B + 3 : ℕ) : ℝ) ^ 13 - ((B + 3 : ℕ) : ℝ) ^ 4 =
        ((B + 3 : ℕ) : ℝ) ^ 4 * (((B + 3 : ℕ) : ℝ) ^ 9 - 1) := by
    rw [hpow13]
    ring
  have hA4gt :
      ((B + 3 : ℕ) : ℝ) ^ 4 * (((B + 3 : ℕ) : ℝ) ^ 9 - 1) <
        (A : ℝ) ^ 4 := by
    rw [hA4, ← hfact]
    linarith [hB4lt]
  have hA4pos : (0 : ℝ) < (A : ℝ) ^ 4 := by
    have : 0 < A := matveev_gap3_A_pos_of_pos_B hpow hB
    exact pow_pos (Nat.cast_pos.mpr this) 4
  have hdenpos :
      (0 : ℝ) <
        ((B + 3 : ℕ) : ℝ) ^ 4 * (((B + 3 : ℕ) : ℝ) ^ 9 - 1) :=
    mul_pos hB3_4_pos h9sub
  have h1 :
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 <
        ((B + 3 : ℕ) : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    (div_lt_div_right hA4pos).mpr hB4lt
  have h2 :
      ((B + 3 : ℕ) : ℝ) ^ 4 / (A : ℝ) ^ 4 <
        ((B + 3 : ℕ) : ℝ) ^ 4 /
          (((B + 3 : ℕ) : ℝ) ^ 4 * (((B + 3 : ℕ) : ℝ) ^ 9 - 1)) :=
    div_lt_div_of_pos_left hB3_4_pos hdenpos hA4gt
  have h3 :
      ((B + 3 : ℕ) : ℝ) ^ 4 /
          (((B + 3 : ℕ) : ℝ) ^ 4 * (((B + 3 : ℕ) : ℝ) ^ 9 - 1)) =
        1 / (((B + 3 : ℕ) : ℝ) ^ 9 - 1) := by
    rw [div_mul_eq_div_div, div_self hB3_4_pos.ne']
  exact lt_trans h1 (h3 ▸ h2)

/-- Legendre threshold `1/(2·13²) = 1/338`. -/
theorem legendre_threshold_eq :
    (1 : ℝ) / (2 * (13 : ℝ) ^ 2) = 1 / 338 := by
  norm_num

/-- On every positive-`B` gap-3 solution the log-ratio error is
    strictly inside Legendre's `1/(2q²)` box for `q = 13`.
    This is expected (`A⁴ ≈ (B+3)¹³`), not a Baker contradiction. -/
theorem cf_error_lt_legendre
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    |log_ratio A B - (4 / 13 : ℝ)| < 1 / (2 * (13 : ℝ) ^ 2) := by
  have hgt := MatveevThm14Proof.gap3_A_gt_one A B hsol hB
  have hle := abs_log_ratio_le_ratio_div hsol hB
  have hratio := ratio_lt_inv_B3_pow_nine hsol hB
  have hA1 : (1 : ℝ) < A := by exact_mod_cast hgt.1
  have hlogA : (0 : ℝ) < log (A : ℝ) := Real.log_pos hA1
  have hlogA2 := MatveevThm14Proof.log_nat_gt_half hgt.1
  have hden : (0 : ℝ) < 13 * log (A : ℝ) :=
    mul_pos (by norm_num) hlogA
  have hB3_gt1 : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) := by
    exact_mod_cast hgt.2
  have h9 : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 9 :=
    one_lt_pow hB3_gt1 (by decide : (9 : ℕ) ≠ 0)
  have h9sub : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 9 - 1 := by linarith
  have hnum :
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 / (13 * log (A : ℝ)) <
        (1 / (((B + 3 : ℕ) : ℝ) ^ 9 - 1)) / (13 * log (A : ℝ)) :=
    (div_lt_div_right hden).mpr hratio
  have hrew :
      (1 / (((B + 3 : ℕ) : ℝ) ^ 9 - 1)) / (13 * log (A : ℝ)) =
        1 / ((((B + 3 : ℕ) : ℝ) ^ 9 - 1) * (13 * log (A : ℝ))) := by
    field_simp [h9sub.ne', hden.ne']
  have hprod :
      (26 : ℝ) <
        log (A : ℝ) * (((B + 3 : ℕ) : ℝ) ^ 9 - 1) := by
    have hmin : (262143 : ℝ) ≤ ((B + 3 : ℕ) : ℝ) ^ 9 - 1 := by
      have h4 : (4 : ℕ) ≤ B + 3 :=
        Nat.add_le_add_right (Nat.succ_le_of_lt hB) 3
      have h4r : (4 : ℝ) ≤ ((B + 3 : ℕ) : ℝ) := by exact_mod_cast h4
      have hpow : (4 : ℝ) ^ 9 ≤ ((B + 3 : ℕ) : ℝ) ^ 9 :=
        pow_le_pow_left (by norm_num) h4r 9
      have hnum : (4 : ℝ) ^ 9 = 262144 := by norm_num
      linarith [hpow, hnum]
    have hmul : (1 / 2 : ℝ) * (262143 : ℝ) ≤
        log (A : ℝ) * (((B + 3 : ℕ) : ℝ) ^ 9 - 1) :=
      mul_le_mul (le_of_lt hlogA2) hmin (by norm_num) (le_of_lt hlogA)
    linarith
  have h338 :
      (338 : ℝ) <
        (((B + 3 : ℕ) : ℝ) ^ 9 - 1) * (13 * log (A : ℝ)) := by
    have : (338 : ℝ) = 13 * 26 := by norm_num
    rw [this, mul_comm (((B + 3 : ℕ) : ℝ) ^ 9 - 1)]
    have h := mul_lt_mul_of_pos_left hprod (by norm_num : (0 : ℝ) < 13)
    convert h using 1
    ring
  have hfinal :
      1 / ((((B + 3 : ℕ) : ℝ) ^ 9 - 1) * (13 * log (A : ℝ))) <
        1 / 338 :=
    (one_div_lt_one_div (mul_pos h9sub hden) (by norm_num : (0 : ℝ) < 338)).2
      h338
  have hthr : (1 : ℝ) / 338 = 1 / (2 * (13 : ℝ) ^ 2) := by norm_num
  exact lt_trans (hle.trans_lt (hrew ▸ hnum)) (hthr ▸ hfinal)

/-- Same Legendre box on the Baker range `B > 10⁶`. -/
theorem cf_error_lt_legendre_of_B_gt_B0
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (_hB0 : B0_nat < B) :
    |log_ratio A B - (4 / 13 : ℝ)| < 1 / (2 * (13 : ℝ) ^ 2) :=
  cf_error_lt_legendre hsol hB

/-- Legendre: `4/13` is a convergent of `log(B+3)/log A`.
    This is the elementary CF substitute for the displayed C=10³⁰
    lattice. It does **not** bound `B`. -/
theorem four_thirteenths_is_convergent
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    ∃ n : ℕ, (4 / 13 : ℚ) = (log_ratio A B).convergent n := by
  have herr := cf_error_lt_legendre hsol hB
  have h : |log_ratio A B - (4 / 13 : ℚ)| <
      1 / (2 * ((4 / 13 : ℚ).den : ℝ) ^ 2) := by
    rw [four_div_thirteen_cast, four_div_thirteen_den]
    exact herr
  exact Real.exists_rat_eq_convergent h

theorem four_thirteenths_is_convergent_of_B_gt_B0
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (_hB0 : B0_nat < B) :
    ∃ n : ℕ, (4 / 13 : ℚ) = (log_ratio A B).convergent n :=
  four_thirteenths_is_convergent hsol hB

/-- Integer gap versus the ratio: `1/(B+3)¹³ < B⁴/A⁴`.
    `matveev_thm14_n2_explicit_of_nat` is at most this gap, so it
    never contradicts `|Λ| ≤ B⁴/A⁴` and never forces `B ≤ 10⁶`. -/
theorem integer_gap_lt_ratio
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (1 : ℝ) / ((B + 3 : ℕ) : ℝ) ^ 13 <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hA4 := matveev_gap3_A_pow_eq_B3_pow_sub_B_pow hpow
  have hB3pos : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) := by
    have : 0 < B + 3 := Nat.add_pos_right B (by decide : 0 < 3)
    exact_mod_cast this
  have hB3_13 : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 13 := pow_pos hB3pos 13
  have hB4nat : 1 ≤ B ^ 4 := Nat.succ_le_of_lt (Nat.pos_pow_of_pos 4 hB)
  have hB4 : (1 : ℝ) ≤ (B : ℝ) ^ 4 := by exact_mod_cast hB4nat
  have hA4pos : (0 : ℝ) < (A : ℝ) ^ 4 := by
    have : 0 < A := matveev_gap3_A_pos_of_pos_B hpow hB
    exact pow_pos (Nat.cast_pos.mpr this) 4
  have hcleared :
      ((B + 3 : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 <
        (B : ℝ) ^ 4 * ((B + 3 : ℕ) : ℝ) ^ 13 := by
    have hlt : ((B + 3 : ℕ) : ℝ) ^ 13 <
        ((B + 3 : ℕ) : ℝ) ^ 13 + 1 := by linarith
    have hscale : ((B + 3 : ℕ) : ℝ) ^ 13 + 1 ≤
        (B : ℝ) ^ 4 * (((B + 3 : ℕ) : ℝ) ^ 13 + 1) := by
      have : (1 : ℝ) * (((B + 3 : ℕ) : ℝ) ^ 13 + 1) ≤
          (B : ℝ) ^ 4 * (((B + 3 : ℕ) : ℝ) ^ 13 + 1) :=
        mul_le_mul_of_nonneg_right hB4 (by linarith [hB3_13])
      simpa using this
    have : ((B + 3 : ℕ) : ℝ) ^ 13 + 1 ≤
        (B : ℝ) ^ 4 * ((B + 3 : ℕ) : ℝ) ^ 13 + (B : ℝ) ^ 4 := by
      calc
        ((B + 3 : ℕ) : ℝ) ^ 13 + 1 ≤
            (B : ℝ) ^ 4 * (((B + 3 : ℕ) : ℝ) ^ 13 + 1) := hscale
        _ = (B : ℝ) ^ 4 * ((B + 3 : ℕ) : ℝ) ^ 13 + (B : ℝ) ^ 4 := by
          ring
    linarith [hlt, this]
  have hA4eq : (A : ℝ) ^ 4 = ((B + 3 : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 := hA4
  have hdiv :
      ((B + 3 : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 <
        (B : ℝ) ^ 4 * ((B + 3 : ℕ) : ℝ) ^ 13 := hcleared
  have : (A : ℝ) ^ 4 < (B : ℝ) ^ 4 * ((B + 3 : ℕ) : ℝ) ^ 13 := by
    rwa [hA4eq]
  have hiff :=
    (div_lt_div_iff hB3_13 hA4pos).mpr
      (by
        have : (1 : ℝ) * (A : ℝ) ^ 4 <
            (B : ℝ) ^ 4 * ((B + 3 : ℕ) : ℝ) ^ 13 := by
          simpa using this
        exact this)
  simpa [one_div] using hiff

/-- Integer-gap lower bound is `1/(B+3)¹³` on a solution (`A⁴ < (B+3)¹³`). -/
theorem abs_Lambda_ge_inv_B3_pow
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (1 : ℝ) / ((B + 3 : ℕ) : ℝ) ^ 13 ≤ |Lambda A B| := by
  have hgt := MatveevThm14Proof.gap3_A_gt_one A B hsol hB
  have hΛ := MatveevThm14Proof.Lambda_gap3_ne_zero A B hsol hB
  have hge :=
    MatveevThm14Proof.abs_log_form_ge_inv_max A (B + 3) hgt.1 hgt.2 hΛ
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hApow : A ^ 4 < (B + 3) ^ 13 := by
    have hB4 : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hB
    have hlt : A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
    rwa [hsol] at hlt
  have hmax : max ((A : ℝ) ^ 4) (((B + 3 : ℕ) : ℝ) ^ 13) =
      ((B + 3 : ℕ) : ℝ) ^ 13 := by
    apply max_eq_right
    have : (A : ℝ) ^ 4 ≤ ((B + 3 : ℕ) : ℝ) ^ 13 := by
      have hle : A ^ 4 ≤ (B + 3) ^ 13 := Nat.le_of_lt hApow
      exact_mod_cast hle
    exact this
  unfold Lambda
  rw [hmax] at hge
  exact hge

/-- Sandwich: integer gap ≤ `|Λ|` ≤ ratio, and the gap is strictly
    smaller than the ratio. No Baker cutoff. -/
theorem integer_gap_le_abs_Lambda_le_ratio
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (1 : ℝ) / ((B + 3 : ℕ) : ℝ) ^ 13 ≤ |Lambda A B| ∧
      |Lambda A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 ∧
        (1 : ℝ) / ((B + 3 : ℕ) : ℝ) ^ 13 <
          (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  ⟨abs_Lambda_ge_inv_B3_pow hsol hB,
    by
      have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
      rw [Lambda_eq_matveev_log_form]
      exact matveev_gap3_abs_lambda_le_ratio hpow,
    integer_gap_lt_ratio hsol hB⟩

/-- The implication-form Baker bound plus the proved ratio upper
    bound is exactly “every solution has `B ≤ B0_nat`”. -/
theorem solutions_B_le_B0_of_from_ratio
    (h : baker_bound_gap3_from_ratio)
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    B ≤ B0_nat := by
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hle := matveev_gap3_abs_lambda_le_ratio hpow
  have hΛ : |4 * log (A : ℝ) - 13 * log (B + 3 : ℝ)| ≤
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
    rw [← Lambda_eq_expanded, Lambda_eq_matveev_log_form]
    exact hle
  exact h A B hsol hB hΛ

theorem baker_bound_gap3_from_ratio_of_solutions_B_le
    (h : ∀ A B : ℕ,
      A ^ 4 + B ^ 4 = (B + 3) ^ 13 → 0 < B → B ≤ B0_nat) :
    baker_bound_gap3_from_ratio := by
  intro A B hsol hB _hupper
  exact h A B hsol hB

/-- Inhabiting the implication form inhabits Level 26
    `baker_bound_gap3`. We do **not** inhabit either. -/
theorem baker_bound_gap3_of_from_ratio
    (h : baker_bound_gap3_from_ratio) : baker_bound_gap3 := by
  refine ⟨B0_nat, B0_nat_eq_ten_pow_six, ?_⟩
  intro B hB0 hEx
  obtain ⟨A, hsol⟩ := hEx
  have hB : 0 < B := matveev_gap3_B_pos_of_solution hsol
  have hle := solutions_B_le_B0_of_from_ratio h hsol hB
  exact (not_le_of_gt hB0) hle

/-- Type-correct packaging only: does not inhabit `hLLL`. -/
theorem baker_bound_gap3_of_bugeaud_LLL_reduction_proof
    (h : bugeaud_LLL_reduction_proof) : baker_bound_gap3 :=
  baker_bound_gap3_of_from_ratio h

#check B0_nat
#check baker_bound_gap3_from_ratio
#check bugeaud_LLL_reduction_proof
#check abs_log_ratio_sub_four_thirteenths
#check abs_log_ratio_le_ratio_div
#check ratio_lt_inv_B3_pow_nine
#check cf_error_lt_legendre
#check four_thirteenths_is_convergent
#check integer_gap_lt_ratio
#check integer_gap_le_abs_Lambda_le_ratio
#check baker_bound_gap3_of_from_ratio
#print axioms four_thirteenths_is_convergent
#print axioms integer_gap_lt_ratio
#print axioms baker_bound_gap3_of_from_ratio

end BealMatveevBeal.MatveevLLL
