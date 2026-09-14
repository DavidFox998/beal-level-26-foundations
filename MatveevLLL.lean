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
  does **not** force `B ≤ 10⁶`;
* the tighter gap `log(1+u) ≥ u/(1+u)` gives
  `B⁴/(B+3)¹³ ≤ |Λ| ≤ B⁴/A⁴`, still the same order
  (ratio of sides is `(B+3)¹³/A⁴ = 1 + B⁴/A⁴`), so still no cutoff;
* `A⁴ > B⁵` so `|Λ| ≤ B⁴/A⁴ < 1/B` (`abs_Lambda_le_inv_B`);
  the elementary gap `1/(B+3)¹³` is still `< 1/B`, so this
  upper bound is not a Baker–Davenport cutoff;
* `1/max(4 log A, 13 log(B+3))` is **not** a lower bound on a
  solution (`abs_Lambda_lt_inv_max_log_coeff`); combining it with
  `|Λ| ≤ 1/B` would be a false close;
* Track 1 `exp(−C1 …)` is `< B⁴/A⁴` (`track1_exp_lt_ratio`);
* the displayed C=10³⁰ floor form approximates `C Λ` to error `< 17`
  (`LLL_e2_linear_form_approx`);
* the rank-3 lattice with columns `(1,0,⌊C log A⌋)`,
  `(0,1,⌊C log(B+3)⌋)`, `(0,0,C)` has `det = C`
  (`LLL_basis_det`);
* `v = 4 b₁ − 13 b₂` lies in the lattice, and on a solution
  with `B > 10⁶` the tight ratio bound makes `C|Λ| < 1`, so
  `‖v‖ < 32` and `λ₁(L) ≤ ‖v‖` (`LLL_v_norm_lt_thirty_two`,
  `LLL_lambda1_lt_thirty_two`). Minkowski is an *upper* bound
  on `λ₁` and does not enlarge `|Λ|`.

Mathlib 4.12 has no LLL shortest-vector theorem. Gram–Schmidt
coefficients, the LLL-reduced predicate, termination, and the
`‖b₁‖ ≤ 2 λ₁` / `2^{1/2} C^{1/3}` bounds stay `def Prop`.
`|Λ| < 1/B` is too weak to make `C|Λ|` small (`C/B = 10^{24}`);
the `‖v‖ < 32` estimate uses `B⁴/A⁴ < 1/((B+3)⁹−1)`, not `1/B`.
A genuine `B ≤ 10⁶` cutoff would need a lower bound on `|Λ|`
stronger than `B⁴/A⁴`. That is circular without an external
LLL/Baker–Davenport theorem. Not v25.

Baker–Davenport / Bugeaud LLL would need a lower bound strictly
stronger than `B⁴/A⁴` for `B > 10⁶`. Mathlib 4.12 has no such
theorem. The Matveev product `O((log B)³)` grows with `B` and makes
`exp(−product)` *smaller*, not larger.

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

/-- `log(1+u) ≥ u/(1+u)` for `u > 0`, from `1 − x⁻¹ ≤ log x`. -/
theorem log_one_plus_ge_div {u : ℝ} (hu : 0 < u) :
    u / (1 + u) ≤ log (1 + u) := by
  have hpos : (0 : ℝ) < 1 + u := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hpos
  have hrew : (1 : ℝ) - (1 + u)⁻¹ = u / (1 + u) := by
    rw [inv_eq_one_div, one_sub_div hpos.ne']
    ring
  rwa [hrew] at h

/-- Tight integer-side lower bound: `|Λ| ≥ B⁴/(B+3)¹³`.
    Same order as the upper bound `B⁴/A⁴ = B⁴/((B+3)¹³ − B⁴)`. -/
theorem abs_Lambda_ge_B4_div_B3_pow
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 ≤ |Lambda A B| := by
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have habs := matveev_gap3_abs_lambda_eq_log_one_plus_ratio hpow
  have hu := matveev_gap3_B_pow_div_A_pow_pos hpow
  have hge := log_one_plus_ge_div hu
  have hA4pos := matveev_gap3_A_pow_pos hpow
  have hsum : (A : ℝ) ^ 4 + (B : ℝ) ^ 4 = ((B + 3 : ℕ) : ℝ) ^ 13 := by
    have hA4 := matveev_gap3_A_pow_eq_B3_pow_sub_B_pow hpow
    linarith
  have hdiv :
      ((B : ℝ) ^ 4 / (A : ℝ) ^ 4) / (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) =
        (B : ℝ) ^ 4 / ((A : ℝ) ^ 4 + (B : ℝ) ^ 4) := by
    have hne : (A : ℝ) ^ 4 ≠ 0 := hA4pos.ne'
    field_simp [hne]
  rw [Lambda_eq_matveev_log_form, habs]
  calc
    (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13
        = (B : ℝ) ^ 4 / ((A : ℝ) ^ 4 + (B : ℝ) ^ 4) := by rw [hsum]
    _ = ((B : ℝ) ^ 4 / (A : ℝ) ^ 4) /
          (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := hdiv.symm
    _ ≤ log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := hge

/-- The tight lower bound is strictly below the ratio upper bound. -/
theorem B4_div_B3_pow_lt_ratio
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hA4pos := matveev_gap3_A_pow_pos hpow
  have hB4pos : (0 : ℝ) < (B : ℝ) ^ 4 :=
    pow_pos (Nat.cast_pos.mpr hB) 4
  have hApow : (A : ℝ) ^ 4 < ((B + 3 : ℕ) : ℝ) ^ 13 := by
    have hA4 := matveev_gap3_A_pow_eq_B3_pow_sub_B_pow hpow
    linarith [hB4pos]
  exact div_lt_div_of_pos_left hB4pos hA4pos hApow

/-- Tight sandwich: `B⁴/(B+3)¹³ ≤ |Λ| ≤ B⁴/A⁴`, sides the same order.
    No extra LLL factor, so no `B ≤ 10⁶`. -/
theorem abs_Lambda_tight_sandwich
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 ≤ |Lambda A B| ∧
      |Lambda A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 ∧
        (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 <
          (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  ⟨abs_Lambda_ge_B4_div_B3_pow hsol hB,
    by
      have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
      rw [Lambda_eq_matveev_log_form]
      exact matveev_gap3_abs_lambda_le_ratio hpow,
    B4_div_B3_pow_lt_ratio hsol hB⟩

/-! ## Baker–Davenport auxiliaries (not a `B ≤ 10⁶` close)

The requested reduction lemma `|Λ| ≤ 1/B` on `B > 10⁶` is true
because `A⁴ > B⁵`. The elementary `1/max(A⁴,C¹³)` gap is
`1/(B+3)¹³ < 1/B`, so the two sides never contradict.
`1/max(4 log A, 13 log(B+3))` is *larger* than `|Λ|` on every
positive-`B` solution, so it is not a lower bound and cannot be
combined with `|Λ| ≤ 1/B` to inhabit `baker_bound_gap3`.
-/

theorem B_pow_five_add_B_pow_four_lt_B3_pow
    {B : ℕ} (_hB : 0 < B) :
    (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 3 : ℕ) : ℝ) ^ 13 := by
  have hx : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : ((B + 3 : ℕ) : ℝ) = (B : ℝ) + 3 := by
    rw [Nat.cast_add, Nat.cast_ofNat]
  have h5 : (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 3 : ℕ) : ℝ) ^ 5 := by
    rw [hC]
    have hexp : ((B : ℝ) + 3) ^ 5 =
        (B : ℝ) ^ 5 + 15 * (B : ℝ) ^ 4 + 90 * (B : ℝ) ^ 3 +
          270 * (B : ℝ) ^ 2 + 405 * (B : ℝ) + 243 := by
      ring
    have h3 : (0 : ℝ) ≤ (B : ℝ) ^ 3 := pow_nonneg hx 3
    have h2 : (0 : ℝ) ≤ (B : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hexp, h3, h2, hx]
  have hC1 : (1 : ℝ) ≤ ((B + 3 : ℕ) : ℝ) := by
    have : 1 ≤ B + 3 := Nat.succ_le_of_lt (Nat.add_pos_right B (by decide : 0 < 3))
    exact_mod_cast this
  have h513 : ((B + 3 : ℕ) : ℝ) ^ 5 ≤ ((B + 3 : ℕ) : ℝ) ^ 13 :=
    pow_le_pow_right hC1 (by decide : (5 : ℕ) ≤ 13)
  exact lt_of_lt_of_le h5 h513

/-- On a solution, `A⁴ > B⁵`. -/
theorem A_pow_gt_B_pow_five
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (B : ℝ) ^ 5 < (A : ℝ) ^ 4 := by
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hA4 := matveev_gap3_A_pow_eq_B3_pow_sub_B_pow hpow
  have hsum := B_pow_five_add_B_pow_four_lt_B3_pow hB
  linarith [hA4, hsum]

/-- Ratio upper bound is `< 1/B`. -/
theorem ratio_lt_inv_B
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (B : ℝ) ^ 4 / (A : ℝ) ^ 4 < 1 / (B : ℝ) := by
  have hA4pos : (0 : ℝ) < (A : ℝ) ^ 4 := by
    have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
    exact matveev_gap3_A_pow_pos hpow
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hgt := A_pow_gt_B_pow_five hsol hB
  have hB4pos : (0 : ℝ) < (B : ℝ) ^ 4 := pow_pos hBpos 4
  have : (B : ℝ) ^ 4 * (B : ℝ) < (A : ℝ) ^ 4 := by
    have : (B : ℝ) ^ 5 = (B : ℝ) ^ 4 * (B : ℝ) := by ring
    rwa [this] at hgt
  rw [div_lt_div_iff hA4pos hBpos, one_mul]
  exact this

/-- Requested upper-bound half: `|Λ| ≤ 1/B` on a solution.
    Not a Baker–Davenport cutoff: the elementary gap is smaller. -/
theorem abs_Lambda_le_inv_B
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    |Lambda A B| < 1 / (B : ℝ) := by
  have hsand := abs_Lambda_tight_sandwich hsol hB
  exact lt_of_le_of_lt hsand.2.1 (ratio_lt_inv_B hsol hB)

theorem abs_Lambda_le_inv_B_of_B_gt_B0
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (_hB0 : B0_nat < B) :
    |Lambda A B| < 1 / (B : ℝ) :=
  abs_Lambda_le_inv_B hsol hB

/-- Elementary `1/(B+3)¹³` is strictly below `1/B`. -/
theorem inv_B3_pow_lt_inv_B {B : ℕ} (hB : 0 < B) :
    (1 : ℝ) / ((B + 3 : ℕ) : ℝ) ^ 13 < 1 / (B : ℝ) := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hCpos : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) := by
    have : 0 < B + 3 := Nat.add_pos_right B (by decide : 0 < 3)
    exact_mod_cast this
  have hC13 : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 13 := pow_pos hCpos 13
  have hlt : (B : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 13 := by
    have h1 : (B : ℝ) < ((B + 3 : ℕ) : ℝ) := by
      have : B < B + 3 := Nat.lt_add_of_pos_right (by decide : 0 < 3)
      exact_mod_cast this
    have hC1 : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) := by
      have : 1 < B + 3 :=
        Nat.lt_of_lt_of_le (by decide : 1 < 4)
          (Nat.add_le_add_right (Nat.succ_le_of_lt hB) 3)
      exact_mod_cast this
    have hpow : ((B + 3 : ℕ) : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 13 :=
      lt_self_pow hC1 (by decide : (1 : ℕ) < 13)
    exact lt_trans h1 hpow
  exact (one_div_lt_one_div hC13 hBpos).2 hlt

/-- Integer-gap `1/max(A⁴,C¹³)` never contradicts `|Λ| < 1/B`. -/
theorem elementary_inv_max_compatible_with_inv_B
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (1 : ℝ) / ((B + 3 : ℕ) : ℝ) ^ 13 < 1 / (B : ℝ) ∧
      (1 : ℝ) / ((B + 3 : ℕ) : ℝ) ^ 13 ≤ |Lambda A B| ∧
        |Lambda A B| < 1 / (B : ℝ) :=
  ⟨inv_B3_pow_lt_inv_B hB,
    abs_Lambda_ge_inv_B3_pow hsol hB,
    abs_Lambda_le_inv_B hsol hB⟩

theorem four_logA_lt_thirteen_logB3
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    4 * log (A : ℝ) < 13 * log ((B + 3 : ℕ) : ℝ) := by
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hA4pos := matveev_gap3_A_pow_pos hpow
  have hB4pos : (0 : ℝ) < (B : ℝ) ^ 4 :=
    pow_pos (by exact_mod_cast hB) 4
  have hApow : (A : ℝ) ^ 4 < ((B + 3 : ℕ) : ℝ) ^ 13 := by
    have hA4 := matveev_gap3_A_pow_eq_B3_pow_sub_B_pow hpow
    linarith [hB4pos]
  have hlog := Real.log_lt_log hA4pos hApow
  rw [Real.log_pow, Real.log_pow] at hlog
  exact hlog

theorem max_log_coeff_eq_thirteen_logB3
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    max (4 * log (A : ℝ)) (13 * log ((B + 3 : ℕ) : ℝ)) =
      13 * log ((B + 3 : ℕ) : ℝ) :=
  max_eq_right (le_of_lt (four_logA_lt_thirteen_logB3 hsol hB))

/-- The proposed `1/max(4 log A, 13 log(B+3))` lower bound is
    false on every positive-`B` gap-3 solution. -/
theorem abs_Lambda_lt_inv_max_log_coeff
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    |Lambda A B| <
      1 / max (4 * log (A : ℝ)) (13 * log ((B + 3 : ℕ) : ℝ)) := by
  have hgt := MatveevThm14Proof.gap3_A_gt_one A B hsol hB
  have hC1 : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) := by exact_mod_cast hgt.2
  have hlogC : (0 : ℝ) < log ((B + 3 : ℕ) : ℝ) := Real.log_pos hC1
  have hmax := max_log_coeff_eq_thirteen_logB3 hsol hB
  rw [hmax]
  have hratio := ratio_lt_inv_B3_pow_nine hsol hB
  have hsand := abs_Lambda_tight_sandwich hsol hB
  have h9sub : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 9 - 1 := by
    have h9 : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 9 :=
      one_lt_pow hC1 (by decide : (9 : ℕ) ≠ 0)
    linarith
  have hCpos : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) :=
    lt_trans (by norm_num : (0 : ℝ) < 1) hC1
  have hloglt : log ((B + 3 : ℕ) : ℝ) < ((B + 3 : ℕ) : ℝ) := by
    have hle := add_one_le_exp (log ((B + 3 : ℕ) : ℝ))
    rw [Real.exp_log hCpos] at hle
    linarith
  have h13C : (13 : ℝ) * log ((B + 3 : ℕ) : ℝ) <
      ((B + 3 : ℕ) : ℝ) ^ 9 - 1 := by
    have h13self : (13 : ℝ) * log ((B + 3 : ℕ) : ℝ) <
        13 * ((B + 3 : ℕ) : ℝ) :=
      mul_lt_mul_of_pos_left hloglt (by norm_num)
    have hC4 : (4 : ℝ) ≤ ((B + 3 : ℕ) : ℝ) := by
      have : 4 ≤ B + 3 :=
        Nat.add_le_add_right (Nat.succ_le_of_lt hB) 3
      exact_mod_cast this
    have hC8 : (4 : ℝ) ^ 8 ≤ ((B + 3 : ℕ) : ℝ) ^ 8 :=
      pow_le_pow_left (by norm_num) hC4 8
    have h48 : (4 : ℝ) ^ 8 = 65536 := by norm_num
    have hscale :
        (13 : ℝ) * ((B + 3 : ℕ) : ℝ) + 1 ≤
          ((B + 3 : ℕ) : ℝ) ^ 9 := by
      have hpow : ((B + 3 : ℕ) : ℝ) ^ 9 =
          ((B + 3 : ℕ) : ℝ) ^ 8 * ((B + 3 : ℕ) : ℝ) := by
        rw [← pow_succ]
      have hbig : (65536 : ℝ) * ((B + 3 : ℕ) : ℝ) ≤
          ((B + 3 : ℕ) : ℝ) ^ 8 * ((B + 3 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_right (h48 ▸ hC8) (le_of_lt hCpos)
      have hsmall : (13 : ℝ) * ((B + 3 : ℕ) : ℝ) + 1 ≤
          (65536 : ℝ) * ((B + 3 : ℕ) : ℝ) := by
        nlinarith [hCpos]
      exact le_trans hsmall (hpow ▸ hbig)
    linarith [h13self, hscale]
  have hinv :
      1 / (((B + 3 : ℕ) : ℝ) ^ 9 - 1) <
        1 / (13 * log ((B + 3 : ℕ) : ℝ)) :=
    (one_div_lt_one_div h9sub (mul_pos (by norm_num) hlogC)).2 h13C
  exact lt_trans (lt_of_le_of_lt hsand.2.1 hratio) hinv

/-- Track 1 packaged RHS is strictly below the ratio upper bound. -/
theorem track1_exp_lt_ratio
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    exp (-MatveevThm14Proof.C1_floor_real * log (A : ℝ) *
        log ((B + 3 : ℕ) : ℝ) *
        MatveevThm14Proof.B0_term (A : ℝ) ((B + 3 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  have hgt := MatveevThm14Proof.gap3_A_gt_one A B hsol hB
  have hΛ := MatveevThm14Proof.Lambda_gap3_ne_zero A B hsol hB
  have hlower :=
    MatveevThm14Proof.matveev_thm14_n2_explicit_of_nat A (B + 3)
      hgt.1 hgt.2 hΛ
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hupper := matveev_gap3_abs_lambda_le_ratio hpow
  exact lt_of_lt_of_le hlower hupper

theorem abs_sub_int_floor (x : ℝ) : |x - ⌊x⌋| < 1 := by
  have hle : (⌊x⌋ : ℝ) ≤ x := Int.floor_le x
  have hlt : x < ⌊x⌋ + 1 := Int.lt_floor_add_one x
  have hnonneg : 0 ≤ x - ⌊x⌋ := sub_nonneg.mpr hle
  rw [abs_of_nonneg hnonneg]
  linarith

/-- Displayed C=10³⁰ floor form approximates `C Λ` with error `< 17`.
    Not an LLL reduction: Mathlib 4.12 has no shortest-vector theorem. -/
theorem LLL_e2_linear_form_approx (A B : ℕ) :
    |(4 : ℝ) * (LLL_e2 A B).1 - 13 * (LLL_e2 A B).2
      - LLL_C_real * Lambda A B| < 17 := by
  set a : ℝ := LLL_C_real * log (A : ℝ)
  set c : ℝ := LLL_C_real * log ((B + 3 : ℕ) : ℝ)
  have hΛ : LLL_C_real * Lambda A B = 4 * a - 13 * c := by
    simp only [Lambda, a, c]
    ring
  have he2 : LLL_e2 A B = (⌊a⌋, ⌊c⌋) := rfl
  have hform :
      (4 : ℝ) * (LLL_e2 A B).1 - 13 * (LLL_e2 A B).2
        - LLL_C_real * Lambda A B =
      4 * (⌊a⌋ - a) - 13 * (⌊c⌋ - c) := by
    rw [he2, hΛ]
    push_cast
    ring
  have ha : |a - ⌊a⌋| < 1 := abs_sub_int_floor a
  have hc : |c - ⌊c⌋| < 1 := abs_sub_int_floor c
  have hbound :
      |4 * (⌊a⌋ - a) - 13 * (⌊c⌋ - c)| < 17 := by
    have h4 : |(4 : ℝ) * (⌊a⌋ - a)| < 4 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      have : |⌊a⌋ - a| = |a - ⌊a⌋| := abs_sub_comm _ _
      rw [this]
      nlinarith [ha]
    have h13 : |(13 : ℝ) * (⌊c⌋ - c)| < 13 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 13)]
      have : |⌊c⌋ - c| = |c - ⌊c⌋| := abs_sub_comm _ _
      rw [this]
      nlinarith [hc]
    have htri : |4 * (⌊a⌋ - a) - 13 * (⌊c⌋ - c)| ≤
        |4 * (⌊a⌋ - a)| + |13 * (⌊c⌋ - c)| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add ((4 : ℝ) * (⌊a⌋ - a)) (-((13 : ℝ) * (⌊c⌋ - c)))
    linarith [htri, h4, h13]
  rwa [hform]

/-! ## Rank-3 Bugeaud lattice (setup, not a shortest-vector close)

Displayed basis of `L ⊂ ℝ³`:

* `b₁ = (1, 0, ⌊C log A⌋)`
* `b₂ = (0, 1, ⌊C log(B+3)⌋)`
* `b₃ = (0, 0, C)`

`det L = C = 10³⁰`. The integer vector `v = 4 b₁ − 13 b₂` is in
`L`. On a gap-3 solution with `B > 10⁶`, `C|Λ| < 1`, so `‖v‖ < 32`
and `λ₁ ≤ 32`. That does **not** force `|Λ|` above `B⁴/A⁴`:
Minkowski bounds `λ₁` from above, and a lower bound on `|Λ|` from
`‖b₁*‖` is Baker–Davenport / LLL, not in Mathlib 4.12.
-/

theorem LLL_C_real_eq : LLL_C_real = (10 : ℝ) ^ 30 := by
  unfold LLL_C_real LLL_C_nat
  norm_num

theorem LLL_C_real_pos : (0 : ℝ) < LLL_C_real := by
  rw [LLL_C_real_eq]
  positivity

def LLL_b1 (A : ℕ) : Fin 3 → ℝ := fun i =>
  if i = 0 then (1 : ℝ)
  else if i = 1 then 0
  else (⌊LLL_C_real * log (A : ℝ)⌋ : ℝ)

def LLL_b2 (B : ℕ) : Fin 3 → ℝ := fun i =>
  if i = 0 then (0 : ℝ)
  else if i = 1 then 1
  else (⌊LLL_C_real * log ((B + 3 : ℕ) : ℝ)⌋ : ℝ)

def LLL_b3 : Fin 3 → ℝ := fun i =>
  if i = 2 then LLL_C_real else 0

theorem LLL_b1_zero (A : ℕ) : LLL_b1 A 0 = 1 := by simp [LLL_b1]
theorem LLL_b1_one (A : ℕ) : LLL_b1 A 1 = 0 := by simp [LLL_b1]
theorem LLL_b1_two (A : ℕ) :
    LLL_b1 A 2 = (⌊LLL_C_real * log (A : ℝ)⌋ : ℝ) := by
  simp [LLL_b1]

theorem LLL_b2_zero (B : ℕ) : LLL_b2 B 0 = 0 := by simp [LLL_b2]
theorem LLL_b2_one (B : ℕ) : LLL_b2 B 1 = 1 := by simp [LLL_b2]
theorem LLL_b2_two (B : ℕ) :
    LLL_b2 B 2 = (⌊LLL_C_real * log ((B + 3 : ℕ) : ℝ)⌋ : ℝ) := by
  simp [LLL_b2]

theorem LLL_b3_zero : LLL_b3 0 = 0 := by simp [LLL_b3]
theorem LLL_b3_one : LLL_b3 1 = 0 := by simp [LLL_b3]
theorem LLL_b3_two : LLL_b3 2 = LLL_C_real := by simp [LLL_b3]

/-- Columns are `b₁, b₂, b₃`. -/
def LLL_basisMatrix (A B : ℕ) : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
  if i = 0 ∧ j = 0 then 1
  else if i = 1 ∧ j = 1 then 1
  else if i = 2 ∧ j = 0 then LLL_b1 A 2
  else if i = 2 ∧ j = 1 then LLL_b2 B 2
  else if i = 2 ∧ j = 2 then LLL_C_real
  else 0

theorem LLL_basis_det (A B : ℕ) :
    (LLL_basisMatrix A B).det = LLL_C_real := by
  rw [Matrix.det_fin_three]
  simp [LLL_basisMatrix, LLL_b1_two, LLL_b2_two]

def lllInner (u v : Fin 3 → ℝ) : ℝ := ∑ i : Fin 3, u i * v i
def lllNormSq (v : Fin 3 → ℝ) : ℝ := lllInner v v
noncomputable def lllNorm (v : Fin 3 → ℝ) : ℝ := Real.sqrt (lllNormSq v)

theorem lllNormSq_eq (v : Fin 3 → ℝ) :
    lllNormSq v = v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2 := by
  unfold lllNormSq lllInner
  rw [Fin.sum_univ_three]
  ring

theorem lllNorm_nonneg (v : Fin 3 → ℝ) : 0 ≤ lllNorm v :=
  Real.sqrt_nonneg _

def LLL_span (A B : ℕ) (x y z : ℤ) : Fin 3 → ℝ :=
  fun i =>
    (x : ℝ) * LLL_b1 A i + (y : ℝ) * LLL_b2 B i + (z : ℝ) * LLL_b3 i

def mem_LLL_lattice (A B : ℕ) (v : Fin 3 → ℝ) : Prop :=
  ∃ x y z : ℤ, v = LLL_span A B x y z

/-- Explicit short vector `v = 4 b₁ − 13 b₂`. -/
def LLL_v (A B : ℕ) : Fin 3 → ℝ := LLL_span A B 4 (-13) 0

theorem LLL_v_mem (A B : ℕ) : mem_LLL_lattice A B (LLL_v A B) :=
  ⟨4, -13, 0, rfl⟩

theorem LLL_v_zero (A B : ℕ) : LLL_v A B 0 = 4 := by
  simp [LLL_v, LLL_span, LLL_b1_zero, LLL_b2_zero, LLL_b3_zero]

theorem LLL_v_one (A B : ℕ) : LLL_v A B 1 = -13 := by
  simp [LLL_v, LLL_span, LLL_b1_one, LLL_b2_one, LLL_b3_one]

theorem LLL_v_two (A B : ℕ) :
    LLL_v A B 2 = (4 : ℝ) * (LLL_e2 A B).1 - 13 * (LLL_e2 A B).2 := by
  simp [LLL_v, LLL_span, LLL_b1_two, LLL_b2_two, LLL_b3_two, LLL_e2]
  ring

theorem LLL_v_ne_zero (A B : ℕ) : LLL_v A B ≠ 0 := by
  intro h
  have := congrArg (fun v : Fin 3 → ℝ => v 0) h
  simp [LLL_v_zero] at this

theorem LLL_v_normSq (A B : ℕ) :
    lllNormSq (LLL_v A B) = 185 + LLL_v A B 2 ^ 2 := by
  rw [lllNormSq_eq, LLL_v_zero, LLL_v_one]
  ring

theorem LLL_v_third_approx (A B : ℕ) :
    |LLL_v A B 2 - LLL_C_real * Lambda A B| < 17 := by
  rw [LLL_v_two]
  exact LLL_e2_linear_form_approx A B

/-- Rearrangement of the floor error: if the third coordinate is
    larger than 17, `|Λ| ≥ (|third| − 17)/C`. Not a `B ≤ 10⁶` cutoff. -/
theorem abs_Lambda_ge_of_third_gt_seventeen
    (A B : ℕ)
    (_h : 17 < |(4 : ℝ) * (LLL_e2 A B).1 - 13 * (LLL_e2 A B).2|) :
    (|(4 : ℝ) * (LLL_e2 A B).1 - 13 * (LLL_e2 A B).2| - 17) / LLL_C_real ≤
      |Lambda A B| := by
  have happ := LLL_e2_linear_form_approx A B
  have hC := LLL_C_real_pos
  have htri : |LLL_C_real * Lambda A B| ≥
      |(4 : ℝ) * (LLL_e2 A B).1 - 13 * (LLL_e2 A B).2| - 17 := by
    have := abs_sub_abs_le_abs_sub
      ((4 : ℝ) * (LLL_e2 A B).1 - 13 * (LLL_e2 A B).2)
      (LLL_C_real * Lambda A B)
    linarith [happ, this]
  have hmul : |LLL_C_real * Lambda A B| = LLL_C_real * |Lambda A B| := by
    rw [abs_mul, abs_of_pos hC]
  rw [hmul] at htri
  rw [div_le_iff₀ hC]
  linarith [htri]

def LLL_nonzero_norms (A B : ℕ) : Set ℝ :=
  { r | ∃ v, mem_LLL_lattice A B v ∧ v ≠ 0 ∧ r = lllNorm v }

noncomputable def LLL_lambda1 (A B : ℕ) : ℝ := sInf (LLL_nonzero_norms A B)

theorem LLL_nonzero_norms_bddBelow (A B : ℕ) :
    BddBelow (LLL_nonzero_norms A B) :=
  ⟨0, by
    intro r ⟨v, _, _, heq⟩
    rw [heq]
    exact lllNorm_nonneg v⟩

theorem LLL_v_mem_norms (A B : ℕ) :
    lllNorm (LLL_v A B) ∈ LLL_nonzero_norms A B :=
  ⟨LLL_v A B, LLL_v_mem A B, LLL_v_ne_zero A B, rfl⟩

theorem LLL_lambda1_le_v_norm (A B : ℕ) :
    LLL_lambda1 A B ≤ lllNorm (LLL_v A B) :=
  csInf_le (LLL_nonzero_norms_bddBelow A B) (LLL_v_mem_norms A B)

/-- Gram–Schmidt: `b₁* = b₁`. -/
def LLL_b1star (A : ℕ) : Fin 3 → ℝ := LLL_b1 A

def LLL_mu21 (A B : ℕ) : ℝ :=
  lllInner (LLL_b2 B) (LLL_b1star A) / lllNormSq (LLL_b1star A)

def LLL_b2star (A B : ℕ) : Fin 3 → ℝ :=
  fun i => LLL_b2 B i - LLL_mu21 A B * LLL_b1star A i

def LLL_mu31 (A : ℕ) (_B : ℕ) : ℝ :=
  lllInner LLL_b3 (LLL_b1star A) / lllNormSq (LLL_b1star A)

def LLL_mu32 (A B : ℕ) : ℝ :=
  lllInner LLL_b3 (LLL_b2star A B) / lllNormSq (LLL_b2star A B)

def LLL_b3star (A B : ℕ) : Fin 3 → ℝ :=
  fun i =>
    LLL_b3 i - LLL_mu31 A B * LLL_b1star A i
      - LLL_mu32 A B * LLL_b2star A B i

theorem LLL_b1_normSq_ge_one (A : ℕ) :
    (1 : ℝ) ≤ lllNormSq (LLL_b1 A) := by
  rw [lllNormSq_eq, LLL_b1_zero, LLL_b1_one]
  nlinarith [sq_nonneg (LLL_b1 A 2)]

/-- Size-reduction inequalities on a 3-basis. The *displayed*
    basis is not claimed to satisfy them. -/
def LLL_size_reduced (μ21 μ31 μ32 : ℝ) : Prop :=
  |μ21| ≤ 1 / 2 ∧ |μ31| ≤ 1 / 2 ∧ |μ32| ≤ 1 / 2

/-- Lovász inequalities (`δ = 3/4`). -/
def LLL_lovasz (b1star b2star b3star : Fin 3 → ℝ) (μ21 μ32 : ℝ) : Prop :=
  (3 / 4 : ℝ) * lllNormSq b1star ≤
      lllNormSq (fun i => b2star i + μ21 * b1star i) ∧
    (3 / 4 : ℝ) * lllNormSq b2star ≤
      lllNormSq (fun i => b3star i + μ32 * b2star i)

def LLL_reduced (b1star b2star b3star : Fin 3 → ℝ)
    (μ21 μ31 μ32 : ℝ) : Prop :=
  LLL_size_reduced μ21 μ31 μ32 ∧ LLL_lovasz b1star b2star b3star μ21 μ32

/-- LLL potential `D = ∏ᵢ ‖bᵢ*‖^{2(n−i+1)}` for `n = 3`, written
    in squared norms: `‖b₁*‖⁶ ‖b₂*‖⁴ ‖b₃*‖²`. Termination (a
    swap drops `D` by a factor `< 3/4`) stays `def Prop`. -/
def lllPotential (b1star b2star b3star : Fin 3 → ℝ) : ℝ :=
  lllNormSq b1star ^ 3 * lllNormSq b2star ^ 2 * lllNormSq b3star

/-- LLL terminates on a rank-3 lattice (potential
    `D = ∏ ‖bᵢ*‖^{2(n−i+1)}` drops on a swap). Not in Mathlib 4.12. -/
def lll_algorithm_terminates : Prop :=
  ∀ A B : ℕ,
    ∃ b1' b2' b3' : Fin 3 → ℝ,
      mem_LLL_lattice A B b1' ∧ mem_LLL_lattice A B b2' ∧
        mem_LLL_lattice A B b3' ∧
          LLL_reduced b1' b2' b3'
            (lllInner b2' b1' / lllNormSq b1')
            (lllInner b3' b1' / lllNormSq b1')
            (lllInner b3' b2' / lllNormSq b2')

/-- LLL reduced ⇒ `‖b₁‖ ≤ 2 λ₁` (`n = 3`). Not in Mathlib 4.12. -/
def lll_svt_bound : Prop :=
  ∀ (A B : ℕ) (b1' : Fin 3 → ℝ),
    mem_LLL_lattice A B b1' →
      lllNorm b1' ≤ 2 * LLL_lambda1 A B

/-- LLL reduced ⇒ `‖b₁‖ ≤ √2 · C^{1/3}`. Not in Mathlib 4.12.
    For `C = 10³⁰` this is `≈ 2.8e10`, much larger than `‖v‖ < 32`. -/
def lll_det_bound : Prop :=
  ∀ (A B : ℕ) (b1' : Fin 3 → ℝ),
    mem_LLL_lattice A B b1' →
      lllNorm b1' ≤ Real.sqrt 2 * LLL_C_real ^ ((1 : ℝ) / 3)

/-- Baker–Davenport from a large first GS vector. Circular without
    an independent estimate of `‖b₁*‖`. Not in Mathlib 4.12. -/
def baker_davenport_gs_lower : Prop :=
  ∀ A B : ℕ,
    1 < A →
      1 < B + 3 →
        (lllNorm (LLL_b1star A) - 17) / LLL_C_real ≤ |Lambda A B|

theorem B3_ge_of_B_gt_B0 {B : ℕ} (hB0 : B0_nat < B) :
    (1000004 : ℕ) ≤ B + 3 := by
  have hB : 1000001 ≤ B := by
    have : B0_nat + 1 ≤ B := Nat.succ_le_of_lt hB0
    simpa [B0_nat] using this
  omega

theorem C_mul_ratio_lt_one_of_B_gt_B0
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B) :
    LLL_C_real * ((B : ℝ) ^ 4 / (A : ℝ) ^ 4) < 1 := by
  have hratio := ratio_lt_inv_B3_pow_nine hsol hB
  have h9sub : (0 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 9 - 1 := by
    have hgt := MatveevThm14Proof.gap3_A_gt_one A B hsol hB
    have hC1 : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) := by exact_mod_cast hgt.2
    have h9 : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) ^ 9 :=
      one_lt_pow hC1 (by decide : (9 : ℕ) ≠ 0)
    linarith
  have hB3 : (1000004 : ℕ) ≤ B + 3 := B3_ge_of_B_gt_B0 hB0
  have hbase : (10 : ℕ) ^ 6 ≤ B + 3 := by
    have : (10 : ℕ) ^ 6 = 1000000 := by decide
    have : (1000000 : ℕ) ≤ 1000004 := by decide
    exact le_trans (by decide : (10 : ℕ) ^ 6 ≤ 1000004) hB3
  have hpow : ((10 : ℕ) ^ 6) ^ 9 ≤ (B + 3) ^ 9 :=
    Nat.pow_le_pow_left hbase 9
  have h54 : ((10 : ℕ) ^ 6) ^ 9 = (10 : ℕ) ^ 54 := by
    rw [← Nat.pow_mul]
  have hreal :
      LLL_C_real + 1 < ((B + 3 : ℕ) : ℝ) ^ 9 := by
    have hle : ((10 : ℕ) ^ 54 : ℝ) ≤ ((B + 3 : ℕ) : ℝ) ^ 9 := by
      exact_mod_cast (h54 ▸ hpow)
    have hC : LLL_C_real + 1 < ((10 : ℕ) ^ 54 : ℝ) := by
      rw [LLL_C_real_eq]
      have : ((10 : ℕ) ^ 54 : ℝ) = (10 : ℝ) ^ 54 := by
        norm_cast
      rw [this]
      norm_num
    exact lt_of_lt_of_le hC hle
  have hden : LLL_C_real < ((B + 3 : ℕ) : ℝ) ^ 9 - 1 := by linarith
  have hquot : LLL_C_real / (((B + 3 : ℕ) : ℝ) ^ 9 - 1) < 1 :=
    (div_lt_one h9sub).2 hden
  have : LLL_C_real * ((B : ℝ) ^ 4 / (A : ℝ) ^ 4) <
      LLL_C_real / (((B + 3 : ℕ) : ℝ) ^ 9 - 1) := by
    have hC := LLL_C_real_pos
    have := mul_lt_mul_of_pos_left hratio hC
    rwa [mul_one_div] at this
  exact lt_trans this hquot

theorem LLL_v_third_abs_lt_eighteen
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B) :
    |LLL_v A B 2| < 18 := by
  have happ := LLL_v_third_approx A B
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  have hle := matveev_gap3_abs_lambda_le_ratio hpow
  have hΛ : |Lambda A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
    rw [Lambda_eq_matveev_log_form]
    exact hle
  have hCΛ : LLL_C_real * |Lambda A B| < 1 := by
    have := mul_le_mul_of_nonneg_left hΛ (le_of_lt LLL_C_real_pos)
    exact lt_of_le_of_lt this (C_mul_ratio_lt_one_of_B_gt_B0 hsol hB hB0)
  have hmul : |LLL_C_real * Lambda A B| = LLL_C_real * |Lambda A B| := by
    rw [abs_mul, abs_of_pos LLL_C_real_pos]
  have : |LLL_v A B 2| < 17 + LLL_C_real * |Lambda A B| := by
    have htri : |LLL_v A B 2| ≤
        |LLL_v A B 2 - LLL_C_real * Lambda A B| +
          |LLL_C_real * Lambda A B| := by
      simpa [sub_eq_add_neg] using
        abs_add (LLL_v A B 2 - LLL_C_real * Lambda A B)
          (LLL_C_real * Lambda A B)
    linarith [happ, htri, hmul]
  linarith [hCΛ]

/-- On a solution with `B > 10⁶`, the tight ratio (not `1/B`)
    makes `C|Λ| < 1`, so `‖v‖ < 32`. Using `|Λ| < 1/B` would give
    `C|Λ| < 10^{24}`, which does not bound `‖v‖`. -/
theorem LLL_v_norm_lt_thirty_two
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B) :
    lllNorm (LLL_v A B) < 32 := by
  have ht := LLL_v_third_abs_lt_eighteen hsol hB hB0
  have hsq : lllNormSq (LLL_v A B) = 185 + LLL_v A B 2 ^ 2 :=
    LLL_v_normSq A B
  have hx : (0 : ℝ) ≤ 185 := by norm_num
  have h185 : Real.sqrt 185 < 14 := by
    exact (Real.sqrt_lt (by norm_num : (0 : ℝ) ≤ 185)
      (by norm_num : (0 : ℝ) ≤ 14)).mpr (by
      rw [show (14 : ℝ) ^ 2 = 196 by norm_num]
      norm_num)
  have hsum : (0 : ℝ) ≤ Real.sqrt 185 + |LLL_v A B 2| :=
    add_nonneg (Real.sqrt_nonneg _) (abs_nonneg _)
  have hsqle : lllNormSq (LLL_v A B) ≤
      (Real.sqrt 185 + |LLL_v A B 2|) ^ 2 := by
    rw [hsq, add_sq, Real.sq_sqrt hx, sq_abs]
    nlinarith [Real.sqrt_nonneg (185 : ℝ), abs_nonneg (LLL_v A B 2)]
  have : lllNorm (LLL_v A B) ≤ Real.sqrt 185 + |LLL_v A B 2| := by
    unfold lllNorm
    exact (Real.sqrt_le_left hsum).2 hsqle
  linarith [this, h185, ht]

theorem LLL_lambda1_lt_thirty_two
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B) :
    LLL_lambda1 A B < 32 :=
  lt_of_le_of_lt (LLL_lambda1_le_v_norm A B)
    (LLL_v_norm_lt_thirty_two hsol hB hB0)

/-- Baker–Davenport / Bugeaud LLL reduction from `|Λ| ≤ B⁴/A⁴`
    down to `B ≤ B0_nat`. Mathlib 4.12 has no such theorem.
    Same type as `baker_bound_gap3_from_ratio`; still uninhabited.
    The proved lattice facts are `LLL_basis_det`, `LLL_v_mem`, and
    `LLL_v_norm_lt_thirty_two`, not this. -/
def baker_davenport_reduction : Prop := baker_bound_gap3_from_ratio

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
#check abs_Lambda_ge_B4_div_B3_pow
#check abs_Lambda_tight_sandwich
#check A_pow_gt_B_pow_five
#check ratio_lt_inv_B
#check abs_Lambda_le_inv_B
#check abs_Lambda_le_inv_B_of_B_gt_B0
#check inv_B3_pow_lt_inv_B
#check elementary_inv_max_compatible_with_inv_B
#check abs_Lambda_lt_inv_max_log_coeff
#check track1_exp_lt_ratio
#check LLL_e2_linear_form_approx
#check LLL_basis_det
#check LLL_v_mem
#check LLL_v_norm_lt_thirty_two
#check LLL_lambda1_lt_thirty_two
#check abs_Lambda_ge_of_third_gt_seventeen
#check LLL_reduced
#check lllPotential
#check lll_algorithm_terminates
#check lll_svt_bound
#check lll_det_bound
#check baker_davenport_gs_lower
#check baker_davenport_reduction
#check baker_bound_gap3_of_from_ratio
#print axioms four_thirteenths_is_convergent
#print axioms integer_gap_lt_ratio
#print axioms abs_Lambda_tight_sandwich
#print axioms abs_Lambda_le_inv_B
#print axioms abs_Lambda_lt_inv_max_log_coeff
#print axioms track1_exp_lt_ratio
#print axioms LLL_e2_linear_form_approx
#print axioms LLL_basis_det
#print axioms LLL_v_norm_lt_thirty_two
#print axioms LLL_lambda1_lt_thirty_two
#print axioms baker_bound_gap3_of_from_ratio

end BealMatveevBeal.MatveevLLL
