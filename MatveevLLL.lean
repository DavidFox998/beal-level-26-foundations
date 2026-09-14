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

Gram–Schmidt orthogonality, Lovász `‖bᵢ*‖² ≥ (1/2) ‖bᵢ₋₁*‖²`,
the swap factor `D ↦ (L/‖b₁*‖²) D < (3/4) D`, integer
`‖b₁‖²`, nearest-integer size-reduction, and the *conditional*
SVT `‖b₁‖ ≤ 2 λ₁` for an LLL-reduced Z-basis are theorems.
`lll_algorithm_terminates` is the existence of an LLL-reduced
Z-basis of the displayed rank-3 lattice: size-reduction is
finite, each Lovász-failing swap drops the integer potential
`D = d₁ d₂ d₃` by a factor `< 3/4`, and `D ∈ ℕ≥1` is bounded
below, so only finitely many swaps occur.
Existence of a reduced basis does **not** give `B ≤ 10⁶`.
A reduced first vector satisfies `‖b₁‖ ≤ 2 λ₁ < 64`, which
makes `‖b₁*‖` *small*, the opposite of the large `r` that
`baker_davenport_gs_lower` would need. Displayed
`lll_svt_bound` (`‖b₁‖ ≤ 2^{(n-1)/2} λ₁ = 2 λ₁` for `n = 3`,
via `lll_gs_lower_half_pow` and
`lll_reduced_first_vec_le_lattice_vec`) and `lll_det_bound`
(`‖b₁‖ ≤ 2^{(n-1)/4} det^{1/n} = √2 · C^{1/3} ≈ 2.8e10`)
are theorems; both are *upper* bounds on a short first vector
and do **not** give `B ≤ 10⁶`.
`baker_davenport_gs_lower` is the rearrangement
`r ≤ |v₃|` and `17 < r` ⇒ `|Λ| ≥ (r−17)/C`;
`baker_davenport_no_cutoff` records that on `B > 10⁶`
one has `|v₃| < 18`, so `r ∈ (17, 18)` and
`(r−17)/C < 10⁻³⁰ < 10⁻⁶ = 1/B0`, compatible with
`|Λ| < 1/B`.
`|Λ| < 1/B` is too weak to make `C|Λ|` small (`C/B = 10^{24}`);
the `‖v‖ < 32` estimate uses `B⁴/A⁴ < 1/((B+3)⁹−1)`, not `1/B`.
A genuine `B ≤ 10⁶` cutoff would need a lower bound on `|Λ|`
stronger than `B⁴/A⁴`. That is circular without an external
reduced-basis length estimate. Not v25.

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
    in squared norms: `‖b₁*‖⁶ ‖b₂*‖⁴ ‖b₃*‖²`. -/
def lllPotential (b1star b2star b3star : Fin 3 → ℝ) : ℝ :=
  lllNormSq b1star ^ 3 * lllNormSq b2star ^ 2 * lllNormSq b3star

theorem lllInner_comm (u v : Fin 3 → ℝ) :
    lllInner u v = lllInner v u := by
  unfold lllInner
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem lllInner_add (u v w : Fin 3 → ℝ) :
    lllInner (fun i => u i + v i) w = lllInner u w + lllInner v w := by
  unfold lllInner
  simp only [add_mul]
  exact Finset.sum_add_distrib

theorem lllInner_add_right (u v w : Fin 3 → ℝ) :
    lllInner u (fun i => v i + w i) = lllInner u v + lllInner u w := by
  unfold lllInner
  simp only [mul_add]
  exact Finset.sum_add_distrib

theorem lllInner_smul (a : ℝ) (u v : Fin 3 → ℝ) :
    lllInner (fun i => a * u i) v = a * lllInner u v := by
  unfold lllInner
  have : ∑ i : Fin 3, a * u i * v i = ∑ i : Fin 3, a * (u i * v i) := by
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [this, ← Finset.mul_sum]

theorem lllInner_smul_right (a : ℝ) (u v : Fin 3 → ℝ) :
    lllInner u (fun i => a * v i) = a * lllInner u v := by
  rw [lllInner_comm, lllInner_smul, lllInner_comm]

theorem lllNormSq_nonneg (v : Fin 3 → ℝ) : 0 ≤ lllNormSq v := by
  rw [lllNormSq_eq]
  nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]

theorem lllNormSq_add_smul_of_orth
    {u v : Fin 3 → ℝ} {a : ℝ} (h : lllInner u v = 0) :
    lllNormSq (fun i => u i + a * v i) =
      lllNormSq u + a ^ 2 * lllNormSq v := by
  have hinn : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0 := by
    have : lllInner u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
      unfold lllInner
      rw [Fin.sum_univ_three]
    rwa [← this]
  rw [lllNormSq_eq, lllNormSq_eq, lllNormSq_eq]
  have hexpand :
      (u 0 + a * v 0) ^ 2 + (u 1 + a * v 1) ^ 2 + (u 2 + a * v 2) ^ 2 =
        (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) +
          a ^ 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) +
            2 * a * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) := by
    ring
  rw [hexpand, hinn]
  ring

/-- Size-reduction plus Lovász and GS orthogonality give
    `‖bᵢ*‖² ≥ (1/2) ‖bᵢ₋₁*‖²`. -/
theorem lll_lovasz_size_half
    {b1star b2star : Fin 3 → ℝ} {μ : ℝ}
    (horth : lllInner b2star b1star = 0)
    (hμ : |μ| ≤ 1 / 2)
    (hlov : (3 / 4 : ℝ) * lllNormSq b1star ≤
        lllNormSq (fun i => b2star i + μ * b1star i)) :
    (1 / 2 : ℝ) * lllNormSq b1star ≤ lllNormSq b2star := by
  have hpy : lllNormSq (fun i => b2star i + μ * b1star i) =
      lllNormSq b2star + μ ^ 2 * lllNormSq b1star :=
    lllNormSq_add_smul_of_orth horth
  have hμsq : μ ^ 2 ≤ (1 / 4 : ℝ) := by
    have habs := abs_le.mp hμ
    nlinarith
  have hN1 := lllNormSq_nonneg b1star
  rw [hpy] at hlov
  nlinarith [hμsq, hN1]

theorem lll_reduced_gs_half
    {b1star b2star b3star : Fin 3 → ℝ} {μ21 μ31 μ32 : ℝ}
    (h12 : lllInner b2star b1star = 0)
    (h23 : lllInner b3star b2star = 0)
    (hred : LLL_reduced b1star b2star b3star μ21 μ31 μ32) :
    (1 / 2 : ℝ) * lllNormSq b1star ≤ lllNormSq b2star ∧
      (1 / 2 : ℝ) * lllNormSq b2star ≤ lllNormSq b3star := by
  obtain ⟨hsize, hlov⟩ := hred
  refine ⟨lll_lovasz_size_half h12 hsize.1 hlov.1,
    lll_lovasz_size_half h23 hsize.2.2 hlov.2⟩

/-- LLL-reduced ⇒ `‖bⱼ*‖² ≥ (1/2)^{j−i} ‖bᵢ*‖²` (`n = 3`):
    consecutive factors `1/2`, and `‖b₃*‖² ≥ (1/4) ‖b₁*‖²`. -/
theorem lll_gs_lower_half_pow
    {b1star b2star b3star : Fin 3 → ℝ} {μ21 μ31 μ32 : ℝ}
    (h12 : lllInner b2star b1star = 0)
    (h23 : lllInner b3star b2star = 0)
    (hred : LLL_reduced b1star b2star b3star μ21 μ31 μ32) :
    (1 / 2 : ℝ) * lllNormSq b1star ≤ lllNormSq b2star ∧
      (1 / 2 : ℝ) * lllNormSq b2star ≤ lllNormSq b3star ∧
        (1 / 4 : ℝ) * lllNormSq b1star ≤ lllNormSq b3star := by
  have h := lll_reduced_gs_half h12 h23 hred
  refine ⟨h.1, h.2, ?_⟩
  nlinarith [h.1, h.2, lllNormSq_nonneg b2star]

/-- On a 1–2 swap the new first squared length is
    `L = ‖b₂* + μ b₁*‖²`, and `D` scales by `L / ‖b₁*‖²`.
    If Lovász fails then this factor is `< 3/4`. -/
theorem lllPotential_swap12_mul
    (b1star b2star b3star : Fin 3 → ℝ) (μ : ℝ)
    (hN1 : lllNormSq b1star ≠ 0)
    (hL : lllNormSq (fun i => b2star i + μ * b1star i) ≠ 0) :
    let L := lllNormSq (fun i => b2star i + μ * b1star i)
    L ^ 3 * (lllNormSq b1star * lllNormSq b2star / L) ^ 2 *
        lllNormSq b3star =
      (L / lllNormSq b1star) * lllPotential b1star b2star b3star := by
  intro L
  unfold lllPotential
  field_simp [hN1, hL]
  ring

theorem lllPotential_swap12_factor_lt
    (b1star b2star b3star : Fin 3 → ℝ) (μ : ℝ)
    (hN1 : 0 < lllNormSq b1star)
    (hD : 0 < lllPotential b1star b2star b3star)
    (hfail : lllNormSq (fun i => b2star i + μ * b1star i) <
        (3 / 4 : ℝ) * lllNormSq b1star) :
    (lllNormSq (fun i => b2star i + μ * b1star i) / lllNormSq b1star) *
        lllPotential b1star b2star b3star <
      (3 / 4 : ℝ) * lllPotential b1star b2star b3star := by
  have hfrac :
      lllNormSq (fun i => b2star i + μ * b1star i) / lllNormSq b1star <
        (3 / 4 : ℝ) :=
    (div_lt_iff hN1).mpr hfail
  exact mul_lt_mul_of_pos_right hfrac hD

/-- Displayed `‖b₁‖² = 1 + ⌊C log A⌋²` is an integer
    (so the first Gram factor of `D` is integer-valued). -/
theorem LLL_b1_normSq_int (A : ℕ) :
    ∃ z : ℤ, (z : ℝ) = lllNormSq (LLL_b1 A) := by
  refine ⟨1 + ⌊LLL_C_real * log (A : ℝ)⌋ ^ 2, ?_⟩
  rw [lllNormSq_eq, LLL_b1_zero, LLL_b1_one, LLL_b1_two]
  push_cast
  ring

theorem LLL_b1_normSq_nat (A : ℕ) :
    ∃ n : ℕ, (n : ℝ) = lllNormSq (LLL_b1 A) := by
  obtain ⟨z, hz⟩ := LLL_b1_normSq_int A
  have hz0 : 0 ≤ z := by
    have : (0 : ℝ) ≤ z := by
      rw [hz]
      exact lllNormSq_nonneg (LLL_b1 A)
    exact Int.cast_nonneg.mp this
  refine ⟨z.toNat, ?_⟩
  have hzZ : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz0
  have : (z.toNat : ℝ) = (z : ℝ) := by
    rw [← hzZ]
    exact_mod_cast rfl
  rwa [this]

/-- Nearest-integer rounding: size-reduction step. -/
def lllNearestInt (x : ℝ) : ℤ := ⌊x + 1 / 2⌋

theorem abs_sub_lllNearestInt (x : ℝ) :
    |x - (lllNearestInt x : ℝ)| ≤ 1 / 2 := by
  have hle : (lllNearestInt x : ℝ) ≤ x + 1 / 2 := Int.floor_le (x + 1 / 2)
  have hlt : x + 1 / 2 < (lllNearestInt x : ℝ) + 1 :=
    Int.lt_floor_add_one (x + 1 / 2)
  have hlo : (lllNearestInt x : ℝ) - 1 / 2 ≤ x := by linarith
  have hhi : x < (lllNearestInt x : ℝ) + 1 / 2 := by linarith
  cases le_or_lt (x - lllNearestInt x) 0 with
  | inl hnonpos =>
    rw [abs_of_nonpos hnonpos]
    linarith [hlo]
  | inr hpos =>
    rw [abs_of_pos hpos]
    linarith [hhi]

def lllZspan (b1 b2 b3 : Fin 3 → ℝ) (x y z : ℤ) : Fin 3 → ℝ :=
  fun i => (x : ℝ) * b1 i + (y : ℝ) * b2 i + (z : ℝ) * b3 i

theorem lllZspan_eq_gs
    {b1s b2s b3s : Fin 3 → ℝ} {μ21 μ31 μ32 : ℝ} {x y z : ℤ}
    {b1 b2 b3 : Fin 3 → ℝ}
    (hb1 : b1 = b1s)
    (hb2 : b2 = fun i => b2s i + μ21 * b1s i)
    (hb3 : b3 = fun i => b3s i + μ31 * b1s i + μ32 * b2s i) :
    lllZspan b1 b2 b3 x y z =
      fun i =>
        ((x : ℝ) + (y : ℝ) * μ21 + (z : ℝ) * μ31) * b1s i +
          ((y : ℝ) + (z : ℝ) * μ32) * b2s i +
            (z : ℝ) * b3s i := by
  ext i
  simp [lllZspan, hb1, hb2, hb3]
  ring

theorem lllNormSq_linear_orth3
    {u v w : Fin 3 → ℝ} {a b c : ℝ}
    (huv : lllInner u v = 0) (huw : lllInner u w = 0)
    (hvw : lllInner v w = 0) :
    lllNormSq (fun i => a * u i + b * v i + c * w i) =
      a ^ 2 * lllNormSq u + b ^ 2 * lllNormSq v + c ^ 2 * lllNormSq w := by
  have huv' : u 0 * v 0 + u 1 * v 1 + u 2 * v 2 = 0 := by
    have : lllInner u v = u 0 * v 0 + u 1 * v 1 + u 2 * v 2 := by
      unfold lllInner; rw [Fin.sum_univ_three]
    rwa [← this]
  have huw' : u 0 * w 0 + u 1 * w 1 + u 2 * w 2 = 0 := by
    have : lllInner u w = u 0 * w 0 + u 1 * w 1 + u 2 * w 2 := by
      unfold lllInner; rw [Fin.sum_univ_three]
    rwa [← this]
  have hvw' : v 0 * w 0 + v 1 * w 1 + v 2 * w 2 = 0 := by
    have : lllInner v w = v 0 * w 0 + v 1 * w 1 + v 2 * w 2 := by
      unfold lllInner; rw [Fin.sum_univ_three]
    rwa [← this]
  rw [lllNormSq_eq, lllNormSq_eq, lllNormSq_eq, lllNormSq_eq]
  have hexpand :
      (a * u 0 + b * v 0 + c * w 0) ^ 2 +
          (a * u 1 + b * v 1 + c * w 1) ^ 2 +
            (a * u 2 + b * v 2 + c * w 2) ^ 2 =
        a ^ 2 * (u 0 ^ 2 + u 1 ^ 2 + u 2 ^ 2) +
          b ^ 2 * (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) +
            c ^ 2 * (w 0 ^ 2 + w 1 ^ 2 + w 2 ^ 2) +
              2 * a * b * (u 0 * v 0 + u 1 * v 1 + u 2 * v 2) +
                2 * a * c * (u 0 * w 0 + u 1 * w 1 + u 2 * w 2) +
                  2 * b * c * (v 0 * w 0 + v 1 * w 1 + v 2 * w 2) := by
    ring
  rw [hexpand, huv', huw', hvw']
  ring

/-- GS reconstruction: `‖bⱼ‖² ≥ ‖bⱼ*‖²`. -/
theorem lll_vec_normSq_ge_star
    {b1s b2s b3s : Fin 3 → ℝ} {μ21 μ31 μ32 : ℝ}
    {b1 b2 b3 : Fin 3 → ℝ}
    (hb1 : b1 = b1s)
    (hb2 : b2 = fun i => b2s i + μ21 * b1s i)
    (hb3 : b3 = fun i => b3s i + μ31 * b1s i + μ32 * b2s i)
    (h12 : lllInner b1s b2s = 0)
    (h13 : lllInner b1s b3s = 0)
    (h23 : lllInner b2s b3s = 0) :
    lllNormSq b1s ≤ lllNormSq b1 ∧
      lllNormSq b2s ≤ lllNormSq b2 ∧
        lllNormSq b3s ≤ lllNormSq b3 := by
  have h1 : lllNormSq b1s ≤ lllNormSq b1 := by rw [hb1]
  have h2 : lllNormSq b2 =
      lllNormSq b2s + μ21 ^ 2 * lllNormSq b1s := by
    have : lllNormSq b2 =
        lllNormSq (fun i => b2s i + μ21 * b1s i) := by rw [hb2]
    rw [this, lllNormSq_add_smul_of_orth
      (by rwa [lllInner_comm] : lllInner b2s b1s = 0)]
  have h3 : lllNormSq b3 =
      lllNormSq b1s * μ31 ^ 2 + lllNormSq b2s * μ32 ^ 2 +
        lllNormSq b3s := by
    have : lllNormSq b3 =
        lllNormSq (fun i =>
          μ31 * b1s i + μ32 * b2s i + (1 : ℝ) * b3s i) := by
      rw [hb3]
      congr
      ext i
      ring
    rw [this, lllNormSq_linear_orth3 h12 h13 h23]
    ring
  refine ⟨h1, ?_, ?_⟩
  · nlinarith [h2, sq_nonneg μ21, lllNormSq_nonneg b1s]
  · nlinarith [h3, sq_nonneg μ31, sq_nonneg μ32,
      lllNormSq_nonneg b1s, lllNormSq_nonneg b2s]

theorem one_le_int_cast_sq {z : ℤ} (hz : z ≠ 0) :
    (1 : ℝ) ≤ (z : ℝ) ^ 2 := by
  have habs : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
  have hx : (1 : ℝ) ≤ |(z : ℝ)| := by exact_mod_cast habs
  rw [← sq_abs]
  nlinarith [hx, abs_nonneg (z : ℝ)]

/-- Integer combination of an LLL-reduced orthogonal GS basis
    has `‖v‖ ≥ ‖b₁‖ / 2`. This is `2^{(n-1)/2} = 2` for `n = 3`. -/
theorem lll_zspan_norm_ge_half
    {b1s b2s b3s : Fin 3 → ℝ} {μ21 μ31 μ32 : ℝ} {x y z : ℤ}
    {b1 b2 b3 : Fin 3 → ℝ}
    (hb1 : b1 = b1s)
    (hb2 : b2 = fun i => b2s i + μ21 * b1s i)
    (hb3 : b3 = fun i => b3s i + μ31 * b1s i + μ32 * b2s i)
    (h12 : lllInner b1s b2s = 0)
    (h13 : lllInner b1s b3s = 0)
    (h23 : lllInner b2s b3s = 0)
    (hhalf : (1 / 2 : ℝ) * lllNormSq b1s ≤ lllNormSq b2s ∧
        (1 / 2 : ℝ) * lllNormSq b2s ≤ lllNormSq b3s)
    (hN1 : 0 < lllNormSq b1s)
    (hxyz : ¬ (x = 0 ∧ y = 0 ∧ z = 0)) :
    lllNorm b1s / 2 ≤ lllNorm (lllZspan b1 b2 b3 x y z) := by
  have hexp := lllZspan_eq_gs (x := x) (y := y) (z := z) hb1 hb2 hb3
  let α : ℝ := (x : ℝ) + (y : ℝ) * μ21 + (z : ℝ) * μ31
  let β : ℝ := (y : ℝ) + (z : ℝ) * μ32
  let γ : ℝ := (z : ℝ)
  have hnorm :
      lllNormSq (lllZspan b1 b2 b3 x y z) =
        α ^ 2 * lllNormSq b1s + β ^ 2 * lllNormSq b2s +
          γ ^ 2 * lllNormSq b3s := by
    change lllNormSq (lllZspan b1 b2 b3 x y z) =
      ((x : ℝ) + (y : ℝ) * μ21 + (z : ℝ) * μ31) ^ 2 * lllNormSq b1s +
        ((y : ℝ) + (z : ℝ) * μ32) ^ 2 * lllNormSq b2s +
          (z : ℝ) ^ 2 * lllNormSq b3s
    rw [hexp]
    exact lllNormSq_linear_orth3 h12 h13 h23
  have hN2 : (1 / 2 : ℝ) * lllNormSq b1s ≤ lllNormSq b2s := hhalf.1
  have hN3 : (1 / 2 : ℝ) * lllNormSq b2s ≤ lllNormSq b3s := hhalf.2
  have hN3' : (1 / 4 : ℝ) * lllNormSq b1s ≤ lllNormSq b3s := by
    nlinarith [hN2, hN3, lllNormSq_nonneg b2s]
  have hsq : lllNormSq b1s / 4 ≤ lllNormSq (lllZspan b1 b2 b3 x y z) := by
    rw [hnorm]
    by_cases hz : z = 0
    · by_cases hy : y = 0
      · have hx : x ≠ 0 := by
          intro hx
          exact hxyz ⟨hx, hy, hz⟩
        have hα : α = (x : ℝ) := by simp [α, hy, hz]
        have hx2 : (1 : ℝ) ≤ (x : ℝ) ^ 2 := one_le_int_cast_sq hx
        rw [hα]
        nlinarith [hx2, hN1, sq_nonneg β, sq_nonneg γ,
          lllNormSq_nonneg b2s, lllNormSq_nonneg b3s]
      · have hy2 : (1 : ℝ) ≤ (y : ℝ) ^ 2 := one_le_int_cast_sq hy
        have hβ : β = (y : ℝ) := by simp [β, hz]
        rw [hβ]
        nlinarith [hy2, hN2, hN1, sq_nonneg α, sq_nonneg γ,
          lllNormSq_nonneg b1s, lllNormSq_nonneg b3s]
    · have hz2 : (1 : ℝ) ≤ (z : ℝ) ^ 2 := one_le_int_cast_sq hz
      have hγ : γ = (z : ℝ) := rfl
      rw [hγ]
      nlinarith [hz2, hN3', hN1, sq_nonneg α, sq_nonneg β,
        lllNormSq_nonneg b1s, lllNormSq_nonneg b2s]
  have hN1nn : 0 ≤ lllNormSq b1s := le_of_lt hN1
  unfold lllNorm
  have hsplit :
      Real.sqrt (lllNormSq b1s) / 2 =
        Real.sqrt (lllNormSq b1s / 4) := by
    rw [Real.sqrt_div hN1nn 4]
    have : Real.sqrt 4 = 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num,
        Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2)]
    rw [this]
  rw [hsplit]
  exact Real.sqrt_le_sqrt hsq

/-- LLL-reduced Z-basis ⇒ `‖b₁‖ ≤ 2 λ₁` (`n = 3`). -/
theorem lll_svt_bound_of_reduced
    (A B : ℕ)
    {b1 b2 b3 b1s b2s b3s : Fin 3 → ℝ} {μ21 μ31 μ32 : ℝ}
    (hb1 : b1 = b1s)
    (hb2 : b2 = fun i => b2s i + μ21 * b1s i)
    (hb3 : b3 = fun i => b3s i + μ31 * b1s i + μ32 * b2s i)
    (h12 : lllInner b1s b2s = 0)
    (h13 : lllInner b1s b3s = 0)
    (h23 : lllInner b2s b3s = 0)
    (hred : LLL_reduced b1s b2s b3s μ21 μ31 μ32)
    (hN1 : 0 < lllNormSq b1s)
    (_hmem : mem_LLL_lattice A B b1)
    (hspan : ∀ v, mem_LLL_lattice A B v →
        ∃ x y z : ℤ, v = lllZspan b1 b2 b3 x y z) :
    lllNorm b1 ≤ 2 * LLL_lambda1 A B := by
  have hhalf := lll_reduced_gs_half
    (by rwa [lllInner_comm] : lllInner b2s b1s = 0)
    (by rwa [lllInner_comm] : lllInner b3s b2s = 0) hred
  have hlb : ∀ r ∈ LLL_nonzero_norms A B, lllNorm b1s / 2 ≤ r := by
    intro r ⟨v, hvmem, hvne, heq⟩
    obtain ⟨x, y, z, hxyz⟩ := hspan v hvmem
    have hnz : ¬ (x = 0 ∧ y = 0 ∧ z = 0) := by
      intro h0
      apply hvne
      rw [hxyz]
      rcases h0 with ⟨hx, hy, hz⟩
      ext i
      simp [lllZspan, hx, hy, hz]
    have := lll_zspan_norm_ge_half hb1 hb2 hb3 h12 h13 h23 hhalf hN1 hnz
    rw [heq, hxyz]
    exact this
  have hinf : lllNorm b1s / 2 ≤ LLL_lambda1 A B :=
    le_csInf ⟨lllNorm (LLL_v A B), LLL_v_mem_norms A B⟩ hlb
  have hb1eq : lllNorm b1 = lllNorm b1s := by rw [hb1]
  rw [hb1eq]
  have hmul : lllNorm b1s ≤ LLL_lambda1 A B * 2 :=
    (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hinf
  linarith [hmul]

/-- Reduced GS lengths: `‖b₁*‖⁶ ≤ 8 (‖b₁*‖² ‖b₂*‖² ‖b₃*‖²)`. -/
theorem lll_det_prod_sq_of_reduced
    {b1s b2s b3s : Fin 3 → ℝ} {μ21 μ31 μ32 : ℝ}
    (h12 : lllInner b2s b1s = 0)
    (h23 : lllInner b3s b2s = 0)
    (hred : LLL_reduced b1s b2s b3s μ21 μ31 μ32) :
    lllNormSq b1s ^ 3 ≤
      8 * (lllNormSq b1s * lllNormSq b2s * lllNormSq b3s) := by
  have hhalf := lll_reduced_gs_half h12 h23 hred
  have hN1 := lllNormSq_nonneg b1s
  have hN2 := lllNormSq_nonneg b2s
  have hN3 := lllNormSq_nonneg b3s
  have h2 : lllNormSq b2s ≥ lllNormSq b1s / 2 := by linarith [hhalf.1]
  have h3 : lllNormSq b3s ≥ lllNormSq b2s / 2 := by linarith [hhalf.2]
  have h34 : lllNormSq b3s ≥ lllNormSq b1s / 4 := by
    nlinarith [h2, h3, hN2]
  have hprod : lllNormSq b1s * lllNormSq b1s ≤
      8 * lllNormSq b2s * lllNormSq b3s := by
    nlinarith [h2, h34, hN2, hN3]
  nlinarith [hprod, hN1]

theorem LLL_b2star_orth_b1star (A B : ℕ)
    (h : lllNormSq (LLL_b1star A) ≠ 0) :
    lllInner (LLL_b2star A B) (LLL_b1star A) = 0 := by
  have hsub :
      LLL_b2star A B =
        fun i => LLL_b2 B i + (-LLL_mu21 A B) * LLL_b1star A i := by
    unfold LLL_b2star
    ext i
    ring
  have hcalc :
      lllInner (LLL_b2star A B) (LLL_b1star A) =
        lllInner (LLL_b2 B) (LLL_b1star A) -
          LLL_mu21 A B * lllNormSq (LLL_b1star A) := by
    rw [hsub, lllInner_add, lllInner_smul]
    unfold lllNormSq
    ring
  rw [hcalc]
  unfold LLL_mu21
  field_simp [h]

theorem LLL_b1star_normSq_ne_zero (A : ℕ) :
    lllNormSq (LLL_b1star A) ≠ 0 := by
  have := LLL_b1_normSq_ge_one A
  unfold LLL_b1star
  linarith

/-- Baker–Davenport rearrangement: if a first GS length `r`
    is at most `|v₃|` and larger than 17, then
    `|Λ| ≥ (r − 17)/C`. On a solution with `B > 10⁶` one has
    `|v₃| < 18`, so this never beats `|Λ| < 1/B`. -/
theorem baker_davenport_gs_lower
    (A B : ℕ) (r : ℝ)
    (hle : r ≤ |LLL_v A B 2|)
    (h17 : 17 < r) :
    (r - 17) / LLL_C_real ≤ |Lambda A B| := by
  have hthird : 17 < |LLL_v A B 2| := lt_of_lt_of_le h17 hle
  have happ := abs_Lambda_ge_of_third_gt_seventeen A B (by
    rw [← LLL_v_two]
    exact hthird)
  have hC := LLL_C_real_pos
  have hform : |LLL_v A B 2| =
      |(4 : ℝ) * (LLL_e2 A B).1 - 13 * (LLL_e2 A B).2| := by
    rw [LLL_v_two]
  have hmono : (r - 17) / LLL_C_real ≤
      (|LLL_v A B 2| - 17) / LLL_C_real :=
    div_le_div_of_nonneg_right (by linarith [hle]) (le_of_lt hC)
  rw [hform] at hmono
  exact le_trans hmono happ

/-- Gram–Schmidt `μ₂₁` for an arbitrary pair. -/
def lllMu21 (b1 b2 : Fin 3 → ℝ) : ℝ :=
  lllInner b2 b1 / lllNormSq b1

def lllB2s (b1 b2 : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => b2 i - lllMu21 b1 b2 * b1 i

def lllMu31 (b1 b3 : Fin 3 → ℝ) : ℝ :=
  lllInner b3 b1 / lllNormSq b1

def lllMu32 (b1 b2 b3 : Fin 3 → ℝ) : ℝ :=
  lllInner b3 (lllB2s b1 b2) / lllNormSq (lllB2s b1 b2)

def lllB3s (b1 b2 b3 : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i =>
    b3 i - lllMu31 b1 b3 * b1 i - lllMu32 b1 b2 b3 * lllB2s b1 b2 i

/-- LLL potential of a triple, written from the original vectors. -/
def lllBasisPotential (b1 b2 b3 : Fin 3 → ℝ) : ℝ :=
  lllPotential b1 (lllB2s b1 b2) (lllB3s b1 b2 b3)

/-- Size-reduction and Lovász on the Gram–Schmidt of `(b₁,b₂,b₃)`. -/
def lllIsReducedBasis (b1 b2 b3 : Fin 3 → ℝ) : Prop :=
  LLL_reduced b1 (lllB2s b1 b2) (lllB3s b1 b2 b3)
    (lllMu21 b1 b2) (lllMu31 b1 b3) (lllMu32 b1 b2 b3)

/-- The triple generates the displayed lattice over `ℤ`. -/
def lllGenerates (A B : ℕ) (b1 b2 b3 : Fin 3 → ℝ) : Prop :=
  ∀ v, mem_LLL_lattice A B v →
    ∃ x y z : ℤ, v = lllZspan b1 b2 b3 x y z

/-- Integer coordinates (the displayed basis is in `ℤ³`). -/
def lllCoordInt (v : Fin 3 → ℝ) : Prop :=
  ∀ i : Fin 3, ∃ z : ℤ, v i = (z : ℝ)

/-- Size-reduction of `b₂` against `b₁`. -/
def lllSizeReduce2 (b1 b2 : Fin 3 → ℝ) : Fin 3 → ℝ :=
  fun i => b2 i - (lllNearestInt (lllMu21 b1 b2) : ℝ) * b1 i

/-- Size-reduction of `b₃` against already size-reduced `b₂`, then `b₁`. -/
def lllSizeReduce3 (b1 b2 b3 : Fin 3 → ℝ) : Fin 3 → ℝ :=
  let b3mid : Fin 3 → ℝ :=
    fun i => b3 i - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 i
  fun i =>
    b3mid i -
      (lllNearestInt (lllInner b3mid b1 / lllNormSq b1) : ℝ) * b1 i

/-- 3×3 Gram determinant in inner-product coordinates. -/
def lllGramDet (b1 b2 b3 : Fin 3 → ℝ) : ℝ :=
  lllNormSq b1 * lllNormSq b2 * lllNormSq b3 +
    2 * lllInner b1 b2 * lllInner b2 b3 * lllInner b1 b3 -
    lllNormSq b1 * lllInner b2 b3 ^ 2 -
    lllNormSq b2 * lllInner b1 b3 ^ 2 -
    lllNormSq b3 * lllInner b1 b2 ^ 2

def lllGram2 (b1 b2 : Fin 3 → ℝ) : ℝ :=
  lllNormSq b1 * lllNormSq b2 - lllInner b1 b2 ^ 2

theorem LLL_span_eq_zspan (A B : ℕ) (x y z : ℤ) :
    LLL_span A B x y z =
      lllZspan (LLL_b1 A) (LLL_b2 B) LLL_b3 x y z := rfl

theorem LLL_b1_mem (A B : ℕ) : mem_LLL_lattice A B (LLL_b1 A) :=
  ⟨1, 0, 0, by
    ext i
    simp [LLL_span]⟩

theorem LLL_b2_mem (A B : ℕ) : mem_LLL_lattice A B (LLL_b2 B) :=
  ⟨0, 1, 0, by
    ext i
    simp [LLL_span]⟩

theorem LLL_b3_mem (A B : ℕ) : mem_LLL_lattice A B LLL_b3 :=
  ⟨0, 0, 1, by
    ext i
    simp [LLL_span]⟩

theorem LLL_displayed_generates (A B : ℕ) :
    lllGenerates A B (LLL_b1 A) (LLL_b2 B) LLL_b3 := by
  intro v ⟨x, y, z, hv⟩
  exact ⟨x, y, z, by rw [hv]; rfl⟩

theorem LLL_b1_coord_int (A : ℕ) : lllCoordInt (LLL_b1 A) := by
  intro i
  fin_cases i
  · exact ⟨1, by simp [LLL_b1]⟩
  · exact ⟨0, by simp [LLL_b1]⟩
  · exact ⟨⌊LLL_C_real * log (A : ℝ)⌋, by simp [LLL_b1]⟩

theorem LLL_b2_coord_int (B : ℕ) : lllCoordInt (LLL_b2 B) := by
  intro i
  fin_cases i
  · exact ⟨0, by simp [LLL_b2]⟩
  · exact ⟨1, by simp [LLL_b2]⟩
  · exact ⟨⌊LLL_C_real * log ((B + 3 : ℕ) : ℝ)⌋, by simp [LLL_b2]⟩

theorem LLL_b3_coord_int : lllCoordInt LLL_b3 := by
  intro i
  fin_cases i
  · exact ⟨0, by simp [LLL_b3]⟩
  · exact ⟨0, by simp [LLL_b3]⟩
  · refine ⟨LLL_C_nat, ?_⟩
    simp [LLL_b3, LLL_C_real]

theorem LLL_span_coord_int (A B : ℕ) (x y z : ℤ) :
    lllCoordInt (LLL_span A B x y z) := by
  intro i
  obtain ⟨p, hp⟩ := LLL_b1_coord_int A i
  obtain ⟨q, hq⟩ := LLL_b2_coord_int B i
  obtain ⟨r, hr⟩ := LLL_b3_coord_int i
  refine ⟨x * p + y * q + z * r, ?_⟩
  simp [LLL_span, hp, hq, hr]

theorem mem_LLL_coord_int {A B : ℕ} {v : Fin 3 → ℝ}
    (h : mem_LLL_lattice A B v) : lllCoordInt v := by
  obtain ⟨x, y, z, hv⟩ := h
  rw [hv]
  exact LLL_span_coord_int A B x y z

theorem lllInner_int_of_coords {u v : Fin 3 → ℝ}
    (hu : lllCoordInt u) (hv : lllCoordInt v) :
    ∃ z : ℤ, (z : ℝ) = lllInner u v := by
  obtain ⟨a0, h0⟩ := hu 0
  obtain ⟨a1, h1⟩ := hu 1
  obtain ⟨a2, h2⟩ := hu 2
  obtain ⟨b0, k0⟩ := hv 0
  obtain ⟨b1, k1⟩ := hv 1
  obtain ⟨b2, k2⟩ := hv 2
  refine ⟨a0 * b0 + a1 * b1 + a2 * b2, ?_⟩
  unfold lllInner
  rw [Fin.sum_univ_three, h0, h1, h2, k0, k1, k2]
  push_cast
  ring

theorem lllNormSq_int_of_coords {v : Fin 3 → ℝ} (hv : lllCoordInt v) :
    ∃ z : ℤ, (z : ℝ) = lllNormSq v :=
  lllInner_int_of_coords hv hv

theorem LLL_span_smul (A B : ℕ) (k x y z : ℤ) :
    (fun i => (k : ℝ) * LLL_span A B x y z i) =
      LLL_span A B (k * x) (k * y) (k * z) := by
  ext i
  simp [LLL_span]
  ring

theorem LLL_span_add (A B : ℕ) (x1 y1 z1 x2 y2 z2 : ℤ) :
    (fun i => LLL_span A B x1 y1 z1 i + LLL_span A B x2 y2 z2 i) =
      LLL_span A B (x1 + x2) (y1 + y2) (z1 + z2) := by
  ext i
  simp [LLL_span]
  ring

theorem LLL_span_sub (A B : ℕ) (x1 y1 z1 x2 y2 z2 : ℤ) :
    (fun i => LLL_span A B x1 y1 z1 i - LLL_span A B x2 y2 z2 i) =
      LLL_span A B (x1 - x2) (y1 - y2) (z1 - z2) := by
  ext i
  simp [LLL_span]
  ring

theorem mem_LLL_smul {A B : ℕ} (k : ℤ) {v : Fin 3 → ℝ}
    (h : mem_LLL_lattice A B v) :
    mem_LLL_lattice A B (fun i => (k : ℝ) * v i) := by
  obtain ⟨x, y, z, hv⟩ := h
  refine ⟨k * x, k * y, k * z, ?_⟩
  rw [hv]
  exact LLL_span_smul A B k x y z

theorem mem_LLL_add {A B : ℕ} {u v : Fin 3 → ℝ}
    (hu : mem_LLL_lattice A B u) (hv : mem_LLL_lattice A B v) :
    mem_LLL_lattice A B (fun i => u i + v i) := by
  obtain ⟨x1, y1, z1, hu'⟩ := hu
  obtain ⟨x2, y2, z2, hv'⟩ := hv
  refine ⟨x1 + x2, y1 + y2, z1 + z2, ?_⟩
  rw [hu', hv']
  exact LLL_span_add A B x1 y1 z1 x2 y2 z2

theorem mem_LLL_sub {A B : ℕ} {u v : Fin 3 → ℝ}
    (hu : mem_LLL_lattice A B u) (hv : mem_LLL_lattice A B v) :
    mem_LLL_lattice A B (fun i => u i - v i) := by
  obtain ⟨x1, y1, z1, hu'⟩ := hu
  obtain ⟨x2, y2, z2, hv'⟩ := hv
  refine ⟨x1 - x2, y1 - y2, z1 - z2, ?_⟩
  rw [hu', hv']
  exact LLL_span_sub A B x1 y1 z1 x2 y2 z2

theorem lllSizeReduce2_mem {A B : ℕ} {b1 b2 : Fin 3 → ℝ}
    (h1 : mem_LLL_lattice A B b1) (h2 : mem_LLL_lattice A B b2) :
    mem_LLL_lattice A B (lllSizeReduce2 b1 b2) := by
  unfold lllSizeReduce2
  exact mem_LLL_sub h2 (mem_LLL_smul _ h1)

theorem lllInner_sub_smul (u v w : Fin 3 → ℝ) (a : ℝ) :
    lllInner (fun i => u i - a * v i) w =
      lllInner u w - a * lllInner v w := by
  have hneg : (fun i => u i - a * v i) =
      (fun i => u i + (-a) * v i) := by
    ext i; ring
  rw [hneg, lllInner_add, lllInner_smul]
  ring

theorem lllInner_sub_smul_right (u v w : Fin 3 → ℝ) (a : ℝ) :
    lllInner u (fun i => v i - a * w i) =
      lllInner u v - a * lllInner u w := by
  rw [lllInner_comm, lllInner_sub_smul, lllInner_comm u v, lllInner_comm w u]

theorem lllNormSq_sub_smul (u v : Fin 3 → ℝ) (a : ℝ) :
    lllNormSq (fun i => u i - a * v i) =
      lllNormSq u - 2 * a * lllInner u v + a ^ 2 * lllNormSq v := by
  have hrew : (fun i => u i - a * v i) = fun i => u i + (-a) * v i := by
    ext i; ring
  unfold lllNormSq
  rw [hrew, lllInner_add, lllInner_smul, lllInner_add_right,
    lllInner_add_right, lllInner_smul_right, lllInner_smul_right]
  rw [lllInner_comm v u]
  ring

theorem lll_lagrange (u v : Fin 3 → ℝ) :
    lllNormSq u * lllNormSq v - lllInner u v ^ 2 =
      (u 0 * v 1 - u 1 * v 0) ^ 2 +
        (u 0 * v 2 - u 2 * v 0) ^ 2 +
          (u 1 * v 2 - u 2 * v 1) ^ 2 := by
  rw [lllNormSq_eq, lllNormSq_eq]
  unfold lllInner
  rw [Fin.sum_univ_three]
  ring

theorem lllGram2_nonneg (b1 b2 : Fin 3 → ℝ) :
    0 ≤ lllGram2 b1 b2 := by
  unfold lllGram2
  have h := lll_lagrange b1 b2
  have : 0 ≤
      (b1 0 * b2 1 - b1 1 * b2 0) ^ 2 +
        (b1 0 * b2 2 - b1 2 * b2 0) ^ 2 +
          (b1 1 * b2 2 - b1 2 * b2 1) ^ 2 := by
    nlinarith [sq_nonneg (b1 0 * b2 1 - b1 1 * b2 0),
      sq_nonneg (b1 0 * b2 2 - b1 2 * b2 0),
      sq_nonneg (b1 1 * b2 2 - b1 2 * b2 1)]
  linarith [h]

theorem lllB2s_orth {b1 b2 : Fin 3 → ℝ} (h : lllNormSq b1 ≠ 0) :
    lllInner (lllB2s b1 b2) b1 = 0 := by
  have hsub :
      lllB2s b1 b2 =
        fun i => b2 i + (-lllMu21 b1 b2) * b1 i := by
    unfold lllB2s
    ext i
    ring
  have hcalc :
      lllInner (lllB2s b1 b2) b1 =
        lllInner b2 b1 - lllMu21 b1 b2 * lllNormSq b1 := by
    rw [hsub, lllInner_add, lllInner_smul]
    unfold lllNormSq
    ring
  rw [hcalc]
  unfold lllMu21
  field_simp [h]

theorem lllB2s_normSq {b1 b2 : Fin 3 → ℝ} (h : lllNormSq b1 ≠ 0) :
    lllNormSq (lllB2s b1 b2) = lllGram2 b1 b2 / lllNormSq b1 := by
  have hμ : lllMu21 b1 b2 = lllInner b2 b1 / lllNormSq b1 := rfl
  have hcomm : lllInner b2 b1 = lllInner b1 b2 := lllInner_comm _ _
  have hexp := lllNormSq_sub_smul b2 b1 (lllMu21 b1 b2)
  unfold lllB2s
  rw [hexp, hμ, hcomm]
  unfold lllGram2
  field_simp [h]
  ring

theorem lllMu21_sizeReduce (b1 b2 : Fin 3 → ℝ) (h : lllNormSq b1 ≠ 0) :
    lllMu21 b1 (lllSizeReduce2 b1 b2) =
      lllMu21 b1 b2 - (lllNearestInt (lllMu21 b1 b2) : ℝ) := by
  unfold lllMu21
  change
    lllInner
        (fun i =>
          b2 i - (lllNearestInt (lllInner b2 b1 / lllNormSq b1) : ℝ) * b1 i)
        b1 / lllNormSq b1 =
      _
  rw [lllInner_sub_smul]
  have hN : lllInner b1 b1 = lllNormSq b1 := rfl
  rw [hN]
  field_simp [h]
  ring

theorem lllMu21_sizeReduce_le (b1 b2 : Fin 3 → ℝ) (h : lllNormSq b1 ≠ 0) :
    |lllMu21 b1 (lllSizeReduce2 b1 b2)| ≤ 1 / 2 := by
  rw [lllMu21_sizeReduce b1 b2 h]
  exact abs_sub_lllNearestInt (lllMu21 b1 b2)

theorem lllNearestInt_zero : lllNearestInt 0 = 0 := by
  unfold lllNearestInt
  norm_num

theorem lllB2s_sizeReduce (b1 b2 : Fin 3 → ℝ) :
    lllB2s b1 (lllSizeReduce2 b1 b2) = lllB2s b1 b2 := by
  by_cases h : lllNormSq b1 = 0
  · have hμ : lllMu21 b1 b2 = 0 := by
      unfold lllMu21
      simp [h]
    have hμ' : lllMu21 b1 (lllSizeReduce2 b1 b2) = 0 := by
      unfold lllMu21
      simp [h]
    ext i
    calc
      lllB2s b1 (lllSizeReduce2 b1 b2) i =
          lllSizeReduce2 b1 b2 i - lllMu21 b1 (lllSizeReduce2 b1 b2) * b1 i :=
        rfl
      _ = lllSizeReduce2 b1 b2 i := by rw [hμ']; ring
      _ = b2 i - (lllNearestInt (lllMu21 b1 b2) : ℝ) * b1 i := rfl
      _ = b2 i := by rw [hμ, lllNearestInt_zero]; ring
      _ = b2 i - lllMu21 b1 b2 * b1 i := by rw [hμ]; ring
      _ = lllB2s b1 b2 i := rfl
  · ext i
    have hμ := lllMu21_sizeReduce b1 b2 h
    calc
      lllB2s b1 (lllSizeReduce2 b1 b2) i =
          lllSizeReduce2 b1 b2 i - lllMu21 b1 (lllSizeReduce2 b1 b2) * b1 i :=
        rfl
      _ = lllSizeReduce2 b1 b2 i -
            (lllMu21 b1 b2 - (lllNearestInt (lllMu21 b1 b2) : ℝ)) * b1 i := by
        rw [hμ]
      _ = b2 i - (lllNearestInt (lllMu21 b1 b2) : ℝ) * b1 i -
            (lllMu21 b1 b2 - (lllNearestInt (lllMu21 b1 b2) : ℝ)) * b1 i :=
        rfl
      _ = b2 i - lllMu21 b1 b2 * b1 i := by ring
      _ = lllB2s b1 b2 i := rfl

theorem lllB3s_sizeReduce2 (b1 b2 b3 : Fin 3 → ℝ) :
    lllB3s b1 (lllSizeReduce2 b1 b2) b3 = lllB3s b1 b2 b3 := by
  unfold lllB3s lllMu32
  rw [lllB2s_sizeReduce]

theorem lllCoordInt_sub_smul {u v : Fin 3 → ℝ} (k : ℤ)
    (hu : lllCoordInt u) (hv : lllCoordInt v) :
    lllCoordInt (fun i => u i - (k : ℝ) * v i) := by
  intro i
  obtain ⟨a, ha⟩ := hu i
  obtain ⟨b, hb⟩ := hv i
  refine ⟨a - k * b, ?_⟩
  change u i - (k : ℝ) * v i = _
  rw [ha, hb]
  push_cast
  ring

theorem lllSizeReduce2_coordInt {b1 b2 : Fin 3 → ℝ}
    (h1 : lllCoordInt b1) (h2 : lllCoordInt b2) :
    lllCoordInt (lllSizeReduce2 b1 b2) :=
  lllCoordInt_sub_smul _ h2 h1

theorem lllZspan_sizeReduce2 (b1 b2 b3 : Fin 3 → ℝ) (k x y z : ℤ) :
    lllZspan b1 b2 b3 x y z =
      lllZspan b1 (fun i => b2 i - (k : ℝ) * b1 i) b3
        (x + y * k) y z := by
  ext i
  simp [lllZspan]
  ring

theorem lllGenerates_sizeReduce2 {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (h : lllGenerates A B b1 b2 b3) :
    lllGenerates A B b1 (lllSizeReduce2 b1 b2) b3 := by
  intro v hv
  obtain ⟨x, y, z, hv'⟩ := h v hv
  refine ⟨x + y * lllNearestInt (lllMu21 b1 b2), y, z, ?_⟩
  rw [hv']
  exact lllZspan_sizeReduce2 b1 b2 b3 _ x y z

theorem lllZspan_of_sizeReduce3 (b1 b2 b3 : Fin 3 → ℝ)
    (k m x y z : ℤ) :
    lllZspan b1 b2 b3 x y z =
      lllZspan b1 b2
        (fun i => b3 i - (k : ℝ) * b2 i - (m : ℝ) * b1 i)
        (x + z * m) (y + z * k) z := by
  ext i
  simp [lllZspan]
  ring

theorem lllSizeReduce3_eq (b1 b2 b3 : Fin 3 → ℝ) :
    lllSizeReduce3 b1 b2 b3 =
      fun i =>
        b3 i - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 i -
          (lllNearestInt
              (lllInner
                  (fun j =>
                    b3 j - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) *
                      b2 j)
                  b1 / lllNormSq b1) : ℝ) *
            b1 i :=
  rfl

theorem lllSizeReduce3_mem {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (h1 : mem_LLL_lattice A B b1) (h2 : mem_LLL_lattice A B b2)
    (h3 : mem_LLL_lattice A B b3) :
    mem_LLL_lattice A B (lllSizeReduce3 b1 b2 b3) := by
  unfold lllSizeReduce3
  exact mem_LLL_sub
    (mem_LLL_sub h3 (mem_LLL_smul _ h2))
    (mem_LLL_smul _ h1)

theorem lllSizeReduce3_coordInt {b1 b2 b3 : Fin 3 → ℝ}
    (h1 : lllCoordInt b1) (h2 : lllCoordInt b2) (h3 : lllCoordInt b3) :
    lllCoordInt (lllSizeReduce3 b1 b2 b3) := by
  unfold lllSizeReduce3
  exact lllCoordInt_sub_smul _
    (lllCoordInt_sub_smul _ h3 h2) h1

theorem lllGenerates_sizeReduce3 {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (h : lllGenerates A B b1 b2 b3) :
    lllGenerates A B b1 b2 (lllSizeReduce3 b1 b2 b3) := by
  intro v hv
  obtain ⟨x, y, z, hv'⟩ := h v hv
  refine ⟨x + z *
      lllNearestInt
        (lllInner
          (fun j =>
            b3 j - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 j)
          b1 / lllNormSq b1),
    y + z * lllNearestInt (lllMu32 b1 b2 b3), z, ?_⟩
  rw [hv', lllSizeReduce3_eq]
  exact lllZspan_of_sizeReduce3 b1 b2 b3 _ _ x y z

theorem lllZspan_swap12 (b1 b2 b3 : Fin 3 → ℝ) (x y z : ℤ) :
    lllZspan b1 b2 b3 x y z = lllZspan b2 b1 b3 y x z := by
  ext i
  simp [lllZspan]
  ring

theorem lllZspan_swap23 (b1 b2 b3 : Fin 3 → ℝ) (x y z : ℤ) :
    lllZspan b1 b2 b3 x y z = lllZspan b1 b3 b2 x z y := by
  ext i
  simp [lllZspan]
  ring

theorem lllGenerates_swap12 {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (h : lllGenerates A B b1 b2 b3) :
    lllGenerates A B b2 b1 b3 := by
  intro v hv
  obtain ⟨x, y, z, hv'⟩ := h v hv
  exact ⟨y, x, z, by rw [hv']; exact lllZspan_swap12 b1 b2 b3 x y z⟩

theorem lllGenerates_swap23 {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (h : lllGenerates A B b1 b2 b3) :
    lllGenerates A B b1 b3 b2 := by
  intro v hv
  obtain ⟨x, y, z, hv'⟩ := h v hv
  exact ⟨x, z, y, by rw [hv']; exact lllZspan_swap23 b1 b2 b3 x y z⟩

def lllColMatrix (b1 b2 b3 : Fin 3 → ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => if j = 0 then b1 i else if j = 1 then b2 i else b3 i

theorem lllNormSq_eq_zero_iff (v : Fin 3 → ℝ) :
    lllNormSq v = 0 ↔ v = 0 := by
  constructor
  · intro h
    rw [lllNormSq_eq] at h
    have h0 : v 0 = 0 := by
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h1 : v 1 = 0 := by
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    have h2 : v 2 = 0 := by
      nlinarith [sq_nonneg (v 0), sq_nonneg (v 1), sq_nonneg (v 2)]
    ext i
    fin_cases i <;> assumption
  · intro h
    rw [h, lllNormSq_eq]
    simp

theorem LLL_basisMatrix_col (A B : ℕ) :
    LLL_basisMatrix A B =
      lllColMatrix (LLL_b1 A) (LLL_b2 B) LLL_b3 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [LLL_basisMatrix, lllColMatrix, LLL_b1, LLL_b2, LLL_b3, LLL_C_real]

theorem lllCol_det_eq_zero_of_b1 {b1 b2 b3 : Fin 3 → ℝ}
    (h : lllNormSq b1 = 0) :
    (lllColMatrix b1 b2 b3).det = 0 := by
  have hb1 : b1 = 0 := (lllNormSq_eq_zero_iff b1).mp h
  rw [Matrix.det_fin_three]
  simp [lllColMatrix, hb1]

theorem lllCol_det_eq_zero_of_gram2
    {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 = 0) :
    (lllColMatrix b1 b2 b3).det = 0 := by
  have hb2s : lllNormSq (lllB2s b1 b2) = 0 := by
    rw [lllB2s_normSq ha, hg, zero_div]
  have h0 : lllB2s b1 b2 = 0 := (lllNormSq_eq_zero_iff _).mp hb2s
  have hb2 : b2 = fun i => lllMu21 b1 b2 * b1 i := by
    ext i
    have hi := congrArg (fun v : Fin 3 → ℝ => v i) h0
    simp [lllB2s] at hi
    linarith
  rw [Matrix.det_fin_three]
  have col0 (i : Fin 3) : lllColMatrix b1 b2 b3 i 0 = b1 i := by
    simp [lllColMatrix]
  have col1 (i : Fin 3) : lllColMatrix b1 b2 b3 i 1 = lllMu21 b1 b2 * b1 i := by
    simp [lllColMatrix]
    exact congrArg (fun v : Fin 3 → ℝ => v i) hb2
  have col2 (i : Fin 3) : lllColMatrix b1 b2 b3 i 2 = b3 i := by
    simp [lllColMatrix]
  rw [col0 0, col0 1, col0 2, col1 0, col1 1, col1 2, col2 0, col2 1, col2 2]
  ring

theorem lllGenerates_det_ne {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (hgen : lllGenerates A B b1 b2 b3) :
    (lllColMatrix b1 b2 b3).det ≠ 0 := by
  obtain ⟨x1, y1, z1, e1⟩ := hgen (LLL_b1 A) (LLL_b1_mem A B)
  obtain ⟨x2, y2, z2, e2⟩ := hgen (LLL_b2 B) (LLL_b2_mem A B)
  obtain ⟨x3, y3, z3, e3⟩ := hgen LLL_b3 (LLL_b3_mem A B)
  let U : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    if j = 0 then
      (if i = 0 then (x1 : ℝ) else if i = 1 then (y1 : ℝ) else (z1 : ℝ))
    else if j = 1 then
      (if i = 0 then (x2 : ℝ) else if i = 1 then (y2 : ℝ) else (z2 : ℝ))
    else
      (if i = 0 then (x3 : ℝ) else if i = 1 then (y3 : ℝ) else (z3 : ℝ))
  have hU0 : U 0 0 = x1 ∧ U 1 0 = y1 ∧ U 2 0 = z1 := by
    simp [U]
  have hU1 : U 0 1 = x2 ∧ U 1 1 = y2 ∧ U 2 1 = z2 := by
    simp [U]
  have hU2 : U 0 2 = x3 ∧ U 1 2 = y3 ∧ U 2 2 = z3 := by
    simp [U]
  have hmul : LLL_basisMatrix A B = lllColMatrix b1 b2 b3 * U := by
    ext i j
    rw [LLL_basisMatrix_col]
    unfold lllColMatrix
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases j
    · simp [hU0.1, hU0.2.1, hU0.2.2, e1, lllZspan]
      ring
    · simp [hU1.1, hU1.2.1, hU1.2.2, e2, lllZspan]
      ring
    · simp [hU2.1, hU2.2.1, hU2.2.2, e3, lllZspan]
      ring
  have hdet :
      (LLL_basisMatrix A B).det =
        (lllColMatrix b1 b2 b3).det * U.det := by
    rw [hmul, Matrix.det_mul]
  intro hz
  rw [LLL_basis_det, hz, zero_mul] at hdet
  exact (ne_of_gt LLL_C_real_pos) hdet

theorem lllGenerates_normSq_b1_ne {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (hgen : lllGenerates A B b1 b2 b3) :
    lllNormSq b1 ≠ 0 := by
  intro h
  exact lllGenerates_det_ne hgen (lllCol_det_eq_zero_of_b1 h)

theorem lllGenerates_gram2_ne {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (hgen : lllGenerates A B b1 b2 b3) :
    lllGram2 b1 b2 ≠ 0 := by
  intro h
  exact lllGenerates_det_ne hgen
    (lllCol_det_eq_zero_of_gram2 (lllGenerates_normSq_b1_ne hgen) h)

theorem lllB3s_orth_b1 {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) :
    lllInner (lllB3s b1 b2 b3) b1 = 0 := by
  have horth2 := lllB2s_orth (b2 := b2) ha
  have hrew :
      lllB3s b1 b2 b3 =
        fun i =>
          (b3 i - lllMu31 b1 b3 * b1 i) -
            lllMu32 b1 b2 b3 * lllB2s b1 b2 i := by
    ext i
    unfold lllB3s
    ring
  rw [hrew, lllInner_sub_smul]
  rw [horth2]
  simp only [mul_zero, sub_zero]
  rw [lllInner_sub_smul]
  unfold lllMu31 lllNormSq
  have hN : lllInner b1 b1 ≠ 0 := ha
  have hcancel :
      lllInner b3 b1 / lllInner b1 b1 * lllInner b1 b1 =
        lllInner b3 b1 :=
    div_mul_cancel₀ _ hN
  rw [hcancel, sub_self]

theorem lllB3s_orth_b2s {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0) :
    lllInner (lllB3s b1 b2 b3) (lllB2s b1 b2) = 0 := by
  have hb2s_ne : lllNormSq (lllB2s b1 b2) ≠ 0 := by
    rw [lllB2s_normSq ha]
    exact div_ne_zero hg ha
  have horth2 := lllB2s_orth (b2 := b2) ha
  unfold lllB3s
  rw [show (fun i =>
        b3 i - lllMu31 b1 b3 * b1 i - lllMu32 b1 b2 b3 * lllB2s b1 b2 i) =
          fun i =>
            (b3 i - lllMu31 b1 b3 * b1 i) -
              lllMu32 b1 b2 b3 * lllB2s b1 b2 i by
        ext i; ring,
      lllInner_sub_smul]
  have hmid :
      lllInner (fun i => b3 i - lllMu31 b1 b3 * b1 i) (lllB2s b1 b2) =
        lllInner b3 (lllB2s b1 b2) := by
    rw [lllInner_sub_smul, lllInner_comm b1, horth2]
    ring
  rw [hmid]
  unfold lllMu32
  have hN : lllInner (lllB2s b1 b2) (lllB2s b1 b2) = lllNormSq (lllB2s b1 b2) :=
    rfl
  rw [hN]
  have :
      lllInner b3 (lllB2s b1 b2) / lllNormSq (lllB2s b1 b2) *
        lllNormSq (lllB2s b1 b2) =
      lllInner b3 (lllB2s b1 b2) :=
    div_mul_cancel₀ _ hb2s_ne
  rw [this, sub_self]

theorem lllB2_eq_gs (b1 b2 : Fin 3 → ℝ) :
    b2 = fun i => lllB2s b1 b2 i + lllMu21 b1 b2 * b1 i := by
  ext i
  unfold lllB2s
  ring

theorem lllB3_eq_gs (b1 b2 b3 : Fin 3 → ℝ) :
    b3 =
      fun i =>
        lllB3s b1 b2 b3 i + lllMu31 b1 b3 * b1 i +
          lllMu32 b1 b2 b3 * lllB2s b1 b2 i := by
  ext i
  unfold lllB3s
  ring

theorem lllMu32_sub_b2 {b1 b2 b3 : Fin 3 → ℝ} (k : ℤ)
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0) :
    lllMu32 b1 b2 (fun i => b3 i - (k : ℝ) * b2 i) =
      lllMu32 b1 b2 b3 - k := by
  have hb2s_ne : lllNormSq (lllB2s b1 b2) ≠ 0 := by
    rw [lllB2s_normSq ha]
    exact div_ne_zero hg ha
  have hb2_b2s : lllInner b2 (lllB2s b1 b2) = lllNormSq (lllB2s b1 b2) := by
    convert_to
      lllInner (fun i => lllB2s b1 b2 i + lllMu21 b1 b2 * b1 i)
          (lllB2s b1 b2) =
        lllNormSq (lllB2s b1 b2)
    · rw [← lllB2_eq_gs]
    rw [lllInner_add, lllInner_smul, lllInner_comm b1, lllB2s_orth ha]
    unfold lllNormSq
    ring
  unfold lllMu32
  rw [lllInner_sub_smul]
  field_simp [hb2s_ne]
  rw [hb2_b2s]
  ring

theorem lllMu32_sub_b1 {b1 b2 b3 : Fin 3 → ℝ} (m : ℤ)
    (ha : lllNormSq b1 ≠ 0) :
    lllMu32 b1 b2 (fun i => b3 i - (m : ℝ) * b1 i) =
      lllMu32 b1 b2 b3 := by
  unfold lllMu32
  rw [lllInner_sub_smul]
  have h0 : lllInner b1 (lllB2s b1 b2) = 0 :=
    (lllInner_comm b1 (lllB2s b1 b2)).trans (lllB2s_orth ha)
  rw [h0]
  ring

theorem lllMu31_sub_b1 {b1 b3 : Fin 3 → ℝ} (m : ℤ)
    (ha : lllNormSq b1 ≠ 0) :
    lllMu31 b1 (fun i => b3 i - (m : ℝ) * b1 i) =
      lllMu31 b1 b3 - m := by
  unfold lllMu31
  rw [lllInner_sub_smul]
  have hN : lllInner b1 b1 = lllNormSq b1 := rfl
  rw [hN]
  field_simp [ha]
  ring

theorem lllMu31_sizeReduce3 {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) :
    lllMu31 b1 (lllSizeReduce3 b1 b2 b3) =
      lllInner
          (fun j =>
            b3 j - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 j)
          b1 / lllNormSq b1 -
        (lllNearestInt
          (lllInner
              (fun j =>
                b3 j - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 j)
              b1 / lllNormSq b1) : ℝ) := by
  change
    lllMu31 b1
        (fun i =>
          (b3 i - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 i) -
            (lllNearestInt
                (lllInner
                    (fun j =>
                      b3 j - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) *
                        b2 j)
                    b1 / lllNormSq b1) : ℝ) *
              b1 i) =
      _
  exact lllMu31_sub_b1 _ ha

theorem lllMu31_sizeReduce3_le {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) :
    |lllMu31 b1 (lllSizeReduce3 b1 b2 b3)| ≤ 1 / 2 := by
  rw [lllMu31_sizeReduce3 ha]
  exact abs_sub_lllNearestInt _

theorem lllMu32_sizeReduce3 {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0) :
    lllMu32 b1 b2 (lllSizeReduce3 b1 b2 b3) =
      lllMu32 b1 b2 b3 - lllNearestInt (lllMu32 b1 b2 b3) := by
  have hmid :
      lllMu32 b1 b2
          (fun i =>
            b3 i - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 i) =
        lllMu32 b1 b2 b3 - lllNearestInt (lllMu32 b1 b2 b3) :=
    lllMu32_sub_b2 _ ha hg
  unfold lllSizeReduce3
  have hlast :=
    lllMu32_sub_b1 (b2 := b2)
      (b3 := fun i =>
        b3 i - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 i)
      (lllNearestInt
        (lllInner
            (fun j =>
              b3 j - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 j)
            b1 / lllNormSq b1))
      ha
  change lllMu32 b1 b2
      (fun i =>
        (b3 i - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) * b2 i) -
          (lllNearestInt
              (lllInner
                  (fun j =>
                    b3 j - (lllNearestInt (lllMu32 b1 b2 b3) : ℝ) *
                      b2 j)
                  b1 / lllNormSq b1) : ℝ) *
            b1 i) =
    _
  rw [hlast, hmid]

theorem lllMu32_sizeReduce3_le {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0) :
    |lllMu32 b1 b2 (lllSizeReduce3 b1 b2 b3)| ≤ 1 / 2 := by
  rw [lllMu32_sizeReduce3 ha hg]
  exact abs_sub_lllNearestInt _

theorem lllB3s_sizeReduce3
    {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0) :
    lllB3s b1 b2 (lllSizeReduce3 b1 b2 b3) = lllB3s b1 b2 b3 := by
  let k : ℤ := lllNearestInt (lllMu32 b1 b2 b3)
  let b3mid : Fin 3 → ℝ := fun i => b3 i - (k : ℝ) * b2 i
  let m : ℤ := lllNearestInt (lllInner b3mid b1 / lllNormSq b1)
  have hb3r : lllSizeReduce3 b1 b2 b3 =
      fun i => b3mid i - (m : ℝ) * b1 i := rfl
  have hμ32 : lllMu32 b1 b2 (lllSizeReduce3 b1 b2 b3) =
      lllMu32 b1 b2 b3 - k := by
    simpa [k] using lllMu32_sizeReduce3 (b3 := b3) ha hg
  have hμ31 : lllMu31 b1 (lllSizeReduce3 b1 b2 b3) =
      lllMu31 b1 b3mid - m := by
    rw [hb3r]
    exact lllMu31_sub_b1 m ha
  have hμ31mid : lllMu31 b1 b3mid =
      lllMu31 b1 b3 - (k : ℝ) * lllMu21 b1 b2 := by
    unfold lllMu31 lllMu21
    simp [b3mid, lllInner_sub_smul]
    field_simp [ha]
  have hb2 := lllB2_eq_gs b1 b2
  ext i
  unfold lllB3s
  rw [hb3r]
  have hi : b3mid i - (m : ℝ) * b1 i -
        lllMu31 b1 (lllSizeReduce3 b1 b2 b3) * b1 i -
        lllMu32 b1 b2 (lllSizeReduce3 b1 b2 b3) * lllB2s b1 b2 i =
      b3 i - lllMu31 b1 b3 * b1 i -
        lllMu32 b1 b2 b3 * lllB2s b1 b2 i := by
    have hb2i : b2 i = lllB2s b1 b2 i + lllMu21 b1 b2 * b1 i :=
      congrArg (fun v : Fin 3 → ℝ => v i) hb2
    simp [b3mid, hμ31, hμ32, hμ31mid, hb2i]
    ring
  exact hi

theorem lllGram2_int {b1 b2 : Fin 3 → ℝ}
    (h1 : lllCoordInt b1) (h2 : lllCoordInt b2) :
    ∃ z : ℤ, (z : ℝ) = lllGram2 b1 b2 := by
  obtain ⟨a, ha⟩ := lllNormSq_int_of_coords h1
  obtain ⟨b, hb⟩ := lllNormSq_int_of_coords h2
  obtain ⟨p, hp⟩ := lllInner_int_of_coords h1 h2
  refine ⟨a * b - p ^ 2, ?_⟩
  unfold lllGram2
  rw [← ha, ← hb, ← hp]
  norm_cast

theorem lllGramDet_int {b1 b2 b3 : Fin 3 → ℝ}
    (h1 : lllCoordInt b1) (h2 : lllCoordInt b2) (h3 : lllCoordInt b3) :
    ∃ z : ℤ, (z : ℝ) = lllGramDet b1 b2 b3 := by
  obtain ⟨a, ha⟩ := lllNormSq_int_of_coords h1
  obtain ⟨b, hb⟩ := lllNormSq_int_of_coords h2
  obtain ⟨c, hc⟩ := lllNormSq_int_of_coords h3
  obtain ⟨p, hp⟩ := lllInner_int_of_coords h1 h2
  obtain ⟨q, hq⟩ := lllInner_int_of_coords h1 h3
  obtain ⟨r, hr⟩ := lllInner_int_of_coords h2 h3
  refine ⟨a * b * c + 2 * p * r * q - a * r ^ 2 - b * q ^ 2 - c * p ^ 2, ?_⟩
  unfold lllGramDet
  rw [← ha, ← hb, ← hc, ← hp, ← hq, ← hr]
  norm_cast

theorem lllB3s_normSq_mul_gram2
    {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0) :
    lllNormSq (lllB3s b1 b2 b3) * lllGram2 b1 b2 =
      lllGramDet b1 b2 b3 := by
  have hb2s := lllB2s_normSq (b2 := b2) ha
  have hb2s_ne : lllNormSq (lllB2s b1 b2) ≠ 0 := by
    rw [hb2s]
    exact div_ne_zero hg ha
  have hw :
      lllNormSq (fun i => b3 i - lllMu31 b1 b3 * b1 i) =
        lllNormSq b3 - lllInner b3 b1 ^ 2 / lllNormSq b1 := by
    have hexp := lllNormSq_sub_smul b3 b1 (lllMu31 b1 b3)
    unfold lllMu31 at hexp ⊢
    rw [hexp]
    field_simp [ha]
    unfold lllNormSq
    ring
  have hstar :
      lllNormSq (lllB3s b1 b2 b3) =
        lllNormSq (fun i => b3 i - lllMu31 b1 b3 * b1 i) -
          lllInner b3 (lllB2s b1 b2) ^ 2 / lllNormSq (lllB2s b1 b2) := by
    have hrew :
        lllB3s b1 b2 b3 =
          fun i =>
            (b3 i - lllMu31 b1 b3 * b1 i) -
              lllMu32 b1 b2 b3 * lllB2s b1 b2 i := by
      ext i
      unfold lllB3s
      ring
    have hexp :=
      lllNormSq_sub_smul
        (fun i => b3 i - lllMu31 b1 b3 * b1 i)
        (lllB2s b1 b2) (lllMu32 b1 b2 b3)
    have hinner :
        lllInner (fun i => b3 i - lllMu31 b1 b3 * b1 i) (lllB2s b1 b2) =
          lllInner b3 (lllB2s b1 b2) := by
      rw [lllInner_sub_smul]
      have h0 : lllInner b1 (lllB2s b1 b2) = 0 :=
        (lllInner_comm b1 (lllB2s b1 b2)).trans (lllB2s_orth ha)
      rw [h0]
      ring
    rw [hrew, hexp, hinner]
    unfold lllMu32
    field_simp [hb2s_ne]
    ring
  have hμ : lllInner b3 (lllB2s b1 b2) =
      lllInner b3 b2 - lllMu21 b1 b2 * lllInner b3 b1 := by
    unfold lllB2s
    rw [lllInner_sub_smul_right]
  rw [hstar, hw, hμ]
  unfold lllGramDet lllGram2 lllMu21
  field_simp [ha, hg, hb2s, hb2s_ne]
  have h31 : lllInner b3 b1 = lllInner b1 b3 := lllInner_comm _ _
  have h32 : lllInner b3 b2 = lllInner b2 b3 := lllInner_comm _ _
  have h21 : lllInner b2 b1 = lllInner b1 b2 := lllInner_comm _ _
  rw [h31, h32, h21]
  unfold lllGram2
  ring

theorem lllBasisPotential_eq_prod
    {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0) :
    lllBasisPotential b1 b2 b3 =
      lllNormSq b1 * lllGram2 b1 b2 * lllGramDet b1 b2 b3 := by
  have h2 := lllB2s_normSq (b2 := b2) ha
  have h3 :
      lllNormSq (lllB3s b1 b2 b3) =
        lllGramDet b1 b2 b3 / lllGram2 b1 b2 := by
    have hmul := lllB3s_normSq_mul_gram2 (b3 := b3) ha hg
    exact (eq_div_iff hg).mpr (by linarith [hmul])
  unfold lllBasisPotential lllPotential
  rw [h2, h3]
  field_simp [ha, hg]
  ring

theorem int_toNat_cast {z : ℤ} (hz : 0 ≤ z) :
    (z.toNat : ℝ) = (z : ℝ) := by
  have hzZ : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
  exact_mod_cast hzZ

theorem lllBasisPotential_nat
    {b1 b2 b3 : Fin 3 → ℝ}
    (h1 : lllCoordInt b1) (h2 : lllCoordInt b2) (h3 : lllCoordInt b3)
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0) :
    ∃ n : ℕ, (n : ℝ) = lllBasisPotential b1 b2 b3 := by
  obtain ⟨za, ha'⟩ := lllNormSq_int_of_coords h1
  obtain ⟨zg, hg'⟩ := lllGram2_int h1 h2
  obtain ⟨zd, hd'⟩ := lllGramDet_int h1 h2 h3
  have hpot := lllBasisPotential_eq_prod (b3 := b3) ha hg
  have hza0 : 0 ≤ za :=
    Int.cast_nonneg.mp (by rw [ha']; exact lllNormSq_nonneg b1)
  have hzg0 : 0 ≤ zg :=
    Int.cast_nonneg.mp (by rw [hg']; exact lllGram2_nonneg b1 b2)
  have hzd0 : 0 ≤ zd := by
    have hmul := lllB3s_normSq_mul_gram2 (b3 := b3) ha hg
    exact Int.cast_nonneg.mp (by
      rw [hd', ← hmul]
      exact mul_nonneg (lllNormSq_nonneg _) (lllGram2_nonneg _ _))
  refine ⟨za.toNat * zg.toNat * zd.toNat, ?_⟩
  have hza := int_toNat_cast hza0
  have hzg := int_toNat_cast hzg0
  have hzd := int_toNat_cast hzd0
  rw [hpot]
  rw [← ha', ← hg', ← hd']
  rw [← hza, ← hzg, ← hzd]
  push_cast
  rfl

theorem lllGram2_swap (b1 b2 : Fin 3 → ℝ) :
    lllGram2 b2 b1 = lllGram2 b1 b2 := by
  unfold lllGram2
  rw [lllInner_comm b2 b1]
  ring

theorem lllGramDet_swap12 (b1 b2 b3 : Fin 3 → ℝ) :
    lllGramDet b2 b1 b3 = lllGramDet b1 b2 b3 := by
  unfold lllGramDet
  rw [lllInner_comm b2 b1, lllInner_comm b1 b3, lllInner_comm b2 b3]
  ring

theorem lllGramDet_swap23 (b1 b2 b3 : Fin 3 → ℝ) :
    lllGramDet b1 b3 b2 = lllGramDet b1 b2 b3 := by
  unfold lllGramDet
  rw [lllInner_comm b2 b3, lllInner_comm b1 b2, lllInner_comm b1 b3]
  ring

theorem lllGram2_b1_b3 (b1 b2 b3 : Fin 3 → ℝ)
    (ha : lllNormSq b1 ≠ 0) :
    lllGram2 b1 b3 =
      lllNormSq b1 *
        lllNormSq (fun i =>
          lllB3s b1 b2 b3 i + lllMu32 b1 b2 b3 * lllB2s b1 b2 i) := by
  have hw :
      (fun i => b3 i - lllMu31 b1 b3 * b1 i) =
        fun i =>
          lllB3s b1 b2 b3 i + lllMu32 b1 b2 b3 * lllB2s b1 b2 i := by
    ext i
    unfold lllB3s
    ring
  have hnorm :
      lllNormSq (fun i => b3 i - lllMu31 b1 b3 * b1 i) =
        lllNormSq b3 - lllInner b3 b1 ^ 2 / lllNormSq b1 := by
    have hexp := lllNormSq_sub_smul b3 b1 (lllMu31 b1 b3)
    unfold lllMu31 at hexp ⊢
    rw [hexp]
    field_simp [ha]
    unfold lllNormSq
    ring
  unfold lllGram2
  rw [← hw, hnorm]
  field_simp [ha]
  rw [lllInner_comm b3 b1]
  ring

theorem lllPotential_swap12_eq
    {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0)
    (hb2 : lllNormSq b2 ≠ 0) :
    lllBasisPotential b2 b1 b3 =
      (lllNormSq b2 / lllNormSq b1) * lllBasisPotential b1 b2 b3 := by
  have hg' : lllGram2 b2 b1 ≠ 0 := by
    rw [lllGram2_swap]; exact hg
  have hD := lllBasisPotential_eq_prod (b3 := b3) ha hg
  have hD' := lllBasisPotential_eq_prod (b1 := b2) (b2 := b1) (b3 := b3) hb2 hg'
  rw [hD, hD', lllGram2_swap, lllGramDet_swap12]
  field_simp [ha, hb2]
  ring

theorem lllPotential_swap23_eq
    {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0)
    (hg13 : lllGram2 b1 b3 ≠ 0) :
    lllBasisPotential b1 b3 b2 =
      (lllNormSq
          (fun i =>
            lllB3s b1 b2 b3 i + lllMu32 b1 b2 b3 * lllB2s b1 b2 i) /
        lllNormSq (lllB2s b1 b2)) *
        lllBasisPotential b1 b2 b3 := by
  have hD := lllBasisPotential_eq_prod (b3 := b3) ha hg
  have hD' := lllBasisPotential_eq_prod (b2 := b3) (b3 := b2) ha hg13
  have h2 := lllB2s_normSq (b2 := b2) ha
  have hL := lllGram2_b1_b3 b1 b2 b3 ha
  rw [hD, hD', lllGramDet_swap23, h2, hL]
  field_simp [ha, hg]
  ring

theorem lll_nat_lt_of_factor
    {m n : ℕ} {D' : ℝ}
    (hm : (m : ℝ) = D')
    (hn : 0 < n)
    (hfactor : D' < (3 / 4 : ℝ) * (n : ℝ)) :
    m < n := by
  have hlt : (m : ℝ) < (n : ℝ) := by
    rw [hm]
    have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
    have h34 : (3 / 4 : ℝ) * (n : ℝ) < n := by nlinarith [hnR]
    exact lt_trans hfactor h34
  exact Nat.cast_lt.mp hlt

theorem lllBasisPotential_pos
    {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (hgen : lllGenerates A B b1 b2 b3)
    (_h1 : lllCoordInt b1) (_h2 : lllCoordInt b2) (_h3 : lllCoordInt b3) :
    0 < lllBasisPotential b1 b2 b3 := by
  have ha := lllGenerates_normSq_b1_ne hgen
  have hg := lllGenerates_gram2_ne hgen
  rw [lllBasisPotential_eq_prod (b3 := b3) ha hg]
  have ha0 : 0 < lllNormSq b1 :=
    lt_of_le_of_ne (lllNormSq_nonneg _) ha.symm
  have hg0 : 0 < lllGram2 b1 b2 :=
    lt_of_le_of_ne (lllGram2_nonneg _ _) hg.symm
  have hdet0 : lllGramDet b1 b2 b3 ≠ 0 := by
    intro h0
    have hmul := lllB3s_normSq_mul_gram2 (b3 := b3) ha hg
    have hb3s : lllNormSq (lllB3s b1 b2 b3) = 0 := by
      nlinarith [hmul, h0, lllGram2_nonneg b1 b2, lllNormSq_nonneg (lllB3s b1 b2 b3)]
    -- det M = 0 if b3s = 0 and we already have independence of first two?
    -- Use: D = a * gram2 * detG = 0 would contradict later; prove detG > 0
    -- from (det M)^2 identity is hard here; instead use generates det ≠ 0
    -- and detG = 0 ⇒ columns of GS dependent ⇒ original dependent.
    have hb3s0 : lllB3s b1 b2 b3 = 0 := (lllNormSq_eq_zero_iff _).mp hb3s
    have hb3 :
        b3 =
          fun i =>
            lllMu31 b1 b3 * b1 i + lllMu32 b1 b2 b3 * lllB2s b1 b2 i := by
      ext i
      have hi := congrArg (fun v : Fin 3 → ℝ => v i) hb3s0
      simp [lllB3s] at hi
      linarith
    have hb2 := lllB2_eq_gs b1 b2
    have : (lllColMatrix b1 b2 b3).det = 0 := by
      rw [Matrix.det_fin_three]
      have col0 (i : Fin 3) : lllColMatrix b1 b2 b3 i 0 = b1 i := by
        simp [lllColMatrix]
      have col1 (i : Fin 3) : lllColMatrix b1 b2 b3 i 1 =
          lllB2s b1 b2 i + lllMu21 b1 b2 * b1 i := by
        simp [lllColMatrix]
        exact congrArg (fun v : Fin 3 → ℝ => v i) hb2
      have col2 (i : Fin 3) : lllColMatrix b1 b2 b3 i 2 =
          lllMu31 b1 b3 * b1 i + lllMu32 b1 b2 b3 * lllB2s b1 b2 i := by
        simp [lllColMatrix]
        exact congrArg (fun v : Fin 3 → ℝ => v i) hb3
      rw [col0 0, col0 1, col0 2, col1 0, col1 1, col1 2, col2 0, col2 1, col2 2]
      ring
    exact lllGenerates_det_ne hgen this
  have hdetpos : 0 < lllGramDet b1 b2 b3 :=
    lt_of_le_of_ne (by
      have hmul := lllB3s_normSq_mul_gram2 (b3 := b3) ha hg
      rw [← hmul]
      exact mul_nonneg (lllNormSq_nonneg _) (lllGram2_nonneg _ _))
      hdet0.symm
  exact mul_pos (mul_pos ha0 hg0) hdetpos

theorem lll_exists_reduced_of_potential
    (A B : ℕ) (n : ℕ)
    (b1 b2 b3 : Fin 3 → ℝ)
    (hmem1 : mem_LLL_lattice A B b1)
    (hmem2 : mem_LLL_lattice A B b2)
    (hmem3 : mem_LLL_lattice A B b3)
    (hgen : lllGenerates A B b1 b2 b3)
    (hint1 : lllCoordInt b1)
    (hint2 : lllCoordInt b2)
    (hint3 : lllCoordInt b3)
    (hpot : (n : ℝ) = lllBasisPotential b1 b2 b3)
    (hn : 0 < n) :
    ∃ b1' b2' b3' : Fin 3 → ℝ,
      mem_LLL_lattice A B b1' ∧
        mem_LLL_lattice A B b2' ∧
          mem_LLL_lattice A B b3' ∧
            lllGenerates A B b1' b2' b3' ∧
              lllIsReducedBasis b1' b2' b3' := by
  induction n using Nat.strong_induction_on generalizing b1 b2 b3 with
  | h n ih =>
    have ha := lllGenerates_normSq_b1_ne hgen
    let b2r := lllSizeReduce2 b1 b2
    let b3r := lllSizeReduce3 b1 b2r b3
    have hmem2r : mem_LLL_lattice A B b2r := lllSizeReduce2_mem hmem1 hmem2
    have hmem3r : mem_LLL_lattice A B b3r :=
      lllSizeReduce3_mem hmem1 hmem2r hmem3
    have hint2r : lllCoordInt b2r := lllSizeReduce2_coordInt hint1 hint2
    have hint3r : lllCoordInt b3r :=
      lllSizeReduce3_coordInt hint1 hint2r hint3
    have hgenr : lllGenerates A B b1 b2r b3r :=
      lllGenerates_sizeReduce3 (lllGenerates_sizeReduce2 hgen)
    have ha' := lllGenerates_normSq_b1_ne hgenr
    have hg' := lllGenerates_gram2_ne hgenr
    have hpot_r : lllBasisPotential b1 b2r b3r = lllBasisPotential b1 b2 b3 := by
      have hb2s : lllB2s b1 b2r = lllB2s b1 b2 := lllB2s_sizeReduce b1 b2
      have hb3s_mid : lllB3s b1 b2r b3r = lllB3s b1 b2r b3 := by
        change lllB3s b1 b2r (lllSizeReduce3 b1 b2r b3) = lllB3s b1 b2r b3
        exact lllB3s_sizeReduce3 ha' hg'
      have hb3s : lllB3s b1 b2r b3 = lllB3s b1 b2 b3 := by
        change lllB3s b1 (lllSizeReduce2 b1 b2) b3 = lllB3s b1 b2 b3
        exact lllB3s_sizeReduce2 b1 b2 b3
      unfold lllBasisPotential
      rw [hb2s, hb3s_mid, hb3s]
    have hsize :
        LLL_size_reduced (lllMu21 b1 b2r) (lllMu31 b1 b3r)
          (lllMu32 b1 b2r b3r) :=
      ⟨lllMu21_sizeReduce_le b1 b2 ha,
        lllMu31_sizeReduce3_le (b2 := b2r) ha',
        lllMu32_sizeReduce3_le ha' hg'⟩
    by_cases h12 :
        (3 / 4 : ℝ) * lllNormSq b1 ≤
          lllNormSq (fun i =>
            lllB2s b1 b2r i + lllMu21 b1 b2r * b1 i)
    · by_cases h23 :
          (3 / 4 : ℝ) * lllNormSq (lllB2s b1 b2r) ≤
            lllNormSq (fun i =>
              lllB3s b1 b2r b3r i +
                lllMu32 b1 b2r b3r * lllB2s b1 b2r i)
      · refine ⟨b1, b2r, b3r, hmem1, hmem2r, hmem3r, hgenr, ?_⟩
        exact ⟨hsize, h12, h23⟩
      · have hfail : lllNormSq (fun i =>
            lllB3s b1 b2r b3r i +
              lllMu32 b1 b2r b3r * lllB2s b1 b2r i) <
            (3 / 4 : ℝ) * lllNormSq (lllB2s b1 b2r) :=
          lt_of_not_ge h23
        have hb2s_ne : lllNormSq (lllB2s b1 b2r) ≠ 0 := by
          rw [lllB2s_normSq ha']
          exact div_ne_zero hg' ha'
        have hgens : lllGenerates A B b1 b3r b2r :=
          lllGenerates_swap23 hgenr
        have hg13 : lllGram2 b1 b3r ≠ 0 :=
          lllGenerates_gram2_ne hgens
        obtain ⟨m, hm⟩ :=
          lllBasisPotential_nat hint1 hint3r hint2r ha' hg13
        have hmpos : 0 < m := by
          have hpos := lllBasisPotential_pos hgens hint1 hint3r hint2r
          have : (0 : ℝ) < m := by rwa [hm]
          exact Nat.cast_pos.mp this
        have hfactor :
            lllBasisPotential b1 b3r b2r <
              (3 / 4 : ℝ) * lllBasisPotential b1 b2r b3r := by
          have heq := lllPotential_swap23_eq (b3 := b3r) ha' hg' hg13
          have hfrac :
              lllNormSq
                  (fun i =>
                    lllB3s b1 b2r b3r i +
                      lllMu32 b1 b2r b3r * lllB2s b1 b2r i) /
                lllNormSq (lllB2s b1 b2r) < (3 / 4 : ℝ) :=
            (div_lt_iff
                (lt_of_le_of_ne (lllNormSq_nonneg _) hb2s_ne.symm)).mpr
              hfail
          have hDpos : 0 < lllBasisPotential b1 b2r b3r := by
            rw [hpot_r, ← hpot]
            exact Nat.cast_pos.mpr hn
          have := mul_lt_mul_of_pos_right hfrac hDpos
          rwa [heq]
        have hmlt : m < n :=
          lll_nat_lt_of_factor hm hn (by
            have := hfactor
            rwa [hpot_r, ← hpot] at this)
        exact ih m hmlt b1 b3r b2r hmem1 hmem3r hmem2r hgens
          hint1 hint3r hint2r hm hmpos
    · have hfail :
          lllNormSq (fun i =>
              lllB2s b1 b2r i + lllMu21 b1 b2r * b1 i) <
            (3 / 4 : ℝ) * lllNormSq b1 :=
        lt_of_not_ge h12
      have hb2r_eq : lllNormSq b2r =
          lllNormSq (fun i =>
            lllB2s b1 b2r i + lllMu21 b1 b2r * b1 i) := by
        have := lllB2_eq_gs b1 b2r
        rw [← this]
      have hgens : lllGenerates A B b2r b1 b3r :=
        lllGenerates_swap12 hgenr
      have hb2r_ne : lllNormSq b2r ≠ 0 :=
        lllGenerates_normSq_b1_ne hgens
      obtain ⟨m, hm⟩ :=
        lllBasisPotential_nat hint2r hint1 hint3r hb2r_ne
          (by
            rw [lllGram2_swap]
            exact hg')
      have hmpos : 0 < m := by
        have hpos := lllBasisPotential_pos hgens hint2r hint1 hint3r
        have : (0 : ℝ) < m := by rwa [hm]
        exact Nat.cast_pos.mp this
      have hfactor :
          lllBasisPotential b2r b1 b3r <
            (3 / 4 : ℝ) * lllBasisPotential b1 b2r b3r := by
        have heq := lllPotential_swap12_eq (b3 := b3r) ha' hg' hb2r_ne
        have hfrac : lllNormSq b2r / lllNormSq b1 < (3 / 4 : ℝ) := by
          rw [hb2r_eq]
          exact (div_lt_iff
              (lt_of_le_of_ne (lllNormSq_nonneg _) ha'.symm)).mpr hfail
        have hDpos : 0 < lllBasisPotential b1 b2r b3r := by
          rw [hpot_r, ← hpot]
          exact Nat.cast_pos.mpr hn
        have := mul_lt_mul_of_pos_right hfrac hDpos
        rwa [heq]
      have hmlt : m < n :=
        lll_nat_lt_of_factor hm hn (by
          have := hfactor
          rwa [hpot_r, ← hpot] at this)
      exact ih m hmlt b2r b1 b3r hmem2r hmem1 hmem3r hgens
        hint2r hint1 hint3r hm hmpos

/-- Existence of an LLL-reduced generating triple for the displayed
    rank-3 lattice. Size-reduction is finite; each Lovász-failing
    swap drops the integer potential `D = d₁ d₂ d₃` by a factor
    `< 3/4`. This does **not** inhabit `baker_bound_gap3`: a reduced
    first vector is short (`‖b₁‖ ≤ 2 λ₁ < 64`), so
    `baker_davenport_gs_lower` still only yields `|Λ| ≳ 10⁻³⁰`. -/
theorem lll_algorithm_terminates (A B : ℕ) :
    ∃ b1 b2 b3 : Fin 3 → ℝ,
      mem_LLL_lattice A B b1 ∧
        mem_LLL_lattice A B b2 ∧
          mem_LLL_lattice A B b3 ∧
            lllGenerates A B b1 b2 b3 ∧
              lllIsReducedBasis b1 b2 b3 := by
  have hmem1 := LLL_b1_mem A B
  have hmem2 := LLL_b2_mem A B
  have hmem3 := LLL_b3_mem A B
  have hgen := LLL_displayed_generates A B
  have hint1 := LLL_b1_coord_int A
  have hint2 := LLL_b2_coord_int B
  have hint3 := LLL_b3_coord_int
  have ha := lllGenerates_normSq_b1_ne hgen
  have hg := lllGenerates_gram2_ne hgen
  obtain ⟨n, hn⟩ := lllBasisPotential_nat hint1 hint2 hint3 ha hg
  have hnpos : 0 < n := by
    have hpos := lllBasisPotential_pos hgen hint1 hint2 hint3
    have : (0 : ℝ) < n := by rwa [hn]
    exact Nat.cast_pos.mp this
  exact lll_exists_reduced_of_potential A B n (LLL_b1 A) (LLL_b2 B) LLL_b3
    hmem1 hmem2 hmem3 hgen hint1 hint2 hint3 hn hnpos

/-- For an LLL-reduced generating triple, every nonzero lattice
    vector `x` satisfies `‖x‖ ≥ 2^{-(n-1)/2} ‖b₁‖`. For `n = 3`
    this is `‖x‖ ≥ ‖b₁‖ / 2`. -/
theorem lll_reduced_first_vec_le_lattice_vec
    (A B : ℕ) {b1 b2 b3 x : Fin 3 → ℝ}
    (hgen : lllGenerates A B b1 b2 b3)
    (hred : lllIsReducedBasis b1 b2 b3)
    (hxmem : mem_LLL_lattice A B x)
    (hxne : x ≠ 0) :
    lllNorm b1 / 2 ≤ lllNorm x := by
  have ha_ne : lllNormSq b1 ≠ 0 := lllGenerates_normSq_b1_ne hgen
  have hg_ne : lllGram2 b1 b2 ≠ 0 := lllGenerates_gram2_ne hgen
  have ha : 0 < lllNormSq b1 :=
    lt_of_le_of_ne (lllNormSq_nonneg b1) ha_ne.symm
  obtain ⟨cx, cy, cz, hxyz⟩ := hgen x hxmem
  have hnz : ¬ (cx = 0 ∧ cy = 0 ∧ cz = 0) := by
    intro h0
    apply hxne
    rw [hxyz]
    rcases h0 with ⟨hx0, hy0, hz0⟩
    ext i
    simp [lllZspan, hx0, hy0, hz0]
  have h12 : lllInner b1 (lllB2s b1 b2) = 0 := by
    have := lllB2s_orth (b2 := b2) ha_ne
    rwa [lllInner_comm]
  have h13 : lllInner b1 (lllB3s b1 b2 b3) = 0 := by
    have := lllB3s_orth_b1 (b2 := b2) (b3 := b3) ha_ne
    rwa [lllInner_comm]
  have h23 : lllInner (lllB2s b1 b2) (lllB3s b1 b2 b3) = 0 := by
    have := lllB3s_orth_b2s (b3 := b3) ha_ne hg_ne
    rwa [lllInner_comm]
  have hhalf :=
    lll_reduced_gs_half
      (lllB2s_orth (b2 := b2) ha_ne)
      (lllB3s_orth_b2s (b3 := b3) ha_ne hg_ne) hred
  have :=
    lll_zspan_norm_ge_half (rfl : b1 = b1) (lllB2_eq_gs b1 b2)
      (lllB3_eq_gs b1 b2 b3) h12 h13 h23 hhalf ha hnz
  rwa [hxyz]

/-- Displayed LLL-reduced generating first vector:
    `‖b₁‖ ≤ 2^{(n-1)/2} λ₁`. For `n = 3` this is `‖b₁‖ ≤ 2 λ₁`.
    Not the false claim that every lattice vector is short. -/
theorem lll_svt_bound (A B : ℕ) {b1 b2 b3 : Fin 3 → ℝ}
    (_hmem : mem_LLL_lattice A B b1)
    (hgen : lllGenerates A B b1 b2 b3)
    (hred : lllIsReducedBasis b1 b2 b3) :
    lllNorm b1 ≤ 2 * LLL_lambda1 A B := by
  have hlb : ∀ r ∈ LLL_nonzero_norms A B, lllNorm b1 / 2 ≤ r := by
    intro r ⟨v, hvmem, hvne, heq⟩
    rw [heq]
    exact lll_reduced_first_vec_le_lattice_vec A B hgen hred hvmem hvne
  have hinf : lllNorm b1 / 2 ≤ LLL_lambda1 A B :=
    le_csInf ⟨lllNorm (LLL_v A B), LLL_v_mem_norms A B⟩ hlb
  have hmul : lllNorm b1 ≤ LLL_lambda1 A B * 2 :=
    (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hinf
  linarith [hmul]

theorem matrix_det_int_of_int_entries
    (M : Matrix (Fin 3) (Fin 3) ℝ)
    (h : ∀ i j : Fin 3, ∃ z : ℤ, M i j = z) :
    ∃ z : ℤ, M.det = z := by
  obtain ⟨a00, h00⟩ := h 0 0
  obtain ⟨a01, h01⟩ := h 0 1
  obtain ⟨a02, h02⟩ := h 0 2
  obtain ⟨a10, h10⟩ := h 1 0
  obtain ⟨a11, h11⟩ := h 1 1
  obtain ⟨a12, h12⟩ := h 1 2
  obtain ⟨a20, h20⟩ := h 2 0
  obtain ⟨a21, h21⟩ := h 2 1
  obtain ⟨a22, h22⟩ := h 2 2
  refine ⟨a00 * a11 * a22 - a00 * a12 * a21 - a01 * a10 * a22
      + a01 * a12 * a20 + a02 * a10 * a21 - a02 * a11 * a20, ?_⟩
  rw [Matrix.det_fin_three, h00, h01, h02, h10, h11, h12, h20, h21, h22]
  norm_cast

theorem lllBasis_eq_col_mul_int {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (hgen : lllGenerates A B b1 b2 b3) :
    ∃ U : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, ∃ z : ℤ, U i j = z) ∧
        LLL_basisMatrix A B = lllColMatrix b1 b2 b3 * U := by
  obtain ⟨x1, y1, z1, e1⟩ := hgen (LLL_b1 A) (LLL_b1_mem A B)
  obtain ⟨x2, y2, z2, e2⟩ := hgen (LLL_b2 B) (LLL_b2_mem A B)
  obtain ⟨x3, y3, z3, e3⟩ := hgen LLL_b3 (LLL_b3_mem A B)
  let U : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    if j = 0 then
      (if i = 0 then (x1 : ℝ) else if i = 1 then (y1 : ℝ) else (z1 : ℝ))
    else if j = 1 then
      (if i = 0 then (x2 : ℝ) else if i = 1 then (y2 : ℝ) else (z2 : ℝ))
    else
      (if i = 0 then (x3 : ℝ) else if i = 1 then (y3 : ℝ) else (z3 : ℝ))
  refine ⟨U, ?_, ?_⟩
  · intro i j
    fin_cases j
    · fin_cases i
      · exact ⟨x1, by simp [U]⟩
      · exact ⟨y1, by simp [U]⟩
      · exact ⟨z1, by simp [U]⟩
    · fin_cases i
      · exact ⟨x2, by simp [U]⟩
      · exact ⟨y2, by simp [U]⟩
      · exact ⟨z2, by simp [U]⟩
    · fin_cases i
      · exact ⟨x3, by simp [U]⟩
      · exact ⟨y3, by simp [U]⟩
      · exact ⟨z3, by simp [U]⟩
  · ext i j
    rw [LLL_basisMatrix_col]
    unfold lllColMatrix
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases j
    · have hU0 : U 0 0 = x1 ∧ U 1 0 = y1 ∧ U 2 0 = z1 := by simp [U]
      simp [hU0.1, hU0.2.1, hU0.2.2, e1, lllZspan]
      ring
    · have hU1 : U 0 1 = x2 ∧ U 1 1 = y2 ∧ U 2 1 = z2 := by simp [U]
      simp [hU1.1, hU1.2.1, hU1.2.2, e2, lllZspan]
      ring
    · have hU2 : U 0 2 = x3 ∧ U 1 2 = y3 ∧ U 2 2 = z3 := by simp [U]
      simp [hU2.1, hU2.2.1, hU2.2.2, e3, lllZspan]
      ring

theorem lllCol_eq_basis_mul_int {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (h1 : mem_LLL_lattice A B b1) (h2 : mem_LLL_lattice A B b2)
    (h3 : mem_LLL_lattice A B b3) :
    ∃ V : Matrix (Fin 3) (Fin 3) ℝ,
      (∀ i j, ∃ z : ℤ, V i j = z) ∧
        lllColMatrix b1 b2 b3 = LLL_basisMatrix A B * V := by
  obtain ⟨x1, y1, z1, e1⟩ := h1
  obtain ⟨x2, y2, z2, e2⟩ := h2
  obtain ⟨x3, y3, z3, e3⟩ := h3
  let V : Matrix (Fin 3) (Fin 3) ℝ := fun i j =>
    if j = 0 then
      (if i = 0 then (x1 : ℝ) else if i = 1 then (y1 : ℝ) else (z1 : ℝ))
    else if j = 1 then
      (if i = 0 then (x2 : ℝ) else if i = 1 then (y2 : ℝ) else (z2 : ℝ))
    else
      (if i = 0 then (x3 : ℝ) else if i = 1 then (y3 : ℝ) else (z3 : ℝ))
  refine ⟨V, ?_, ?_⟩
  · intro i j
    fin_cases j
    · fin_cases i
      · exact ⟨x1, by simp [V]⟩
      · exact ⟨y1, by simp [V]⟩
      · exact ⟨z1, by simp [V]⟩
    · fin_cases i
      · exact ⟨x2, by simp [V]⟩
      · exact ⟨y2, by simp [V]⟩
      · exact ⟨z2, by simp [V]⟩
    · fin_cases i
      · exact ⟨x3, by simp [V]⟩
      · exact ⟨y3, by simp [V]⟩
      · exact ⟨z3, by simp [V]⟩
  · ext i j
    rw [LLL_basisMatrix_col]
    unfold lllColMatrix
    rw [Matrix.mul_apply, Fin.sum_univ_three]
    fin_cases j
    · have hV0 : V 0 0 = x1 ∧ V 1 0 = y1 ∧ V 2 0 = z1 := by simp [V]
      simp [hV0.1, hV0.2.1, hV0.2.2, e1, LLL_span]
      ring
    · have hV1 : V 0 1 = x2 ∧ V 1 1 = y2 ∧ V 2 1 = z2 := by simp [V]
      simp [hV1.1, hV1.2.1, hV1.2.2, e2, LLL_span]
      ring
    · have hV2 : V 0 2 = x3 ∧ V 1 2 = y3 ∧ V 2 2 = z3 := by simp [V]
      simp [hV2.1, hV2.2.1, hV2.2.2, e3, LLL_span]
      ring

/-- A generating lattice triple has `|det M| = C`. -/
theorem lllCol_abs_det_eq_C {A B : ℕ} {b1 b2 b3 : Fin 3 → ℝ}
    (h1 : mem_LLL_lattice A B b1) (h2 : mem_LLL_lattice A B b2)
    (h3 : mem_LLL_lattice A B b3) (hgen : lllGenerates A B b1 b2 b3) :
    |(lllColMatrix b1 b2 b3).det| = LLL_C_real := by
  obtain ⟨U, hUint, hU⟩ := lllBasis_eq_col_mul_int hgen
  obtain ⟨V, hVint, hV⟩ := lllCol_eq_basis_mul_int h1 h2 h3
  obtain ⟨u, hu⟩ := matrix_det_int_of_int_entries U hUint
  obtain ⟨v, hv⟩ := matrix_det_int_of_int_entries V hVint
  have hCU : LLL_C_real = (lllColMatrix b1 b2 b3).det * U.det := by
    have := congrArg Matrix.det hU
    rw [LLL_basis_det, Matrix.det_mul] at this
    exact this
  have hCV : (lllColMatrix b1 b2 b3).det = LLL_C_real * V.det := by
    have := congrArg Matrix.det hV
    rw [Matrix.det_mul, LLL_basis_det] at this
    exact this
  have hprod : (u : ℝ) * v = 1 := by
    have hmid :
        (lllColMatrix b1 b2 b3).det * U.det =
          (LLL_C_real * V.det) * U.det := by
      rw [hCV]
    have hC1 : LLL_C_real = LLL_C_real * (V.det * U.det) := by
      nth_rw 1 [hCU]
      rw [hmid]
      ring
    have hone : (1 : ℝ) = V.det * U.det := by
      have hC := ne_of_gt LLL_C_real_pos
      have h' : LLL_C_real * 1 = LLL_C_real * (V.det * U.det) := by
        rw [mul_one]
        exact hC1
      exact mul_left_cancel₀ hC h'
    rw [hu, hv, mul_comm] at hone
    exact hone.symm
  have h1z : (u * v : ℤ) = 1 := by
    exact_mod_cast hprod
  have huunit : u = 1 ∨ u = -1 :=
    Int.eq_one_or_neg_one_of_mul_eq_one h1z
  have hCpos : 0 < LLL_C_real := LLL_C_real_pos
  rcases huunit with hu1 | hu1
  · have : (lllColMatrix b1 b2 b3).det = LLL_C_real := by
      have h := hCU
      rw [hu, hu1, Int.cast_one, mul_one] at h
      exact h.symm
    rw [this, abs_of_pos hCpos]
  · have : (lllColMatrix b1 b2 b3).det = -LLL_C_real := by
      have h := hCU
      rw [hu, hu1, Int.cast_neg, Int.cast_one] at h
      linarith
    rw [this, abs_neg, abs_of_pos hCpos]

theorem lllCol_as_vec (b1 b2 b3 : Fin 3 → ℝ) :
    (fun k => lllColMatrix b1 b2 b3 k 0) = b1 ∧
      (fun k => lllColMatrix b1 b2 b3 k 1) = b2 ∧
        (fun k => lllColMatrix b1 b2 b3 k 2) = b3 := by
  refine ⟨?_, ?_, ?_⟩
  · ext k; simp [lllColMatrix]
  · ext k; simp [lllColMatrix]
  · ext k; simp [lllColMatrix]

theorem lllTranspose_mul_apply (b1 b2 b3 : Fin 3 → ℝ) (i j : Fin 3) :
    (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) i j =
      lllInner
        (fun k => lllColMatrix b1 b2 b3 k i)
        (fun k => lllColMatrix b1 b2 b3 k j) := by
  unfold lllInner
  rw [Matrix.mul_apply]
  simp only [Matrix.transpose_apply]

theorem lllGramDet_eq_col_det_sq (b1 b2 b3 : Fin 3 → ℝ) :
    lllGramDet b1 b2 b3 = (lllColMatrix b1 b2 b3).det ^ 2 := by
  have hpow :
      (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3).det =
        (lllColMatrix b1 b2 b3).det ^ 2 := by
    rw [Matrix.det_mul, Matrix.det_transpose]
    ring
  have hG :
      (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3).det =
        lllGramDet b1 b2 b3 := by
    have hc := lllCol_as_vec b1 b2 b3
    have a : (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) 0 0 =
        lllNormSq b1 := by
      rw [lllTranspose_mul_apply, hc.1]; rfl
    have p01 : (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) 0 1 =
        lllInner b1 b2 := by
      rw [lllTranspose_mul_apply, hc.1, hc.2.1]
    have q02 : (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) 0 2 =
        lllInner b1 b3 := by
      rw [lllTranspose_mul_apply, hc.1, hc.2.2]
    have p10 : (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) 1 0 =
        lllInner b2 b1 := by
      rw [lllTranspose_mul_apply, hc.2.1, hc.1]
    have b11 : (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) 1 1 =
        lllNormSq b2 := by
      rw [lllTranspose_mul_apply, hc.2.1]; rfl
    have r12 : (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) 1 2 =
        lllInner b2 b3 := by
      rw [lllTranspose_mul_apply, hc.2.1, hc.2.2]
    have q20 : (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) 2 0 =
        lllInner b3 b1 := by
      rw [lllTranspose_mul_apply, hc.2.2, hc.1]
    have r21 : (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) 2 1 =
        lllInner b3 b2 := by
      rw [lllTranspose_mul_apply, hc.2.2, hc.2.1]
    have c22 : (Matrix.transpose (lllColMatrix b1 b2 b3) * lllColMatrix b1 b2 b3) 2 2 =
        lllNormSq b3 := by
      rw [lllTranspose_mul_apply, hc.2.2]; rfl
    rw [Matrix.det_fin_three, a, p01, q02, p10, b11, r12, q20, r21, c22]
    have h21 : lllInner b2 b1 = lllInner b1 b2 := lllInner_comm _ _
    have h31 : lllInner b3 b1 = lllInner b1 b3 := lllInner_comm _ _
    have h32 : lllInner b3 b2 = lllInner b2 b3 := lllInner_comm _ _
    rw [h21, h31, h32]
    unfold lllGramDet lllNormSq
    ring
  linarith

theorem lll_gs_prod_eq_gramDet {b1 b2 b3 : Fin 3 → ℝ}
    (ha : lllNormSq b1 ≠ 0) (hg : lllGram2 b1 b2 ≠ 0) :
    lllNormSq b1 * lllNormSq (lllB2s b1 b2) *
        lllNormSq (lllB3s b1 b2 b3) =
      lllGramDet b1 b2 b3 := by
  have h2 := lllB2s_normSq (b2 := b2) ha
  have h3 := lllB3s_normSq_mul_gram2 (b3 := b3) ha hg
  have h3' :
      lllNormSq (lllB3s b1 b2 b3) =
        lllGramDet b1 b2 b3 / lllGram2 b1 b2 :=
    (eq_div_iff hg).mpr (by linarith [h3])
  rw [h2, h3']
  field_simp [ha, hg]

theorem lllNorm_pow_six (v : Fin 3 → ℝ) :
    lllNorm v ^ 6 = lllNormSq v ^ 3 := by
  unfold lllNorm
  have hnn := lllNormSq_nonneg v
  have hsq : Real.sqrt (lllNormSq v) ^ 2 = lllNormSq v := Real.sq_sqrt hnn
  have hpow : Real.sqrt (lllNormSq v) ^ 6 =
      (Real.sqrt (lllNormSq v) ^ 2) ^ 3 := by
    rw [← pow_mul]
  rw [hpow, hsq]

theorem lll_det_bound_rhs_pow_six :
    (Real.sqrt 2 * LLL_C_real ^ ((1 : ℝ) / 3)) ^ 6 =
      8 * LLL_C_real ^ 2 := by
  rw [mul_pow]
  have h2 : Real.sqrt 2 ^ 6 = 8 := by
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hpow : Real.sqrt 2 ^ 6 = (Real.sqrt 2 ^ 2) ^ 3 := by
      rw [← pow_mul]
    rw [hpow, hsq]
    norm_num
  have hx : 0 ≤ LLL_C_real := le_of_lt LLL_C_real_pos
  have hC : (LLL_C_real ^ ((1 : ℝ) / 3)) ^ 6 = LLL_C_real ^ 2 := by
    rw [← Real.rpow_natCast LLL_C_real 2]
    rw [← Real.rpow_mul_natCast hx ((1 : ℝ) / 3) 6]
    congr 1
    norm_num
  rw [h2, hC]

/-- Displayed LLL-reduced generating first vector:
    `‖b₁‖ ≤ 2^{(n-1)/4} det(L)^{1/n}`. For `n = 3` and
    `det = C` this is `‖b₁‖ ≤ √2 · C^{1/3}`. For `C = 10³⁰`
    this is `≈ 2.8e10`, an *upper* bound, much larger than
    `‖v‖ < 32`. Not a `B ≤ 10⁶` cutoff. -/
theorem lll_det_bound (A B : ℕ) {b1 b2 b3 : Fin 3 → ℝ}
    (h1 : mem_LLL_lattice A B b1) (h2 : mem_LLL_lattice A B b2)
    (h3 : mem_LLL_lattice A B b3) (hgen : lllGenerates A B b1 b2 b3)
    (hred : lllIsReducedBasis b1 b2 b3) :
    lllNorm b1 ≤ Real.sqrt 2 * LLL_C_real ^ ((1 : ℝ) / 3) := by
  have ha_ne : lllNormSq b1 ≠ 0 := lllGenerates_normSq_b1_ne hgen
  have hg_ne : lllGram2 b1 b2 ≠ 0 := lllGenerates_gram2_ne hgen
  have hprod :=
    lll_det_prod_sq_of_reduced
      (lllB2s_orth (b2 := b2) ha_ne)
      (lllB3s_orth_b2s (b3 := b3) ha_ne hg_ne) hred
  have hgs := lll_gs_prod_eq_gramDet (b3 := b3) ha_ne hg_ne
  have hG := lllGramDet_eq_col_det_sq b1 b2 b3
  have habs := lllCol_abs_det_eq_C h1 h2 h3 hgen
  have hsq : (lllColMatrix b1 b2 b3).det ^ 2 = LLL_C_real ^ 2 := by
    rw [← sq_abs, habs]
  have hN3 : lllNormSq b1 ^ 3 ≤ 8 * LLL_C_real ^ 2 := by
    have hstep :
        8 * (lllNormSq b1 * lllNormSq (lllB2s b1 b2) *
            lllNormSq (lllB3s b1 b2 b3)) =
          8 * LLL_C_real ^ 2 := by
      rw [hgs, hG, hsq]
    exact hprod.trans (le_of_eq hstep)
  have hleft := lllNorm_pow_six b1
  have hright := lll_det_bound_rhs_pow_six
  have hpow :
      lllNorm b1 ^ 6 ≤
        (Real.sqrt 2 * LLL_C_real ^ ((1 : ℝ) / 3)) ^ 6 := by
    rw [hleft, hright]
    exact hN3
  have ha0 : 0 ≤ lllNorm b1 := lllNorm_nonneg b1
  have hb0 : 0 ≤ Real.sqrt 2 * LLL_C_real ^ ((1 : ℝ) / 3) :=
    mul_nonneg (Real.sqrt_nonneg _)
      (Real.rpow_nonneg (le_of_lt LLL_C_real_pos) _)
  exact (pow_le_pow_iff_left ha0 hb0 (by norm_num : (6 : ℕ) ≠ 0)).mp hpow

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

/-- On a gap-3 solution with `B > 10⁶`, any Baker–Davenport
    witness `17 < r ≤ |v₃|` lies in `(17, 18)`, so
    `(r − 17)/C < 1/C = 10⁻³⁰ < 1/B0 = 10⁻⁶`. Compatible with
    `|Λ| < 1/B`; not a `B ≤ 10⁶` cutoff. -/
theorem baker_davenport_no_cutoff
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B)
    (r : ℝ) (hle : r ≤ |LLL_v A B 2|) (h17 : 17 < r) :
    r < 18 ∧
      (r - 17) / LLL_C_real < 1 / LLL_C_real ∧
        (1 : ℝ) / LLL_C_real < 1 / (B0_nat : ℝ) ∧
          (r - 17) / LLL_C_real ≤ |Lambda A B| ∧
            |Lambda A B| < 1 / (B : ℝ) := by
  have ht := LLL_v_third_abs_lt_eighteen hsol hB hB0
  have hrlt : r < 18 := lt_of_le_of_lt hle ht
  have hC := LLL_C_real_pos
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hquot : (r - 17) / LLL_C_real < 1 / LLL_C_real := by
    rw [div_lt_div_iff hC hC, one_mul]
    nlinarith [hrlt, hC]
  have hC_lt_B0 : (1 : ℝ) / LLL_C_real < 1 / (B0_nat : ℝ) := by
    rw [div_lt_div_iff hC hB0pos]
    simp only [one_mul]
    rw [LLL_C_real_eq, B0_nat_eq]
    have : ((1000000 : ℕ) : ℝ) < (10 : ℝ) ^ 30 := by norm_num
    exact this
  have hBD := baker_davenport_gs_lower A B r hle h17
  have hupper := abs_Lambda_le_inv_B hsol hB
  exact ⟨hrlt, hquot, hC_lt_B0, hBD, hupper⟩

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
#check lllPotential_swap12_factor_lt
#check LLL_b1_normSq_nat
#check abs_sub_lllNearestInt
#check lll_reduced_gs_half
#check lll_svt_bound_of_reduced
#check lll_det_prod_sq_of_reduced
#check lllIsReducedBasis
#check lllBasisPotential
#check lllGenerates
#check lll_algorithm_terminates
#check lll_svt_bound
#check lll_det_bound
#check lll_gs_lower_half_pow
#check lll_vec_normSq_ge_star
#check lll_reduced_first_vec_le_lattice_vec
#check baker_davenport_gs_lower
#check baker_davenport_no_cutoff
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
#print axioms lllPotential_swap12_factor_lt
#print axioms lll_svt_bound_of_reduced
#print axioms baker_davenport_gs_lower
#print axioms lll_algorithm_terminates
#print axioms lll_svt_bound
#print axioms lll_det_bound
#print axioms baker_davenport_no_cutoff
#print axioms baker_bound_gap3_of_from_ratio

end BealMatveevBeal.MatveevLLL
