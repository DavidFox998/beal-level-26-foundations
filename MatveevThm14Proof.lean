/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Importable copy of `Beal/Matveev/MatveevThm14Proof.lean`.
  Lake's LEAN_PATH puts the relocated kernel's `Beal/` prefix first, so
  `Beal.Matveev.*` cannot be imported from other modules. This root
  module is the same namespace `BealMatveevBeal.MatveevThm14Proof`.
-/
import Mathlib
import BealLevel26Foundations.Beal.FullProof.BealMatveevConstants
import BealLevel26Foundations.Beal.FullProof.BealMatveevInequality
import BealLevel26Foundations.Beal.FullProof.BealMatveevThm14
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

/-!
# Integer gap for the displayed Matveev 2000 n=2 RHS

Matveev 2000 Theorem 1.4 (n=2, D=1, κ=1) is an algebraic-number lower
bound on `|b₁ log α₁ + b₂ log α₂|`, proved via interpolation determinants,
multiplicity estimates, and Kummer theory (Matveev, Izv. Math. 64 (2000)).
Mathlib 4.12 has no such theorem. This file does **not** formalise that
interpolation, and it does **not** inhabit the bare-real statement

  `∀ A B : ℝ, 1 < A → 1 < B+3 → Λ ≠ 0 → |Λ| > exp(−C₁ A₁ A₂ B₀)`

which is false: a real `A` can hug `(B+3)^{13/4}` and make `|Λ|` smaller
than any `exp(−C (log)³)`.

What it **does** prove, with axioms only `[propext, Classical.choice, Quot.sound]`,
is the **integer gap** that the same numerical RHS is smaller than `|Λ|`
whenever `A` and `B+3` are integers `> 1` and `A⁴ ≠ (B+3)¹³`:

* `|4 log A − 13 log C| = |log(A⁴) − log(C¹³)| ≥ 1 / max(A⁴, C¹³)`
  because distinct positive integers are at least distance 1 apart and
  `1 − x⁻¹ ≤ log x` (Mathlib `Real.one_sub_inv_le_log_of_pos`);
* `log(max(A⁴, C¹³)) ≤ 13 · (log A + log C) < 13 · B0_term`;
* `C1_floor · log A · log C > 13` because `log 2 > 1/2` and
  `C1_floor / 4 > 13`.

On a gap-3 solution this is `matveev_general_on_gap3` **without** `hGen`.
`BealMatveevBeal.matveev_gap3_lower` uses it for the **B≤10^6** uniform
bound. That does **not** inhabit unrestricted
`matveev_theorem_1_4_gap3_target` (the product is still
`O((log(B+3))³)` and does not beat `B⁴/A⁴` for large `B`) and does
**not** inhabit `baker_bound_gap3`. Not v25.
-/

noncomputable section

open Real
open BealLevel26Foundations.BealMatveevConstants
open BealLevel26Foundations.BealMatveevInequality
open BealLevel26Foundations.BealMatveevThm14
open BealLevel26Foundations.BealGap3BakerUpperBound

namespace BealMatveevBeal.MatveevThm14Proof

/-- Same numeric floor as `BealMatveevBeal.C1_floor` (Matveev 2000 n=2 after Bugeaud). -/
def C1_floor : ℕ := 143186215390

def C1_floor_real : ℝ := (C1_floor : ℝ)

/-- Same height as `BealMatveevBeal.height_B0_nat` (`C1_floor * 30^6`). -/
def height_B0_nat : ℕ := 104382751019310000000

theorem C1_floor_eq_level26 : C1_floor = matveev_C1_floor := rfl

theorem height_B0_nat_eq_level26 : height_B0_nat = matveev_height_B0 := rfl

theorem C1_floor_numeral : C1_floor = 143186215390 := rfl

theorem height_B0_nat_numeral : height_B0_nat = 104382751019310000000 := rfl

/-- `B0_term` of Matveev 2000 n=2 with `B = 13` and heights `A₁ = log A`, `A₂ = log C`. -/
def B0_term (A C : ℝ) : ℝ :=
  log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C

lemma log_thirteen_gt_one : (1 : ℝ) < log (13 : ℝ) := by
  have hexp : Real.exp 1 < (13 : ℝ) :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  exact (Real.lt_log_iff_exp_lt (by norm_num : (0 : ℝ) < 13)).2 hexp

/-- `log 2 > 1/2`. -/
theorem log_two_gt_half : (1 / 2 : ℝ) < log 2 :=
  lt_trans (by norm_num) Real.log_two_gt_d9

/-- Positive integers `≥ 2` have `log n > 1/2`. -/
theorem log_nat_gt_half {n : ℕ} (hn : 1 < n) : (1 / 2 : ℝ) < log n := by
  have h2 : (2 : ℕ) ≤ n := Nat.succ_le_of_lt hn
  have hle : log 2 ≤ log n :=
    Real.log_le_log (by norm_num) (by exact_mod_cast h2)
  exact lt_of_lt_of_le log_two_gt_half hle

/-- `C1_floor / 4 > 13`. -/
theorem C1_div_four_gt_thirteen : (13 : ℝ) < (C1_floor : ℝ) / 4 := by
  have : (13 : ℝ) * 4 < (C1_floor : ℝ) := by
    norm_num [C1_floor]
  linarith

theorem C1_floor_real_pos : (0 : ℝ) < C1_floor_real := by
  unfold C1_floor_real C1_floor
  norm_num

/-- For integers `A > 1` and `C > 1`, the product `C1 · log A · log C` exceeds 13. -/
theorem C1_mul_logs_gt_thirteen (A C : ℕ) (hA : 1 < A) (hC : 1 < C) :
    (13 : ℝ) < C1_floor_real * log A * log C := by
  have hA2 := log_nat_gt_half hA
  have hC2 := log_nat_gt_half hC
  have hCpos := C1_floor_real_pos
  have hApos : (0 : ℝ) < log A := lt_trans (by norm_num) hA2
  have hprod : (1 / 4 : ℝ) < log A * log C := by
    have : (1 / 2 : ℝ) * (1 / 2) < log A * log C :=
      mul_lt_mul hA2 (le_of_lt hC2) (by norm_num) (le_of_lt hApos)
    linarith
  have hscale : C1_floor_real * (1 / 4) < C1_floor_real * (log A * log C) :=
    mul_lt_mul_of_pos_left hprod hCpos
  have hC14 : C1_floor_real * (1 / 4) = C1_floor_real / 4 := by ring
  have hre : C1_floor_real * log A * log C = C1_floor_real * (log A * log C) := by
    ring
  rw [hre]
  exact lt_trans C1_div_four_gt_thirteen (hC14 ▸ hscale)

theorem B0_term_pos (A C : ℕ) (hA : 1 < A) (hC : 1 < C) :
    0 < B0_term A C := by
  have hApos : 0 < log (A : ℝ) := Real.log_pos (by exact_mod_cast hA)
  have hCpos : 0 < log (C : ℝ) := Real.log_pos (by exact_mod_cast hC)
  have h13 := log_thirteen_gt_one
  have hll : 0 < log (log (13 : ℝ)) := Real.log_pos h13
  unfold B0_term
  linarith [h13, hll, hApos, hCpos]

theorem log_add_lt_B0_term (A C : ℕ) (_hA : 1 < A) (_hC : 1 < C) :
    log A + log C < B0_term A C := by
  have h13 := log_thirteen_gt_one
  have hll : 0 < log (log (13 : ℝ)) := Real.log_pos h13
  unfold B0_term
  linarith [h13, hll]

/-- `1/M ≤ log M − log N` when `0 < N < M`. -/
theorem log_sub_ge_inv_of_lt {N M : ℕ} (hN : 0 < N) (hlt : N < M) :
    (1 : ℝ) / (M : ℝ) ≤ log M - log N := by
  have hMpos : 0 < M := Nat.lt_trans hN hlt
  have hM2 : 2 ≤ M := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt hN hlt)
  have hM1 : 1 ≤ M := le_trans (by decide : (1 : ℕ) ≤ 2) hM2
  have hNle : N ≤ M - 1 := Nat.le_sub_of_add_le (Nat.succ_le_of_lt hlt)
  have hNposR : (0 : ℝ) < N := by exact_mod_cast hN
  have hMposR : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hM1posN : 0 < M - 1 := Nat.sub_pos_of_lt (Nat.succ_le_iff.mp hM2)
  have hM1posR : (0 : ℝ) < (M - 1 : ℕ) := by exact_mod_cast hM1posN
  have hcast : ((M - 1 : ℕ) : ℝ) = (M : ℝ) - 1 := by
    rw [Nat.cast_sub hM1, Nat.cast_one]
  have hNleR : (N : ℝ) ≤ ((M - 1 : ℕ) : ℝ) := by exact_mod_cast hNle
  have hdiv : (M : ℝ) / ((M - 1 : ℕ) : ℝ) ≤ (M : ℝ) / N :=
    div_le_div_of_nonneg_left (le_of_lt hMposR) hNposR hNleR
  have hxpos : (0 : ℝ) < (M : ℝ) / ((M - 1 : ℕ) : ℝ) :=
    div_pos hMposR hM1posR
  have hlogdiv : log ((M : ℝ) / ((M - 1 : ℕ) : ℝ)) ≤ log ((M : ℝ) / N) :=
    Real.log_le_log hxpos hdiv
  have hlogMN : log ((M : ℝ) / N) = log M - log N :=
    Real.log_div hMposR.ne' hNposR.ne'
  have hone :
      (1 : ℝ) - ((M : ℝ) / ((M - 1 : ℕ) : ℝ))⁻¹ = 1 / M := by
    rw [inv_div, hcast]
    have hMne : (M : ℝ) ≠ 0 := hMposR.ne'
    field_simp [hMne]
  have hlogx : (1 : ℝ) / M ≤ log ((M : ℝ) / ((M - 1 : ℕ) : ℝ)) := by
    have := Real.one_sub_inv_le_log_of_pos hxpos
    rwa [hone] at this
  calc
    (1 : ℝ) / M ≤ log ((M : ℝ) / ((M - 1 : ℕ) : ℝ)) := hlogx
    _ ≤ log ((M : ℝ) / N) := hlogdiv
    _ = log M - log N := hlogMN

/-- Distinct positive integers satisfy `|log N − log M| ≥ 1 / max(N,M)`. -/
theorem abs_log_nat_sub_ge_inv_max {N M : ℕ} (hN : 0 < N) (hM : 0 < M)
    (hne : N ≠ M) :
    (1 : ℝ) / max (N : ℝ) (M : ℝ) ≤ |log N - log M| := by
  rcases lt_trichotomy N M with hlt | heq | hgt
  · have hmax : max (N : ℝ) (M : ℝ) = M :=
      max_eq_right (le_of_lt (by exact_mod_cast hlt : (N : ℝ) < M))
    have hlog : log (N : ℝ) < log (M : ℝ) :=
      Real.log_lt_log (by exact_mod_cast hN) (by exact_mod_cast hlt)
    rw [hmax, abs_of_nonpos (sub_nonpos.mpr (le_of_lt hlog))]
    simpa [neg_sub] using log_sub_ge_inv_of_lt hN hlt
  · exact (hne heq).elim
  · have hmax : max (N : ℝ) (M : ℝ) = N :=
      max_eq_left (le_of_lt (by exact_mod_cast hgt : (M : ℝ) < N))
    have hlog : log (M : ℝ) < log (N : ℝ) :=
      Real.log_lt_log (by exact_mod_cast hM) (by exact_mod_cast hgt)
    rw [hmax, abs_of_nonneg (sub_nonneg.mpr (le_of_lt hlog))]
    simpa [abs_sub_comm] using log_sub_ge_inv_of_lt hM hgt

theorem pow_ne_of_log_form_ne {A C : ℕ} (_hA : 1 < A) (_hC : 1 < C)
    (hΛ : 4 * log (A : ℝ) - 13 * log (C : ℝ) ≠ 0) :
    A ^ 4 ≠ C ^ 13 := by
  intro heq
  have hcast : ((A ^ 4 : ℕ) : ℝ) = ((C ^ 13 : ℕ) : ℝ) := by rw [heq]
  rw [Nat.cast_pow, Nat.cast_pow] at hcast
  have hlog : log ((A : ℝ) ^ 4) = log ((C : ℝ) ^ 13) := congrArg log hcast
  rw [Real.log_pow, Real.log_pow] at hlog
  exact hΛ (sub_eq_zero.mpr hlog)

theorem abs_log_form_ge_inv_max (A C : ℕ) (hA : 1 < A) (hC : 1 < C)
    (hΛ : 4 * log (A : ℝ) - 13 * log (C : ℝ) ≠ 0) :
    (1 : ℝ) / max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13) ≤
      |4 * log (A : ℝ) - 13 * log (C : ℝ)| := by
  have hAposN : 0 < A := Nat.zero_lt_of_lt hA
  have hCposN : 0 < C := Nat.zero_lt_of_lt hC
  have hNpos : 0 < A ^ 4 := Nat.pos_pow_of_pos 4 hAposN
  have hMpos : 0 < C ^ 13 := Nat.pos_pow_of_pos 13 hCposN
  have hne := pow_ne_of_log_form_ne hA hC hΛ
  have hgap := abs_log_nat_sub_ge_inv_max hNpos hMpos hne
  have hrew : |log ((A ^ 4 : ℕ) : ℝ) - log ((C ^ 13 : ℕ) : ℝ)| =
      |4 * log (A : ℝ) - 13 * log (C : ℝ)| := by
    rw [Nat.cast_pow, Nat.cast_pow, Real.log_pow, Real.log_pow]
    norm_cast
  have hmax : max (((A ^ 4 : ℕ) : ℝ)) (((C ^ 13 : ℕ) : ℝ)) =
      max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13) := by
    rw [Nat.cast_pow, Nat.cast_pow]
  rw [← hrew, ← hmax]
  exact hgap

theorem log_max_pow_le_thirteen_sum (A C : ℕ) (hA : 1 < A) (hC : 1 < C) :
    log (max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13)) ≤
      13 * (log (A : ℝ) + log (C : ℝ)) := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (Nat.zero_lt_of_lt hC)
  have hA1 : (1 : ℝ) < A := by exact_mod_cast hA
  have hC1 : (1 : ℝ) < C := by exact_mod_cast hC
  have hNpos : (0 : ℝ) < (A : ℝ) ^ 4 := pow_pos hApos 4
  have hMpos : (0 : ℝ) < (C : ℝ) ^ 13 := pow_pos hCpos 13
  have hlogA : 0 < log (A : ℝ) := Real.log_pos hA1
  have hlogC : 0 < log (C : ℝ) := Real.log_pos hC1
  have h4 : log ((A : ℝ) ^ 4) = 4 * log (A : ℝ) := Real.log_pow (A : ℝ) 4
  have h13 : log ((C : ℝ) ^ 13) = 13 * log (C : ℝ) := Real.log_pow (C : ℝ) 13
  have hle4 : 4 * log (A : ℝ) ≤ 13 * (log (A : ℝ) + log (C : ℝ)) := by
    nlinarith
  have hle13 : 13 * log (C : ℝ) ≤ 13 * (log (A : ℝ) + log (C : ℝ)) := by
    nlinarith
  have hlogmax :
      log (max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13)) =
        max (log ((A : ℝ) ^ 4)) (log ((C : ℝ) ^ 13)) := by
    rcases le_total ((A : ℝ) ^ 4) ((C : ℝ) ^ 13) with h | h
    · have hmx : max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13) = (C : ℝ) ^ 13 := max_eq_right h
      have hl : log ((A : ℝ) ^ 4) ≤ log ((C : ℝ) ^ 13) :=
        Real.log_le_log hNpos h
      rw [hmx, max_eq_right hl]
    · have hmx : max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13) = (A : ℝ) ^ 4 := max_eq_left h
      have hl : log ((C : ℝ) ^ 13) ≤ log ((A : ℝ) ^ 4) :=
        Real.log_le_log hMpos h
      rw [hmx, max_eq_left hl]
  rw [hlogmax, h4, h13]
  exact max_le hle4 hle13

theorem log_max_lt_height_product (A C : ℕ) (hA : 1 < A) (hC : 1 < C) :
    log (max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13)) <
      C1_floor_real * log A * log C * B0_term A C := by
  have hsum := log_max_pow_le_thirteen_sum A C hA hC
  have hB0lt := log_add_lt_B0_term A C hA hC
  have hB0pos := B0_term_pos A C hA hC
  have hC1 := C1_mul_logs_gt_thirteen A C hA hC
  have h13pos : (0 : ℝ) < 13 := by norm_num
  have hleft : 13 * (log (A : ℝ) + log (C : ℝ)) < 13 * B0_term A C :=
    mul_lt_mul_of_pos_left hB0lt h13pos
  have hright : 13 * B0_term A C < C1_floor_real * log A * log C * B0_term A C :=
    mul_lt_mul_of_pos_right hC1 hB0pos
  exact lt_of_le_of_lt hsum (lt_trans hleft hright)

/-- Integer form of the displayed Matveev n=2 bound. The bare-real
    statement without integrality of `A` and `C` is false. -/
theorem matveev_thm14_n2_explicit_of_nat
    (A C : ℕ) (hA : 1 < A) (hC : 1 < C)
    (hΛ : 4 * log (A : ℝ) - 13 * log (C : ℝ) ≠ 0) :
    |4 * log (A : ℝ) - 13 * log (C : ℝ)| >
      exp (-C1_floor_real * log A * log C *
        (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C)) := by
  have hge := abs_log_form_ge_inv_max A C hA hC hΛ
  have hApos : (0 : ℝ) < A := by exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hmaxpos : (0 : ℝ) < max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13) :=
    lt_of_lt_of_le (pow_pos hApos 4) (le_max_left _ _)
  have hprod := log_max_lt_height_product A C hA hC
  have hneg :
      -C1_floor_real * log A * log C *
        (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C) =
      -(C1_floor_real * log A * log C * B0_term A C) := by
    unfold B0_term
    ring
  have hexp :
      exp (-(C1_floor_real * log A * log C * B0_term A C)) <
        exp (-log (max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13))) :=
    Real.exp_lt_exp.mpr (neg_lt_neg hprod)
  have hinv : exp (-log (max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13))) =
      (1 : ℝ) / max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13) := by
    rw [Real.exp_neg, Real.exp_log hmaxpos, inv_eq_one_div]
  have hstrict :
      exp (-(C1_floor_real * log A * log C * B0_term A C)) <
        (1 : ℝ) / max ((A : ℝ) ^ 4) ((C : ℝ) ^ 13) :=
    hinv ▸ hexp
  rw [hneg]
  exact lt_of_lt_of_le hstrict hge

/-- Displayed Matveev 2000 Thm 1.4 n=2 bound for **integer-valued** heights.

    Extra hypotheses `∃ n, A = n` and `∃ c, B+3 = c` are required: the same
    inequality on arbitrary reals is false. This is the integer gap, not a
    formalisation of Matveev's interpolation determinant. -/
theorem matveev_thm14_n2_explicit
    (A B : ℝ) (hA : 1 < A) (hB : 1 < B + 3)
    (hΛ : 4 * log A - 13 * log (B + 3) ≠ 0)
    (hA_nat : ∃ n : ℕ, A = n)
    (hB3_nat : ∃ c : ℕ, B + 3 = c) :
    |4 * log A - 13 * log (B + 3)| >
      exp (-C1_floor_real * log A * log (B + 3) *
        (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log (B + 3))) := by
  obtain ⟨n, hn⟩ := hA_nat
  obtain ⟨c, hc⟩ := hB3_nat
  have hn1 : 1 < n := by
    have : (1 : ℝ) < (n : ℝ) := hn ▸ hA
    exact_mod_cast this
  have hc1 : 1 < c := by
    have : (1 : ℝ) < (c : ℝ) := hc ▸ hB
    exact_mod_cast this
  have hΛn : 4 * log (n : ℝ) - 13 * log (c : ℝ) ≠ 0 := by
    rw [← hn, ← hc]
    exact hΛ
  have hmain := matveev_thm14_n2_explicit_of_nat n c hn1 hc1 hΛn
  rw [hn, hc]
  exact hmain

/-- Honest gap-3 bounds. Not `A < B+3`: `eq_implies_A_gt_B` gives `B < A`. -/
theorem gap3_A_gt_one (A B : ℕ)
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    1 < A ∧ 1 < B + 3 := by
  have hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := h
  have hAgt : B < A := eq_implies_A_gt_B hsol hB
  have hAgt1 : 1 < A := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) hAgt
  have hB3 : 1 < B + 3 :=
    Nat.lt_of_lt_of_le (by decide : 1 < 4)
      (Nat.add_le_add_right (Nat.succ_le_of_lt hB) 3)
  exact ⟨hAgt1, hB3⟩

/-- On a gap-3 solution, `Λ = 4 log A − 13 log(B+3) < 0`, hence ≠ 0. -/
theorem Lambda_gap3_ne_zero (A B : ℕ)
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    4 * log (A : ℝ) - 13 * log ((B + 3 : ℕ) : ℝ) ≠ 0 := by
  have hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := h
  have hlt := (matveev_gap3_log_form_upper_bound hsol hB).1
  unfold matveev_log_form at hlt
  exact ne_of_lt hlt

/-- Gap-3 instance: no `hGen`. Uses `B < A` ⇒ `1 < A` and `Λ < 0`.
    Does not inhabit unrestricted `matveev_gap3_lower` and does not
    force `B ≤ 10^6`. -/
theorem matveev_general_on_gap3 (A B : ℕ)
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    |4 * log (A : ℝ) - 13 * log (B + 3 : ℝ)| >
      exp (-C1_floor_real * log (A : ℝ) * log (B + 3 : ℝ) *
        B0_term (A : ℝ) (B + 3 : ℝ)) := by
  have hb := gap3_A_gt_one A B h hB
  have hcast : (B + 3 : ℝ) = ((B + 3 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_ofNat]
  have hΛn := Lambda_gap3_ne_zero A B h hB
  have hmain := matveev_thm14_n2_explicit_of_nat A (B + 3) hb.1 hb.2 hΛn
  rw [hcast]
  exact hmain

/-- Same bound written with Level 26 `matveev_log_form`. -/
theorem matveev_general_on_gap3_log_form (A B : ℕ)
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    |matveev_log_form A B| >
      exp (-C1_floor_real * log (A : ℝ) * log ((B + 3 : ℕ) : ℝ) *
        B0_term (A : ℝ) ((B + 3 : ℕ) : ℝ)) := by
  have hmain := matveev_general_on_gap3 A B h hB
  have hcast : (B + 3 : ℝ) = ((B + 3 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_ofNat]
  unfold matveev_log_form
  rw [hcast] at hmain
  exact hmain

#print axioms matveev_thm14_n2_explicit
#print axioms matveev_thm14_n2_explicit_of_nat
#print axioms matveev_general_on_gap3

end BealMatveevBeal.MatveevThm14Proof
