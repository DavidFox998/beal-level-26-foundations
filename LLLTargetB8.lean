/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Separate Lake target `BealMatveevBealV25B0Search`
  (same lib as `BealMatveevBealV25B0Search.lean`). Do **not** add
  `Beal/Matveev/LLLTargetB8.lean`: `.submodules Beal.Matveev`
  would pull it into the default glob. Do **not** import
  `Beal.Matveev.MatveevThm14General`.
-/
import BealMatveevBealV25B0Search

/-!
# LLL target `|Λ| ≥ B⁻⁸` (not a v25 mint)

On a gap-3 solution with `B ≥ 100` one already has
`|Λ| ≤ 2/B⁹` (`abs_Lambda_lt_two_div_B_pow_nine` at `f12ad03`).
If LLL lifted Matveev’s `B^{−C1}` lower bound with
`C1 = 143186215390` down to `|Λ| ≥ B⁻⁸`, then
`1/B⁸ ≤ 2/B⁹`, hence `B ≤ 2`, contradicting `B ≥ B0 = 10⁶`.
That would close the infinite branch `B ≥ B0`. The finite
branch `B ≤ B0` still needs Darmon–Merel `(4,4,13)` (the extra
axiom in `BealTrueV25`, not the default glob). This file does
**not** inhabit the LLL lift, does **not** inhabit
`LLL_reduces_bound_to_B0_v25`, and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

The 2-dim floor-lattice placeholder `[[C,0],[⌊C log A⌋,1]]` is
**not** shipped: `PAdicLLL` already has `b1 = (1,0)` of length
`1 < B0`, so that Euclidean cutoff fails. Working `C = 10³⁰`
makes `B0/C` smaller than `1/B0`, not a `|Λ| ≥ B⁻⁸` lift.

0 sorry. Tag `v24-v24x-final-rank3-shape-nogo` stays at `c1d173e`.
-/

namespace BealMatveevBeal.LLLTargetB8

open BealMatveevBeal.BealMatveevBealV25B0Search

/-- Honest LLL goal: `|Λ| ≥ B⁻⁸` on a solution with `B ≥ 100`.
    Same statement as `abs_Lambda_ge_inv_B_pow_eight`. Uninhabited. -/
noncomputable def abs_Lambda_ge_B_pow_neg_eight : Prop :=
  abs_Lambda_ge_inv_B_pow_eight

theorem abs_Lambda_ge_B_pow_neg_eight_eq :
    abs_Lambda_ge_B_pow_neg_eight = abs_Lambda_ge_inv_B_pow_eight :=
  rfl

/-- Reduce Matveev `C1 = 143186215390` to an exponent `< 9`.
    Uninhabited: Bugeaud–Laurent typically reaches `10²`–`10³`,
    not `< 9`. Equivalent to `|Λ| ≥ B⁻⁸`. -/
noncomputable def LLL_reduces_C1_to_lt_nine : Prop :=
  abs_Lambda_ge_B_pow_neg_eight

/-- Packaged v25 LLL close. Uninhabited: the first two conjuncts
    are the missing lower bound; the third is the large-`B`
    nogo they would imply. Rank-3
    `BealMatveevBealV25Rank3.LLL_reduces_bound_to_B0_v25` is a
    different `def Prop` in another target. -/
noncomputable def LLL_reduces_bound_to_B0_v25 : Prop :=
  abs_Lambda_ge_B_pow_neg_eight ∧
    LLL_reduces_C1_to_lt_nine ∧
      ∀ {A B : ℕ}, B0_nat ≤ B → A ^ 4 + B ^ 4 = (B + 3) ^ 13 → False

theorem one_div_pow_eight_le_two_div_pow_nine_implies_B_le_two
    {B : ℕ} (hB : 1 ≤ B)
    (hle : (1 : ℝ) / (B : ℝ) ^ 8 ≤ 2 / (B : ℝ) ^ 9) : B ≤ 2 := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hB)
  have h8 : (0 : ℝ) < (B : ℝ) ^ 8 := pow_pos hBpos 8
  have h9 : (0 : ℝ) < (B : ℝ) ^ 9 := pow_pos hBpos 9
  have hmul : (1 : ℝ) * (B : ℝ) ^ 9 ≤ 2 * (B : ℝ) ^ 8 :=
    (div_le_div_iff h8 h9).mp hle
  simp only [one_mul] at hmul
  have hcancel : (B : ℝ) ^ 8 * (B : ℝ) ≤ (B : ℝ) ^ 8 * 2 := by
    convert hmul using 1; ring
  have hB2 : (B : ℝ) ≤ 2 := le_of_mul_le_mul_left hcancel h8
  exact_mod_cast hB2

/-- If LLL inhabits `|Λ| ≥ B⁻⁸`, the proved `|Λ| ≤ 2/B⁹` forces
    `B ≤ 2`, contradicting `B ≥ B0 = 10⁶`. Does **not** inhabit
    the LLL hypothesis. -/
theorem no_sol_of_abs_Lambda_ge_B_pow_neg_eight
    (hge : abs_Lambda_ge_B_pow_neg_eight)
    {A B : ℕ} (hB0 : B0_nat ≤ B)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) : False := by
  have h100B0 : 100 ≤ B0_nat := by
    rw [B0_nat_eq]
    decide
  have h100 : 100 ≤ B := h100B0.trans hB0
  have hup := abs_Lambda_lt_two_div_B_pow_nine h100 hsol
  have hlow := hge h100 hsol
  have hle : (1 : ℝ) / (B : ℝ) ^ 8 ≤ 2 / (B : ℝ) ^ 9 :=
    hlow.trans hup
  have h1 : 1 ≤ B := le_trans (by decide : (1 : ℕ) ≤ 100) h100
  have hB2 : B ≤ 2 :=
    one_div_pow_eight_le_two_div_pow_nine_implies_B_le_two h1 hle
  have hB0le2 : B0_nat ≤ 2 := hB0.trans hB2
  rw [B0_nat_eq] at hB0le2
  exact (by decide : ¬((1000000 : ℕ) ≤ 2)) hB0le2

/-- Same implication, packaged as the large-`B` nogo. -/
theorem LLL_closes_B_ge_B0_of_pow_neg_eight
    (hge : abs_Lambda_ge_B_pow_neg_eight) :
    ∀ {A B : ℕ}, B0_nat ≤ B → A ^ 4 + B ^ 4 = (B + 3) ^ 13 → False :=
  no_sol_of_abs_Lambda_ge_B_pow_neg_eight hge

/-- Correct `by_cases` shape. Does **not** inhabit either
    branch: `B ≤ B0` is still `gap3_B_le_B0_no_solution`
    (`def Prop`, or Darmon–Merel in `BealTrueV25`), and
    `B ≥ B0` still needs `abs_Lambda_ge_B_pow_neg_eight`. -/
theorem future_v25_shape_of_B8_lift :
    gap3_B_le_B0_no_solution →
      abs_Lambda_ge_B_pow_neg_eight →
        ∀ B A : ℕ, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro hLe hge B A hsol
  by_cases h : B ≤ B0_nat
  · exact hLe B h A hsol
  · exact no_sol_of_abs_Lambda_ge_B_pow_neg_eight hge (le_of_not_le h) hsol

#check abs_Lambda_ge_B_pow_neg_eight
#check LLL_reduces_C1_to_lt_nine
#check LLL_reduces_bound_to_B0_v25
#check no_sol_of_abs_Lambda_ge_B_pow_neg_eight
#check LLL_closes_B_ge_B0_of_pow_neg_eight
#check future_v25_shape_of_B8_lift
#print axioms no_sol_of_abs_Lambda_ge_B_pow_neg_eight
#print axioms future_v25_shape_of_B8_lift

end BealMatveevBeal.LLLTargetB8
