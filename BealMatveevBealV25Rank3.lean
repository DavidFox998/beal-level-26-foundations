/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Separate Lake target `BealMatveevBealV25Rank3`,
  **not** the default `BealMatveevBeal` glob. Do **not** import
  `Beal.Matveev.MatveevThm14General`.
-/
import Mathlib
import PAdicLLL
import MatveevLLL

/-!
# Rank-3 Bugeaud–Laurent shape (not a v25 mint)

Successor of `v24-v24x-final-lll-dirichlet-nogo`. This file
wraps the shipped rank-3 lattice of `MatveevLLL.lean`:
`v = 4 b₁ − 13 b₂` encodes `Λ = 4 log A − 13 log(B+3)`, and
on a solution with `B > B0` one has `‖v‖ < 32` (a **short**
vector). That is the opposite of a `B ≤ B0` cutoff.
`baker_davenport_no_cutoff` already records the compatibility
with `|Λ| < 1/B`.

It does **not** claim Euclidean length `≥ B0` or `|u α + v| > exp(−B0)`
(those are false: `lll_euclidean_lower_bound_fails`,
`lll_form_lower_bound_fails`). It does **not** set `C = B0` as
the working lattice: the short-vector theorem uses
`MatveevLLL.LLL_C_nat = 10^30`. Shrinking `C` does not turn
`‖v‖ < 32` into a lower bound on `|Λ|`.

Fillable wrappers: `gap3_B_lt_A_of_sol`, `abs_Lambda_lt_inv_B`,
`lll_short_vector_of_large_B`, and the implication
`future_unconditional_shape`. None of those inhabit
`LLL_reduces_bound_to_B0`. `matveev_gap3_lower` is still a
lower bound on `|Λ|` when a solution exists and `B ≤ B0`, not
`¬∃ A`. Darmon–Merel `(4,4,13)` is still an extra axiom in
`BealTrueV25`.

`LLL_reduces_bound_to_B0` / `hGen` / `hLLL` stay `def Prop`.
Defining them as the constant true proposition is forbidden.
This file does **not** fork Mathlib, does **not** open a
Mathlib PR, and does **not** change `lean-toolchain`.
This file does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.
0 sorry. `C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

namespace BealMatveevBeal.BealMatveevBealV25Rank3

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_padic :
    C1_floor = BealMatveevBeal.PAdicLLL.C1_floor :=
  rfl

theorem B0_nat_eq_padic :
    B0_nat = BealMatveevBeal.PAdicLLL.B0_nat :=
  rfl

theorem B0_nat_eq_lll :
    B0_nat = BealMatveevBeal.MatveevLLL.B0_nat :=
  rfl

/-- Placeholder `C = B0`. **Not** the working rank-3 scaling.
    `MatveevLLL` uses `C = 10^30`. -/
def C_LLL_placeholder : ℕ := B0_nat

theorem C_LLL_placeholder_eq_B0 : C_LLL_placeholder = B0_nat := rfl

theorem LLL_C_ne_placeholder :
    BealMatveevBeal.MatveevLLL.LLL_C_nat ≠ C_LLL_placeholder := by
  rw [BealMatveevBeal.MatveevLLL.LLL_C_nat_eq, C_LLL_placeholder_eq_B0,
    B0_nat_eq]
  decide

/-! ## Fillable wrappers (not a v25 close) -/

/-- On a gap-3 solution, `B < A`. Does **not** inhabit
    `LLL_reduces_bound_to_B0`. -/
theorem gap3_B_lt_A_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) : B < A := by
  cases Nat.eq_zero_or_pos B with
  | inl h0 =>
    subst h0
    have hA : A ≠ 0 := by
      intro hA
      subst hA
      exact (by decide : ¬((0 : ℕ) ^ 4 + 0 ^ 4 = (0 + 3) ^ 13)) hsol
    exact Nat.pos_of_ne_zero hA
  | inr hpos =>
    exact BealMatveevBeal.PAdicLLL.A_gt_B_of_sol
      (by decide : (1 : ℕ) ≤ 3) hsol hpos

/-- Usable elementary upper bound, already on main as
    `MatveevLLL.abs_Lambda_le_inv_B`. The pc2 lemma
    `2(B+10)⁴ < (B+1)¹³` is `¬ A ≤ B+10`, not this log bound. -/
theorem abs_Lambda_lt_inv_B {A B : ℕ} (hB : 2 ≤ B) (_hA : B < A)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    |4 * Real.log (A : ℝ) - 13 * Real.log (B + 3 : ℝ)| <
      1 / (B : ℝ) := by
  have hBpos : 0 < B := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hB
  have h := BealMatveevBeal.MatveevLLL.abs_Lambda_le_inv_B hsol hBpos
  simpa [BealMatveevBeal.MatveevLLL.Lambda_eq_expanded] using h

/-- Rank-3 short vector `v = 4 b₁ − 13 b₂` on a solution with
    `B > B0`. This is `MatveevLLL.LLL_v_norm_lt_thirty_two`.
    Minkowski / LLL still *upper*-bound `λ₁`. Compatible with
    `|Λ| < 1/B` (`baker_davenport_no_cutoff`). -/
theorem lll_short_vector_of_large_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B) :
    BealMatveevBeal.MatveevLLL.lllNorm
        (BealMatveevBeal.MatveevLLL.LLL_v A B) <
      32 ∧ BealMatveevBeal.MatveevLLL.LLL_v A B ≠ 0 :=
  ⟨BealMatveevBeal.MatveevLLL.LLL_v_norm_lt_thirty_two hsol hB hB0,
    BealMatveevBeal.MatveevLLL.LLL_v_ne_zero A B⟩

/-- Same short-vector fact as `λ₁ < 32`. -/
theorem lll_lambda1_of_large_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B) :
    BealMatveevBeal.MatveevLLL.LLL_lambda1 A B < 32 :=
  BealMatveevBeal.MatveevLLL.LLL_lambda1_lt_thirty_two hsol hB hB0

/-! ## Kernel claims stay `def Prop` -/

/-- Future close `B > B0 → sol → False`. Uninhabited: the
    rank-3 vector is short, Matveev+LLL lose on `B ≥ B0`, and
    `matveev_gap3_lower` is not `¬∃ A`. -/
def LLL_reduces_bound_to_B0 : Prop :=
  ∀ B : ℕ, B0_nat < B →
    ∀ A : ℕ, B < A → A ^ 4 + B ^ 4 = (B + 3) ^ 13 → False

def LLL_reduces_bound_to_B0_future : Prop :=
  LLL_reduces_bound_to_B0

def hGen : Prop := LLL_reduces_bound_to_B0

def hLLL : Prop := LLL_reduces_bound_to_B0

/-- Correct `by_cases` shape. Does **not** inhabit either
    branch: the `B ≤ B0` side is not `matveev_gap3_lower`, and
    the `B > B0` side is `LLL_reduces_bound_to_B0`. -/
theorem future_unconditional_shape :
    (∀ B : ℕ, B ≤ B0_nat → ¬ ∃ A : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13) →
      LLL_reduces_bound_to_B0 →
        ∀ B : ℕ, ¬ ∃ A : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13 := by
  intro hLe hGt B
  by_cases h : B ≤ B0_nat
  · exact hLe B h
  · push_neg at h
    intro ⟨A, hsol⟩
    exact hGt B h A (gap3_B_lt_A_of_sol hsol) hsol

/-- Packaged: fillable lemmas plus the uninhabited reduction. -/
theorem rank3_shape_nogo {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 2 ≤ B) (hB0 : B0_nat < B) :
    B < A ∧
      |4 * Real.log (A : ℝ) - 13 * Real.log (B + 3 : ℝ)| <
          1 / (B : ℝ) ∧
        BealMatveevBeal.MatveevLLL.lllNorm
            (BealMatveevBeal.MatveevLLL.LLL_v A B) <
          32 :=
  ⟨gap3_B_lt_A_of_sol hsol,
    abs_Lambda_lt_inv_B hB (gap3_B_lt_A_of_sol hsol) hsol,
    (lll_short_vector_of_large_B hsol
        (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hB) hB0).1⟩

#check C1_floor_eq
#check B0_nat_eq
#check LLL_C_ne_placeholder
#check gap3_B_lt_A_of_sol
#check abs_Lambda_lt_inv_B
#check lll_short_vector_of_large_B
#check lll_lambda1_of_large_B
#check LLL_reduces_bound_to_B0
#check hGen
#check hLLL
#check future_unconditional_shape
#check rank3_shape_nogo
#check BealMatveevBeal.PAdicLLL.lll_euclidean_lower_bound_fails
#check BealMatveevBeal.PAdicLLL.lll_form_lower_bound_fails
#check BealMatveevBeal.MatveevLLL.LLL_v_norm_lt_thirty_two
#check BealMatveevBeal.MatveevLLL.baker_davenport_no_cutoff
#print axioms C1_floor_eq
#print axioms gap3_B_lt_A_of_sol
#print axioms abs_Lambda_lt_inv_B
#print axioms lll_short_vector_of_large_B
#print axioms future_unconditional_shape
#print axioms rank3_shape_nogo

end BealMatveevBeal.BealMatveevBealV25Rank3
