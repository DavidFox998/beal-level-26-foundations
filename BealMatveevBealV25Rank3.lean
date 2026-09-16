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

`C_LLL_v25 = C1_floor` (not `C1²`). The numeral
`B0/C > 1/B` on `B > B0` is true (`B0_div_C_gt_inv_B`).
On a solution that cutoff **contradicts** the shipped
`|Λ| < 1/B`, so `|Λ| ≥ B0/C` is false
(`lll_B0_div_C_lower_bound_fails`). `λ₁ < 32 < B0`, so a
vector of Euclidean scale `C|Λ| < B0` is **long** compared
with `λ₁`; Minkowski / `lll_svt_bound` still *upper*-bound
a short first vector.

Fillable wrappers: `gap3_B_lt_A_of_sol`, `abs_Lambda_lt_inv_B`,
`lll_short_vector_of_large_B`, `B0_div_C_gt_inv_B`, and the
implication `future_unconditional_shape`. None of those inhabit
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

/-- Draft cutoff scaling `C = C1_floor`, **not** `C1²`.
    `B0/C ≈ 7e-6`. Working rank-3 lattice in `MatveevLLL`
    still uses `C = 10^30`. -/
def C_LLL_v25 : ℕ := C1_floor

theorem C_LLL_v25_eq_C1 : C_LLL_v25 = C1_floor := rfl

theorem C_LLL_v25_eq : C_LLL_v25 = 143186215390 := rfl

theorem one_lt_C1_floor : 1 < C1_floor := by
  rw [C1_floor_eq]
  decide

theorem C_LLL_v25_lt_C1_sq :
    C_LLL_v25 < C1_floor * C1_floor := by
  rw [C_LLL_v25_eq_C1]
  have h : 1 < C1_floor := one_lt_C1_floor
  have hpos : 0 < C1_floor := Nat.zero_lt_of_lt h
  calc
    C1_floor = C1_floor * 1 := (mul_one C1_floor).symm
    _ < C1_floor * C1_floor := Nat.mul_lt_mul_of_pos_left h hpos

theorem C_LLL_v25_ne_C1_sq :
    C_LLL_v25 ≠ C1_floor * C1_floor :=
  ne_of_lt C_LLL_v25_lt_C1_sq

theorem C_LLL_v25_lt_B0_sq :
    C_LLL_v25 < B0_nat * B0_nat := by
  rw [C_LLL_v25_eq, B0_nat_eq]
  decide

theorem C_LLL_v25_lt_B0_mul_B {B : ℕ} (hB : B0_nat < B) :
    C_LLL_v25 < B0_nat * B :=
  lt_trans C_LLL_v25_lt_B0_sq
    (Nat.mul_lt_mul_of_pos_left hB (by
      rw [B0_nat_eq]
      decide))

theorem two_le_of_B_gt_B0 {B : ℕ} (hB : B0_nat < B) : 2 ≤ B :=
  BealMatveevBeal.PAdicLLL.two_le_of_B_ge_B0 (le_of_lt hB)

/-- Closed numeral cutoff: `B0 / C1_floor > 1/B` for `B > B0`.
    Cross-multiply: `B0 * B > C` because `B0 * B0 = 10^{12} > C`.
    This is **not** `|Λ| ≥ B0/C`. -/
theorem B0_div_C_gt_inv_B {B : ℕ} (hB : B0_nat < B) :
    (B0_nat : ℝ) / (C_LLL_v25 : ℝ) > 1 / (B : ℝ) := by
  have hBpos : (0 : ℝ) < (B : ℝ) :=
    Nat.cast_pos.mpr (lt_trans (by
      rw [B0_nat_eq]
      decide) hB)
  have hCpos : (0 : ℝ) < (C_LLL_v25 : ℝ) :=
    Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one one_lt_C1_floor)
  have hnat : C_LLL_v25 < B0_nat * B := C_LLL_v25_lt_B0_mul_B hB
  have hcast : (C_LLL_v25 : ℝ) < (B0_nat : ℝ) * (B : ℝ) := by
    exact_mod_cast hnat
  have hlt : (1 : ℝ) / (B : ℝ) < (B0_nat : ℝ) / (C_LLL_v25 : ℝ) := by
    rw [div_lt_div_iff hBpos hCpos, one_mul]
    exact hcast
  exact hlt

theorem thirty_two_lt_B0 : (32 : ℝ) < (B0_nat : ℝ) := by
  rw [B0_nat_eq]
  norm_num

/-- `‖b₁‖ ≤ 2 λ₁` is an *upper* bound. Combined with `λ₁ < 32`
    this is `‖b₁‖ < 64 < B0`, the opposite of a `B0` cutoff. -/
theorem sixty_four_lt_B0 : (64 : ℝ) < (B0_nat : ℝ) := by
  rw [B0_nat_eq]
  norm_num

theorem lll_svt_bound_of_rank3 (A B : ℕ) {b1 b2 b3 : Fin 3 → ℝ}
    (hmem : BealMatveevBeal.MatveevLLL.mem_LLL_lattice A B b1)
    (hgen : BealMatveevBeal.MatveevLLL.lllGenerates A B b1 b2 b3)
    (hred : BealMatveevBeal.MatveevLLL.lllIsReducedBasis b1 b2 b3) :
    BealMatveevBeal.MatveevLLL.lllNorm b1 ≤
      2 * BealMatveevBeal.MatveevLLL.LLL_lambda1 A B :=
  BealMatveevBeal.MatveevLLL.lll_svt_bound A B hmem hgen hred

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

/-- `λ₁ < 32 < B0`. A vector of Euclidean scale `B0` is **not**
    shorter than `λ₁`. -/
theorem lll_lambda1_lt_B0 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B) :
    BealMatveevBeal.MatveevLLL.LLL_lambda1 A B < (B0_nat : ℝ) :=
  lt_trans (lll_lambda1_of_large_B hsol hB hB0) thirty_two_lt_B0

/-- On a solution with `B > B0`, the elementary `|Λ| < 1/B`
    is already stricter than `B0/C`. -/
theorem abs_Lambda_lt_B0_div_C {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB0 : B0_nat < B) :
    |4 * Real.log (A : ℝ) - 13 * Real.log (B + 3 : ℝ)| <
      (B0_nat : ℝ) / (C_LLL_v25 : ℝ) := by
  have h2 : 2 ≤ B := two_le_of_B_gt_B0 hB0
  have hA : B < A := gap3_B_lt_A_of_sol hsol
  have hUp := abs_Lambda_lt_inv_B h2 hA hsol
  have hCut := B0_div_C_gt_inv_B hB0
  exact lt_trans hUp hCut

/-- The draft Baker lower bound `|Λ| ≥ B0/C` is **false** on a
    gap-3 solution with `B > B0`: it contradicts
    `abs_Lambda_lt_inv_B` together with `B0_div_C_gt_inv_B`.
    Short-vector `‖v‖ < 32` / `λ₁ < 32` cannot restore it:
    those are *upper* bounds on a short vector. -/
theorem lll_B0_div_C_lower_bound_fails {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB0 : B0_nat < B) :
    ¬ ((B0_nat : ℝ) / (C_LLL_v25 : ℝ) ≤
        |4 * Real.log (A : ℝ) - 13 * Real.log (B + 3 : ℝ)|) :=
  not_le.mpr (abs_Lambda_lt_B0_div_C hsol hB0)

/-! ## Kernel claims stay `def Prop` -/

/-- Future close `B > B0 → sol → False`. Uninhabited: the
    rank-3 vector is short, Matveev+LLL lose on `B ≥ B0`, and
    `matveev_gap3_lower` is not `¬∃ A`. -/
def LLL_reduces_bound_to_B0 : Prop :=
  ∀ B : ℕ, B0_nat < B →
    ∀ A : ℕ, B < A → A ^ 4 + B ^ 4 = (B + 3) ^ 13 → False

def LLL_reduces_bound_to_B0_future : Prop :=
  LLL_reduces_bound_to_B0

/-- Draft v25 inhabitant name. Stays `def Prop`: the proposed
    `|Λ| ≥ B0/C` lower bound fails on a solution. -/
def LLL_reduces_bound_to_B0_v25 : Prop :=
  LLL_reduces_bound_to_B0

def LLL_reduces_bound_to_B0_future_inhabitant : Prop :=
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

/-- Packaged B0/C nogo: numeral cutoff beats `1/B`, the proposed
    `|Λ| ≥ B0/C` fails on a solution, and `λ₁ < 32 < B0`. -/
theorem lll_B0_div_C_shape_nogo {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB0 : B0_nat < B) :
    (B0_nat : ℝ) / (C_LLL_v25 : ℝ) > 1 / (B : ℝ) ∧
      |4 * Real.log (A : ℝ) - 13 * Real.log (B + 3 : ℝ)| <
          (B0_nat : ℝ) / (C_LLL_v25 : ℝ) ∧
        BealMatveevBeal.MatveevLLL.LLL_lambda1 A B < (B0_nat : ℝ) :=
  ⟨B0_div_C_gt_inv_B hB0,
    abs_Lambda_lt_B0_div_C hsol hB0,
    lll_lambda1_lt_B0 hsol
      (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) (two_le_of_B_gt_B0 hB0))
      hB0⟩

#check C_LLL_v25_eq
#check C_LLL_v25_ne_C1_sq
#check B0_div_C_gt_inv_B
#check abs_Lambda_lt_B0_div_C
#check lll_B0_div_C_lower_bound_fails
#check lll_lambda1_lt_B0
#check lll_svt_bound_of_rank3
#check sixty_four_lt_B0
#check LLL_reduces_bound_to_B0
#check LLL_reduces_bound_to_B0_v25
#check hGen
#check hLLL
#check future_unconditional_shape
#check rank3_shape_nogo
#check lll_B0_div_C_shape_nogo
#check BealMatveevBeal.PAdicLLL.lll_euclidean_lower_bound_fails
#check BealMatveevBeal.PAdicLLL.lll_form_lower_bound_fails
#check BealMatveevBeal.MatveevLLL.LLL_v_norm_lt_thirty_two
#check BealMatveevBeal.MatveevLLL.lll_svt_bound
#check BealMatveevBeal.MatveevLLL.baker_davenport_no_cutoff
#print axioms C1_floor_eq
#print axioms B0_div_C_gt_inv_B
#print axioms gap3_B_lt_A_of_sol
#print axioms abs_Lambda_lt_inv_B
#print axioms lll_short_vector_of_large_B
#print axioms lll_svt_bound_of_rank3
#print axioms lll_B0_div_C_lower_bound_fails
#print axioms future_unconditional_shape
#print axioms rank3_shape_nogo
#print axioms lll_B0_div_C_shape_nogo

end BealMatveevBeal.BealMatveevBealV25Rank3
