/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v24.2.1 -- logarithmic form as logarithm of ratio
on gap-3 solutions.
Keeps all v24.0.0 through v24.2.0 lemmas.

On a gap-3 solution A^4 + B^4 = (B+3)^13:
  * 0 < A via matveev_gap3_A_pos
  * 0 < B via matveev_gap3_B_pos_of_solution
  * 0 < (A:Real)^4 via matveev_gap3_A_pow_pos
  * 0 < ((B+3):Real)^13 via matveev_gap3_B3_pow_pos
  * Lambda = 4 log A - 13 log (B+3) = -log((B+3)^13 / A^4)
  * |Lambda| = log((B+3)^13 / A^4) = log(1 + B^4 / A^4)
    (matveev_gap3_log_form_eq_log_ratio,
     matveev_gap3_abs_lambda_eq_log_one_plus_ratio)
  * 0 < matveev_target_exp_lower < 1
    (matveev_exp_lower_lt_one_and_pos)

Links the upper bound side via ratio toward Baker B0.

thirty_pow is 30^6 = 729000000, not
the 7-digit typo 72900000 (= 30^6 / 10).
C1_floor * 729000000 = height_B0
= 104382751019310000000.
C1_floor * 72900000 = height_B0 / 10
= 10438275101931000000.
Both products stay decide theorems.

Does NOT inhabit baker_bound_gap3.
Does NOT inhabit
  |Lambda| > exp(matveev_C_exp_bound).
Mathlib 4.12 has no Matveev 2000 Thm 1.4.
v25 is only when
baker_bound_gap3 greens and
baker_conditional_gap3_full drops hBaker.

Does not import RibetMazur, BealFreyB14,
or FreyModularity_13.
Does not use sorry.
-/

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import BealLevel26Foundations.Beal.FullProof.BealMatveevConstants
import BealLevel26Foundations.Beal.FullProof.BealMatveevInequality
import BealLevel26Foundations.Beal.FullProof.BealMatveevInequalityReal
import BealLevel26Foundations.Beal.FullProof.BealBakerBoundGap3
import BealLevel26Foundations.Beal.FullProof.BealBugeaudLLLFormal
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000000

namespace BealLevel26Foundations.BealMatveevThm14

open BealLevel26Foundations.BealMatveevConstants
open BealLevel26Foundations.BealMatveevInequality
open BealLevel26Foundations.BealMatveevInequalityReal
open BealLevel26Foundations.BealBakerBoundGap3
open BealLevel26Foundations.BealBugeaudLLLFormal
open BealLevel26Foundations.BealGap3BakerUpperBound

/-! ## v19 constants, both thirty_pow numerals -/

theorem matveev_C1_floor_eq :
    matveev_C1_floor = 143186215390 := by
  decide

/-- 30^6 = 729000000. -/
theorem matveev_thirty_pow_eq_30_pow_6 :
    matveev_thirty_pow = Nat.pow 30 6 := by
  decide

theorem matveev_thirty_pow_eq_729000000 :
    matveev_thirty_pow = 729000000 := by
  decide

/-- The recurring typo 72900000 is not 30^6.
    30^6 = 729000000 = 72900000 * 10. -/
theorem matveev_thirty_pow_ne_72900000 :
    matveev_thirty_pow ≠ 72900000 := by
  decide

/-- Numeral check: the typo times ten is 30^6. -/
theorem matveev_thirty_pow_eq_typo_times_ten :
    matveev_thirty_pow = 72900000 * 10 := by
  decide

theorem matveev_C1_floor_pos :
    matveev_C1_floor > 0 := by
  decide

theorem matveev_thirty_pow_pos :
    matveev_thirty_pow > 0 := by
  decide

theorem matveev_height_B0_eq_numeral :
    matveev_height_B0 = 104382751019310000000 := by
  decide

theorem matveev_c4_scale_eq_16 :
    matveev_c4_scale = 16 :=
  rfl

/-- Tate survivor reused as a Nat identity.
    Does not import BealFreyB14. -/
theorem tate_survivor_63982 :
    (63982 : Nat) = 2 * 31991 := by
  decide

/-! ## v20 Bugeaud LLL integer skeleton -/

theorem matveev_thm14_bugeaud_K_eq :
    bugeaud_K = Nat.pow 10 20 :=
  bugeaud_K_eq

theorem matveev_thm14_bugeaud_LLL_basis_holds :
    bugeaud_LLL_basis ≠ [] :=
  bugeaud_LLL_basis_holds

/-! ## v21 integer log-form nonzero -/

theorem matveev_thm14_log_form_int_ne_zero_zero :
    matveev_log_form_int 0 ≠ 0 :=
  matveev_log_form_ne_zero_zero

theorem matveev_thm14_log_form_int_ne_zero_fourteen :
    matveev_log_form_int 14 ≠ 0 :=
  matveev_log_form_ne_zero_fourteen

/-! ## v22 / v23 Real exponent -/

noncomputable def matveev_C_exp_bound_thm14 :=
  matveev_C_exp_bound

theorem matveev_thm14_height_gt_onee12 :
    ten_pow_12 < matveev_height_B0 :=
  matveev_height_B0_gt_onee12

/-- log(height_B0) > 0 from height > 10^12
    and Real.log_pos. -/
theorem matveev_height_log_pos :
    (0 : Real) < Real.log (matveev_height_B0 : Real) := by
  have hone : (1 : Real) < (matveev_height_B0 : Real) := by
    have hcast : ((1 : Nat) : Real) < (matveev_height_B0 : Real) :=
      Nat.cast_lt.mpr
        (Nat.lt_trans (by decide : 1 < ten_pow_12)
          matveev_height_B0_gt_onee12)
    simpa using hcast
  exact Real.log_pos hone

/-- Restate v23: displayed exponent is negative. -/
theorem matveev_exp_bound_neg :
    matveev_C_exp_bound < 0 :=
  matveev_C_exp_bound_neg

/-- height_B0 > 2 as a Real, from
    height_B0 > 10^12. -/
theorem matveev_height_B0_gt_two :
    (2 : Real) < (matveev_height_B0 : Real) := by
  have hcast : ((2 : Nat) : Real) < (matveev_height_B0 : Real) :=
    Nat.cast_lt.mpr
      (Nat.lt_trans (by decide : 2 < ten_pow_12)
        matveev_height_B0_gt_onee12)
  simpa using hcast

/-- Real.log is strictly monotone on positives. -/
theorem matveev_log_height_monotone :
    ∀ (h1 h2 : Real),
      (0 : Real) < h1 → h1 < h2 →
        Real.log h1 < Real.log h2 :=
  fun _ _ hpos hlt => Real.log_lt_log hpos hlt

/-- C_exp_bound < 0 iff log(height_B0) > 0,
    since C1_floor > 0 and thirty_pow > 0. -/
theorem matveev_C_exp_bound_lt_zero_of_pos_log :
    matveev_C_exp_bound < 0 ↔
      (0 : Real) < Real.log (matveev_height_B0 : Real) := by
  have hC : (0 : Real) < (matveev_C1_floor : Real) :=
    Nat.cast_pos.mpr matveev_C1_floor_pos
  have hT : (0 : Real) < (matveev_thirty_pow : Real) :=
    Nat.cast_pos.mpr matveev_thirty_pow_pos
  have hCT : (0 : Real) <
      (matveev_C1_floor : Real) * (matveev_thirty_pow : Real) :=
    mul_pos hC hT
  have hdef :
      matveev_C_exp_bound =
        -((matveev_C1_floor : Real) * (matveev_thirty_pow : Real) *
            Real.log (matveev_height_B0 : Real)) :=
    rfl
  constructor
  · intro hneg
    have hprod : (0 : Real) <
        (matveev_C1_floor : Real) * (matveev_thirty_pow : Real) *
          Real.log (matveev_height_B0 : Real) := by
      rw [hdef] at hneg
      exact neg_lt_zero.mp hneg
    exact pos_of_mul_pos_right hprod (le_of_lt hCT)
  · intro hlog
    have hmul : (0 : Real) <
        (matveev_C1_floor : Real) * (matveev_thirty_pow : Real) *
          Real.log (matveev_height_B0 : Real) :=
      mul_pos hCT hlog
    rw [hdef]
    exact neg_neg_of_pos hmul

theorem matveev_thm14_C_exp_bound_lt_neg_onee12 :
    matveev_C_exp_bound < -((ten_pow_12 : Nat) : Real) :=
  matveev_C_exp_bound_lt_neg_onee12

/-! ## v24.0.2 — exp of the displayed bound -/

/-- Direct restatement of v24.0.1 negativity. -/
theorem matveev_exp_bound_lt_zero :
    matveev_C_exp_bound < 0 :=
  matveev_exp_bound_neg

/-- exp(C_exp_bound) < 1 because the
    exponent is negative. -/
theorem matveev_exp_of_bound_pos_lt_one :
    Real.exp matveev_C_exp_bound < 1 :=
  Real.exp_lt_one_iff.mpr matveev_exp_bound_lt_zero

/-- exp is always positive. -/
theorem matveev_exp_of_bound_pos :
    (0 : Real) < Real.exp matveev_C_exp_bound :=
  Real.exp_pos matveev_C_exp_bound

/-- Strengthen v23 strict comparison to ≤
    for AMS-facing statements. -/
theorem matveev_C_exp_bound_le_neg_onee12 :
    matveev_C_exp_bound ≤ -((ten_pow_12 : Nat) : Real) :=
  le_of_lt matveev_C_exp_bound_lt_neg_onee12

/-- Named uniform lower-bound shape.
    0 < target < 1; this is not yet
    |Lambda| > target. -/
noncomputable def matveev_target_exp_lower : Real :=
  Real.exp matveev_C_exp_bound

theorem matveev_target_exp_lower_pos :
    (0 : Real) < matveev_target_exp_lower :=
  matveev_exp_of_bound_pos

theorem matveev_target_exp_lower_lt_one :
    matveev_target_exp_lower < 1 :=
  matveev_exp_of_bound_pos_lt_one

/-! ## v24.1.0 — height product identity

    The displayed exponent is
    -(C1_floor * thirty_pow * log height_B0)
    with thirty_pow = 30^6 = 729000000.
    That product equals height_B0.
    The 7-digit typo 72900000 is 30^6 / 10
    and its product is height_B0 / 10.
    Does not use sorry. -/

/-- Typo product: C1_floor * (30^6 / 10).
    This is height_B0 / 10, not height_B0. -/
theorem matveev_C1_floor_mul_thirty_pow_div10 :
    matveev_C1_floor * 72900000 = 10438275101931000000 := by
  decide

/-- Correct 30^6 product. This is height_B0. -/
theorem matveev_C1_floor_mul_thirty_pow :
    matveev_C1_floor * 729000000 = 104382751019310000000 := by
  decide

/-- Typo product times ten recovers height_B0. -/
theorem matveev_C1_floor_mul_thirty_pow_div10_times_ten :
    matveev_C1_floor * 72900000 * 10 = matveev_height_B0 := by
  decide

/-- The typo product is not the displayed height. -/
theorem matveev_C1_floor_mul_thirty_pow_div10_ne_height :
    matveev_C1_floor * 72900000 ≠ matveev_height_B0 := by
  decide

/-- Product that controls the displayed exponent.
    height_B0 = C1_floor * thirty_pow
    with thirty_pow = 729000000 = 30^6.
    Not height_B0 * 10. -/
theorem matveev_height_product_link :
    matveev_height_B0 = matveev_C1_floor * matveev_thirty_pow := by
  decide

/-! ## v24.1.1 — rewriting C_exp_bound via height_B0

    Uses `matveev_height_product_link`
    (`height_B0 = C1_floor * thirty_pow`) to rewrite
    `matveev_C_exp_bound` to
    `-((height_B0 : Real) * Real.log (height_B0 : Real))`.
    Does not use sorry. -/

/-- Rewrite C_exp_bound using the height_B0 product identity. -/
theorem matveev_C_exp_bound_eq_neg_height_mul_log :
    matveev_C_exp_bound =
      -(((matveev_height_B0 : Real) *
          Real.log (matveev_height_B0 : Real))) := by
  have hprod : ((matveev_C1_floor : Real) * (matveev_thirty_pow : Real)) =
      (matveev_height_B0 : Real) := by
    have hnat : matveev_C1_floor * matveev_thirty_pow = matveev_height_B0 :=
      matveev_height_product_link.symm
    exact_mod_cast hnat
  unfold matveev_C_exp_bound
  rw [hprod]

/-- Associativity version of the rewrite for AMS statements:
    -(height_B0 : Real) * log height_B0. -/
theorem matveev_C_exp_bound_eq_neg_height_log :
    matveev_C_exp_bound =
      -(matveev_height_B0 : Real) * Real.log (matveev_height_B0 : Real) := by
  rw [matveev_C_exp_bound_eq_neg_height_mul_log]
  ring

/-- Target lower bound written with height_B0 directly. -/
theorem matveev_target_exp_lower_eq :
    matveev_target_exp_lower =
      Real.exp (-((matveev_height_B0 : Real) *
        Real.log (matveev_height_B0 : Real))) := by
  unfold matveev_target_exp_lower
  rw [matveev_C_exp_bound_eq_neg_height_mul_log]

/-- height_B0 * log height_B0 is strictly positive. -/
theorem matveev_height_B0_mul_log_pos :
    (0 : Real) < (matveev_height_B0 : Real) *
      Real.log (matveev_height_B0 : Real) := by
  have hpos_h : (0 : Real) < (matveev_height_B0 : Real) := by
    have hcast : ((0 : Nat) : Real) < (matveev_height_B0 : Real) :=
      Nat.cast_lt.mpr
        (Nat.lt_trans (by decide : 0 < 2)
          (Nat.lt_trans (by decide : 2 < ten_pow_12)
            matveev_height_B0_gt_onee12))
    simpa using hcast
  exact mul_pos hpos_h matveev_height_log_pos

/-- Equivalence of C_exp_bound < 0 with 0 < height_B0 * log height_B0. -/
theorem matveev_C_exp_bound_neg_of_mul_log_pos :
    matveev_C_exp_bound < 0 ↔
      (0 : Real) < (matveev_height_B0 : Real) *
        Real.log (matveev_height_B0 : Real) := by
  rw [matveev_C_exp_bound_eq_neg_height_mul_log]
  exact neg_lt_zero

/-- Integer trace of the Thm 1.4 start. -/
def matveev_thm14_constants : List Int :=
  [143186215390, 729000000, 104382751019310000000,
    16, 63982, 1000000000000]

theorem matveev_thm14_constants_hold :
    matveev_thm14_constants ≠ [] := by
  decide

/-! ## v24.2.0 — Logarithmic form upper bound on gap-3 solutions

    On a gap-3 solution A^4 + B^4 = (B+3)^13:
      * B > 0 by eliminating B = 0 via baker_le_B0_gap3
      * A > 0 via eq_implies_A_gt_B
      * Lambda = 4 log A - 13 log (B+3) < 0
      * |Lambda| = -Lambda = -(4 log A - 13 log (B+3))
      * 0 < matveev_target_exp_lower < 1

    Does not use sorry. -/

/-- On any gap-3 solution A^4 + B^4 = (B+3)^13, B must be strictly positive
    because B = 0 is eliminated by baker_le_B0_gap3 (0 ≤ baker_B0). -/
theorem matveev_gap3_B_pos_of_solution {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    0 < B := by
  cases' Nat.eq_zero_or_pos B with hB0 hpos
  · exfalso
    have hle : B ≤ baker_B0 := by rw [hB0]; decide
    exact baker_le_B0_gap3 hle ⟨A, hsol⟩
  · exact hpos

/-- On any gap-3 solution A^4 + B^4 = (B+3)^13, A must be strictly positive
    because 0 < B and B < A via eq_implies_A_gt_B. -/
theorem matveev_gap3_A_pos {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    0 < A := by
  have hB := matveev_gap3_B_pos_of_solution hsol
  have hgt := eq_implies_A_gt_B hsol hB
  exact Nat.lt_trans hB hgt

/-- On a gap-3 solution with B > 0, A is strictly positive. -/
theorem matveev_gap3_A_pos_of_pos_B {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hB : 0 < B) :
    0 < A := by
  have hgt := eq_implies_A_gt_B hsol hB
  exact Nat.lt_trans hB hgt

/-- On a gap-3 solution with B > 0, the Real logarithmic form
    Lambda = 4 log A - 13 log (B+3) is strictly negative,
    and |Lambda| = -Lambda = -(4 log A - 13 log (B+3)). -/
theorem matveev_gap3_log_form_upper_bound {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hB : 0 < B) :
    matveev_log_form A B < 0 ∧
      |matveev_log_form A B| = -matveev_log_form A B := by
  have hlt := matveev_log_form_lt_zero_of_gap3 hsol hB
  exact ⟨hlt, abs_of_neg hlt⟩

/-- Expanded version of matveev_gap3_log_form_upper_bound with
    explicit 4 log A - 13 log (B+3). -/
theorem matveev_gap3_log_form_upper_bound_expanded {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hB : 0 < B) :
    (4 : Real) * Real.log (A : Real) -
        (13 : Real) * Real.log ((B + 3 : Nat) : Real) < 0 ∧
      |(4 : Real) * Real.log (A : Real) -
        (13 : Real) * Real.log ((B + 3 : Nat) : Real)| =
        -((4 : Real) * Real.log (A : Real) -
          (13 : Real) * Real.log ((B + 3 : Nat) : Real)) :=
  matveev_gap3_log_form_upper_bound hsol hB

/-- Upper bound shape holding directly from the solution identity without
    requiring B > 0 as a hypothesis (B > 0 is deduced). -/
theorem matveev_gap3_log_form_upper_bound_of_solution {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    matveev_log_form A B < 0 ∧
      |matveev_log_form A B| = -matveev_log_form A B :=
  matveev_gap3_log_form_upper_bound hsol (matveev_gap3_B_pos_of_solution hsol)

/-- Restatement of the target exponential lower bound in (0, 1):
    0 < matveev_target_exp_lower ∧ matveev_target_exp_lower < 1. -/
theorem matveev_exp_lower_lt_one_and_pos :
    (0 : Real) < matveev_target_exp_lower ∧
      matveev_target_exp_lower < 1 :=
  ⟨matveev_target_exp_lower_pos, matveev_target_exp_lower_lt_one⟩

/-! ## v24.2.1 — Logarithmic form as logarithm of ratio

    On a gap-3 solution A^4 + B^4 = (B+3)^13:
      * 0 < (A:Real)^4
      * 0 < ((B+3):Real)^13
      * (B+3)^13 / A^4 = 1 + B^4 / A^4
      * Lambda = 4 log A - 13 log (B+3) = -log((B+3)^13 / A^4)
      * |Lambda| = log((B+3)^13 / A^4) = log(1 + B^4 / A^4)

    Does not use sorry. -/

/-- On a gap-3 solution, (A : Real)^4 is strictly positive. -/
theorem matveev_gap3_A_pow_pos {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    (0 : Real) < (A : Real) ^ 4 := by
  have hA : 0 < A := matveev_gap3_A_pos hsol
  have hAR : (0 : Real) < (A : Real) := Nat.cast_pos.mpr hA
  exact pow_pos hAR 4

/-- On a gap-3 solution, ((B+3) : Real)^13 is strictly positive. -/
theorem matveev_gap3_B3_pow_pos {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    (0 : Real) < ((B + 3 : Nat) : Real) ^ 13 := by
  have hB : 0 < B := matveev_gap3_B_pos_of_solution hsol
  have hB3 : 0 < B + 3 :=
    Nat.lt_trans hB (Nat.lt_add_of_pos_right (by decide : 0 < 3))
  have hB3R : (0 : Real) < ((B + 3 : Nat) : Real) := Nat.cast_pos.mpr hB3
  exact pow_pos hB3R 13

/-- On a gap-3 solution, the ratio ((B+3) : Real)^13 / (A : Real)^4 equals
    1 + (B : Real)^4 / (A : Real)^4. -/
theorem matveev_gap3_ratio_eq_one_plus_ratio {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    ((B + 3 : Nat) : Real) ^ 13 / (A : Real) ^ 4 =
      1 + (B : Real) ^ 4 / (A : Real) ^ 4 := by
  have hA4_pos := matveev_gap3_A_pow_pos hsol
  have hA4_ne : (A : Real) ^ 4 ≠ 0 := hA4_pos.ne'
  have hcast_pow : ((B + 3 : Nat) : Real) ^ 13 =
      (A : Real) ^ 4 + (B : Real) ^ 4 := by
    have hcast : ((Nat.pow (B + 3) 13 : Nat) : Real) =
        ((Nat.pow A 4 + Nat.pow B 4 : Nat) : Real) := by
      rw [← hsol]
    push_cast at hcast
    simpa [Nat.cast_pow] using hcast
  rw [hcast_pow, add_div, div_self hA4_ne]

/-- On a gap-3 solution, Lambda = -log(((B+3) : Real)^13 / (A : Real)^4),
    and |Lambda| = log(((B+3) : Real)^13 / (A : Real)^4) = log(1 + B^4 / A^4). -/
theorem matveev_gap3_log_form_eq_log_ratio {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    matveev_log_form A B =
      -Real.log (((B + 3 : Nat) : Real) ^ 13 / (A : Real) ^ 4) ∧
    |matveev_log_form A B| =
      Real.log (((B + 3 : Nat) : Real) ^ 13 / (A : Real) ^ 4) ∧
    Real.log (((B + 3 : Nat) : Real) ^ 13 / (A : Real) ^ 4) =
      Real.log (1 + (B : Real) ^ 4 / (A : Real) ^ 4) := by
  have hB3_pow_pos := matveev_gap3_B3_pow_pos hsol
  have hA_pow_pos := matveev_gap3_A_pow_pos hsol
  have hlog_div : Real.log (((B + 3 : Nat) : Real) ^ 13 / (A : Real) ^ 4) =
      Real.log (((B + 3 : Nat) : Real) ^ 13) - Real.log ((A : Real) ^ 4) :=
    Real.log_div hB3_pow_pos.ne' hA_pow_pos.ne'
  have hlog_pow13 : Real.log (((B + 3 : Nat) : Real) ^ 13) =
      (13 : Real) * Real.log ((B + 3 : Nat) : Real) :=
    Real.log_pow ((B + 3 : Nat) : Real) 13
  have hlog_pow4 : Real.log ((A : Real) ^ 4) =
      (4 : Real) * Real.log (A : Real) :=
    Real.log_pow (A : Real) 4
  have hratio_log : Real.log (((B + 3 : Nat) : Real) ^ 13 / (A : Real) ^ 4) =
      (13 : Real) * Real.log ((B + 3 : Nat) : Real) -
        (4 : Real) * Real.log (A : Real) := by
    rw [hlog_div, hlog_pow13, hlog_pow4]
  have hlambda : matveev_log_form A B =
      -Real.log (((B + 3 : Nat) : Real) ^ 13 / (A : Real) ^ 4) := by
    rw [hratio_log]
    unfold matveev_log_form
    ring
  have hbound := matveev_gap3_log_form_upper_bound_of_solution hsol
  have habs : |matveev_log_form A B| =
      Real.log (((B + 3 : Nat) : Real) ^ 13 / (A : Real) ^ 4) := by
    rw [hbound.2, hlambda, neg_neg]
  have heq_ratio : Real.log (((B + 3 : Nat) : Real) ^ 13 / (A : Real) ^ 4) =
      Real.log (1 + (B : Real) ^ 4 / (A : Real) ^ 4) := by
    rw [matveev_gap3_ratio_eq_one_plus_ratio hsol]
  exact ⟨hlambda, habs, heq_ratio⟩

/-- Upper bound side via ratio: on a solution,
    |Lambda| = log(1 + B^4 / A^4). -/
theorem matveev_gap3_abs_lambda_eq_log_one_plus_ratio {A B : Nat}
    (hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    |matveev_log_form A B| = Real.log (1 + (B : Real) ^ 4 / (A : Real) ^ 4) := by
  have h := matveev_gap3_log_form_eq_log_ratio hsol
  rw [h.2.1, h.2.2]

/-! ## Named Matveev 2000 Thm 1.4 target

    On a gap-3 solution the v23 theorem
    already gives Lambda != 0.  The uniform
    lower bound |Lambda| > exp(C_exp_bound)
    is Matveev 2000 Thm 1.4 and is not in
    Mathlib 4.12.  Stays a def Prop.
    Does not inhabit baker_bound_gap3. -/

def matveev_inequality_real_target : Prop :=
  ∀ (A B : Nat),
    0 < B →
      Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 →
        |matveev_log_form A B| > Real.exp matveev_C_exp_bound

/-- Same target under the v22 name, still
    uninhabited. -/
def matveev_inequality_real_formal_remaining : Prop :=
  matveev_inequality_real_formal

/-- baker_bound_gap3 stays a def Prop. -/
def baker_bound_gap3_remaining_thm14 : Prop :=
  baker_bound_gap3

#check matveev_C1_floor_eq
#check matveev_thirty_pow_eq_30_pow_6
#check matveev_thirty_pow_eq_729000000
#check matveev_thirty_pow_ne_72900000
#check matveev_height_B0_eq_numeral
#check tate_survivor_63982
#check matveev_thm14_bugeaud_LLL_basis_holds
#check matveev_C1_floor_pos
#check matveev_thirty_pow_pos
#check matveev_thirty_pow_eq_typo_times_ten
#check matveev_height_log_pos
#check matveev_exp_bound_neg
#check matveev_height_B0_gt_two
#check matveev_log_height_monotone
#check matveev_C_exp_bound_lt_zero_of_pos_log
#check matveev_exp_bound_lt_zero
#check matveev_exp_of_bound_pos_lt_one
#check matveev_exp_of_bound_pos
#check matveev_C_exp_bound_le_neg_onee12
#check matveev_target_exp_lower
#check matveev_C1_floor_mul_thirty_pow_div10
#check matveev_C1_floor_mul_thirty_pow
#check matveev_C1_floor_mul_thirty_pow_div10_times_ten
#check matveev_C1_floor_mul_thirty_pow_div10_ne_height
#check matveev_height_product_link
#check matveev_C_exp_bound_eq_neg_height_mul_log
#check matveev_C_exp_bound_eq_neg_height_log
#check matveev_target_exp_lower_eq
#check matveev_height_B0_mul_log_pos
#check matveev_C_exp_bound_neg_of_mul_log_pos
#check matveev_gap3_B_pos_of_solution
#check matveev_gap3_A_pos
#check matveev_gap3_A_pos_of_pos_B
#check matveev_gap3_log_form_upper_bound
#check matveev_gap3_log_form_upper_bound_expanded
#check matveev_gap3_log_form_upper_bound_of_solution
#check matveev_exp_lower_lt_one_and_pos
#check matveev_gap3_A_pow_pos
#check matveev_gap3_B3_pow_pos
#check matveev_gap3_ratio_eq_one_plus_ratio
#check matveev_gap3_log_form_eq_log_ratio
#check matveev_gap3_abs_lambda_eq_log_one_plus_ratio
#check matveev_inequality_real_target
#check baker_bound_gap3_remaining_thm14
#print axioms matveev_C1_floor_eq
#print axioms matveev_thirty_pow_eq_30_pow_6
#print axioms matveev_thirty_pow_eq_729000000
#print axioms matveev_thirty_pow_ne_72900000
#print axioms matveev_thirty_pow_eq_typo_times_ten
#print axioms matveev_C1_floor_pos
#print axioms matveev_thirty_pow_pos
#print axioms matveev_height_B0_eq_numeral
#print axioms matveev_c4_scale_eq_16
#print axioms tate_survivor_63982
#print axioms matveev_thm14_bugeaud_K_eq
#print axioms matveev_thm14_bugeaud_LLL_basis_holds
#print axioms matveev_thm14_log_form_int_ne_zero_zero
#print axioms matveev_thm14_log_form_int_ne_zero_fourteen
#print axioms matveev_thm14_height_gt_onee12
#print axioms matveev_height_log_pos
#print axioms matveev_exp_bound_neg
#print axioms matveev_height_B0_gt_two
#print axioms matveev_log_height_monotone
#print axioms matveev_C_exp_bound_lt_zero_of_pos_log
#print axioms matveev_exp_bound_lt_zero
#print axioms matveev_exp_of_bound_pos_lt_one
#print axioms matveev_exp_of_bound_pos
#print axioms matveev_C_exp_bound_le_neg_onee12
#print axioms matveev_target_exp_lower_pos
#print axioms matveev_target_exp_lower_lt_one
#print axioms matveev_C1_floor_mul_thirty_pow_div10
#print axioms matveev_C1_floor_mul_thirty_pow
#print axioms matveev_C1_floor_mul_thirty_pow_div10_times_ten
#print axioms matveev_C1_floor_mul_thirty_pow_div10_ne_height
#print axioms matveev_height_product_link
#print axioms matveev_C_exp_bound_eq_neg_height_mul_log
#print axioms matveev_C_exp_bound_eq_neg_height_log
#print axioms matveev_target_exp_lower_eq
#print axioms matveev_height_B0_mul_log_pos
#print axioms matveev_C_exp_bound_neg_of_mul_log_pos
#print axioms matveev_gap3_B_pos_of_solution
#print axioms matveev_gap3_A_pos
#print axioms matveev_gap3_A_pos_of_pos_B
#print axioms matveev_gap3_log_form_upper_bound
#print axioms matveev_gap3_log_form_upper_bound_expanded
#print axioms matveev_gap3_log_form_upper_bound_of_solution
#print axioms matveev_exp_lower_lt_one_and_pos
#print axioms matveev_gap3_A_pow_pos
#print axioms matveev_gap3_B3_pow_pos
#print axioms matveev_gap3_ratio_eq_one_plus_ratio
#print axioms matveev_gap3_log_form_eq_log_ratio
#print axioms matveev_gap3_abs_lambda_eq_log_one_plus_ratio
#print axioms matveev_thm14_C_exp_bound_lt_neg_onee12
#print axioms matveev_thm14_constants_hold

end BealLevel26Foundations.BealMatveevThm14
