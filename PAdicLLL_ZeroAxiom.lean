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

/-!
# Integer-form / binary-log LLL no-go (not a v25 mint)

Successor of `v24-v24x-final-padic-lll-nogo`. Nat/Int only: no
`Real.log`, no new axiom. This file does **not** fork Mathlib
and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

The proposed 0-axiom close was:

* a scaled binary log `Nat.log 2 n * scale / 1000` in place of
  `scale * Real.log n`;
* the `ℤ`-linear form `u · a + v · C1_floor` with
  `a = log_nat_approx (B+3) C1_floor`;
* a short-vector witness `|u a + v C1| < C1/2` on a gap-3
  solution, then an LLL lower bound `≥ B0`.

That form always vanishes at `(C1_floor, -a)`, with both
coordinates in the claimed box whenever `B ≤ C1_floor`. The
witness does **not** use `A⁴+B⁴=(B+3)¹³`, so it cannot cut
`B ≤ B0`. Separately, `Nat.sqrt C1_floor < B0_nat`, so a
Minkowski *upper* bound from `det = C1_floor` is also smaller
than `B0`. For `det = C1_floor^2` one has
`Nat.sqrt det = C1_floor > B0`, still an upper bound on a short
vector (the opposite of a cutoff).

`matveev_gap3_lower` is the integer-gap Matveev lower bound on
solutions with `B ≤ B0`, not `¬∃ A`. `not_A_le_B_add_ten_of_gap3`
only kills `A ≤ B+10`. Neither closes
`∀ B, ¬∃ A, A⁴+B⁴=(B+3)¹³`.

`LLL_reduces_bound_to_B0_zero_axiom` /
`beal_gap3_4_4_13_unconditional_zero_axiom` stay `def Prop`.
0 sorry. `C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

set_option maxHeartbeats 400000

namespace BealMatveevBeal.PAdicLLL_ZeroAxiom

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem B0_lt_C1_floor : B0_nat < C1_floor := by
  rw [B0_nat_eq, C1_floor_eq]
  decide

theorem C1_floor_div_two_pos : 0 < C1_floor / 2 := by
  rw [C1_floor_eq]
  decide

/-! ## Minkowski scale: `det = C1` is too small; `det = C1²` is the wrong direction -/

theorem C1_floor_lt_B0_pow_two : C1_floor < B0_nat ^ 2 := by
  rw [C1_floor_eq, B0_nat_eq]
  decide

theorem minkowski_sqrt_C1_lt_B0 : Nat.sqrt C1_floor < B0_nat :=
  Nat.sqrt_lt'.mpr C1_floor_lt_B0_pow_two

theorem sqrt_C1_sq_eq_C1 : Nat.sqrt (C1_floor * C1_floor) = C1_floor :=
  Nat.sqrt_eq C1_floor

/-- `det = C1²` makes `Nat.sqrt det > B0`, but Minkowski still
    *upper*-bounds a short vector. -/
theorem sqrt_C1_sq_gt_B0 : B0_nat < Nat.sqrt (C1_floor * C1_floor) := by
  rw [sqrt_C1_sq_eq_C1]
  exact B0_lt_C1_floor

/-! ## Scaled binary log (not a Real.log Taylor remainder) -/

/-- Scaled `Nat.log 2`. This is **not** a proved approximation of
    `scale * Real.log n`. The `/ 1000` is the displayed placeholder
    from the 0-axiom skeleton. -/
def log_nat_approx (n scale : ℕ) : ℕ :=
  Nat.log 2 n * scale / 1000

theorem log_nat_approx_le_scale_of_log_le {n scale : ℕ}
    (h : Nat.log 2 n ≤ 1000) :
    log_nat_approx n scale ≤ scale := by
  unfold log_nat_approx
  have hmul : Nat.log 2 n * scale ≤ 1000 * scale :=
    Nat.mul_le_mul_right scale h
  have hdiv : Nat.log 2 n * scale / 1000 ≤ 1000 * scale / 1000 :=
    Nat.div_le_div_right hmul
  have hcancel : 1000 * scale / 1000 = scale :=
    Nat.mul_div_right scale (by decide : 0 < 1000)
  exact hdiv.trans_eq hcancel

theorem two_pow_38_gt_C1_add_three : C1_floor + 3 < 2 ^ 38 := by
  rw [C1_floor_eq]
  decide

theorem C1_add_three_ne_zero : C1_floor + 3 ≠ 0 := by
  rw [C1_floor_eq]
  decide

theorem log2_C1_add_three_lt_38 :
    Nat.log 2 (C1_floor + 3) < 38 :=
  (Nat.lt_pow_iff_log_lt (by decide : 1 < 2) C1_add_three_ne_zero).1
    two_pow_38_gt_C1_add_three

theorem thirty_eight_le_thousand : 38 ≤ 1000 := by decide

theorem log2_B_add_three_le_of_B_le_C1 {B : ℕ} (hB : B ≤ C1_floor) :
    Nat.log 2 (B + 3) ≤ Nat.log 2 (C1_floor + 3) :=
  Nat.log_mono_right (Nat.add_le_add_right hB 3)

theorem log2_B_add_three_le_thousand {B : ℕ} (hB : B ≤ C1_floor) :
    Nat.log 2 (B + 3) ≤ 1000 :=
  (log2_B_add_three_le_of_B_le_C1 hB).trans <|
    (Nat.le_of_lt log2_C1_add_three_lt_38).trans thirty_eight_le_thousand

theorem log_nat_approx_le_C1_of_B_le {B : ℕ} (hB : B ≤ C1_floor) :
    log_nat_approx (B + 3) C1_floor ≤ C1_floor :=
  log_nat_approx_le_scale_of_log_le (log2_B_add_three_le_thousand hB)

/-! ## Displayed `ℤ`-lattice: determinant `C1_floor` -/

def lll_lattice_B (B : ℕ) : ℤ × ℤ × ℤ × ℤ :=
  (1, 0, (log_nat_approx (B + 3) C1_floor : ℤ), (C1_floor : ℤ))

theorem lll_lattice_B_det (B : ℕ) :
    (lll_lattice_B B).1 * (lll_lattice_B B).2.2.2 -
      (lll_lattice_B B).2.1 * (lll_lattice_B B).2.2.1 =
      (C1_floor : ℤ) := by
  unfold lll_lattice_B
  simp

/-! ## The integer form always has a kernel vector in the claimed box -/

theorem integer_form_kernel (a c : ℤ) : c * a + (-a) * c = 0 := by
  ring

/-- The naive integer form always has a nontrivial kernel. This is
    why a Nat/Int-only `u·a+v·C1` close cannot cut `B ≤ B0`. -/
theorem nat_int_form_has_kernel (a C1 : ℤ) (hC1 : C1 ≠ 0) :
    ∃ u v : ℤ, (u, v) ≠ (0, 0) ∧ u * a + v * C1 = 0 := by
  refine ⟨C1, -a, ?_, ?_⟩
  · intro h
    exact hC1 (congrArg Prod.fst h)
  · exact integer_form_kernel a C1

theorem displayed_form_vanishes (B : ℕ) :
    (C1_floor : ℤ) * (log_nat_approx (B + 3) C1_floor : ℤ) +
        (-(log_nat_approx (B + 3) C1_floor : ℤ)) * (C1_floor : ℤ) =
      0 :=
  integer_form_kernel _ _

/-- Short-vector witness for **every** `B ≤ C1_floor`, with no
    gap-3 hypothesis. This is the skeleton `lll_short_vector_of_sol`
    minus the unused equation. -/
theorem displayed_kernel_in_box {B : ℕ} (hB : B ≤ C1_floor) :
    ∃ u v : ℤ,
      u.natAbs ≤ C1_floor ∧
        v.natAbs ≤ C1_floor ∧
          (u * (log_nat_approx (B + 3) C1_floor : ℤ) +
              v * (C1_floor : ℤ)).natAbs <
            C1_floor / 2 := by
  set a : ℤ := (log_nat_approx (B + 3) C1_floor : ℤ)
  refine ⟨(C1_floor : ℤ), -a, ?_, ?_, ?_⟩
  · rw [Int.natAbs_ofNat]
  · have hneg : (-a).natAbs = a.natAbs := Int.natAbs_neg a
    have hcast : a.natAbs = log_nat_approx (B + 3) C1_floor :=
      Int.natAbs_ofNat _
    rw [hneg, hcast]
    exact log_nat_approx_le_C1_of_B_le hB
  · have hform :
        (C1_floor : ℤ) * a + (-a) * (C1_floor : ℤ) = 0 :=
      displayed_form_vanishes B
    rw [hform, Int.natAbs_zero]
    exact C1_floor_div_two_pos

/-- Same witness the skeleton extracted from a solution. It does
    not use the solution. -/
theorem lll_short_vector_exists_without_sol {B : ℕ}
    (hB : B ≤ C1_floor) :
    ∃ u v : ℤ,
      u.natAbs ≤ C1_floor ∧
        v.natAbs ≤ C1_floor ∧
          (u * (log_nat_approx (B + 3) C1_floor : ℤ) +
              v * (C1_floor : ℤ)).natAbs <
            C1_floor / 2 :=
  displayed_kernel_in_box hB

/-! ## Kernel claims stay `def Prop` -/

/-- Skeleton close `B > B0 → sol → B ≤ C1 → B ≤ B0`. Uninhabited:
    the displayed short vector exists without a solution. -/
def LLL_reduces_bound_to_B0_zero_axiom : Prop :=
  ∀ (B : ℕ), B0_nat < B →
    ∀ (A : ℕ), B < A →
      A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
        B ≤ C1_floor →
          B ≤ B0_nat

/-- Unconditional gap-3 vanishing. Uninhabited: `matveev_gap3_lower`
    is a Matveev lower bound, not `¬∃ A`; Darmon–Merel is still an
    axiom in `BealTrueV25`. -/
def beal_gap3_4_4_13_unconditional_zero_axiom : Prop :=
  ∀ B : ℕ, ¬ ∃ A : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13

def baker_bound_B0_1e6 : Prop :=
  ∀ (A B C : ℕ), A ^ 4 + B ^ 4 = C ^ 13 → B ≤ B0_nat

def hGen : Prop := LLL_reduces_bound_to_B0_zero_axiom

def hLLL : Prop := LLL_reduces_bound_to_B0_zero_axiom

/-! ## Combined no-go (Nat/Int) -/

theorem p_adic_lll_zero_axiom_unconditional_nogo :
    Nat.sqrt C1_floor < B0_nat ∧
      B0_nat < C1_floor ∧
        C1_floor < B0_nat ^ 2 ∧
          B0_nat < Nat.sqrt (C1_floor * C1_floor) ∧
            (∀ B : ℕ, B ≤ C1_floor →
              ∃ u v : ℤ,
                u.natAbs ≤ C1_floor ∧
                  v.natAbs ≤ C1_floor ∧
                    (u * (log_nat_approx (B + 3) C1_floor : ℤ) +
                        v * (C1_floor : ℤ)).natAbs <
                      C1_floor / 2) := by
  refine ⟨minkowski_sqrt_C1_lt_B0, B0_lt_C1_floor,
    C1_floor_lt_B0_pow_two, sqrt_C1_sq_gt_B0, ?_⟩
  intro B hB
  exact displayed_kernel_in_box hB

#check C1_floor_eq
#check B0_nat_eq
#check B0_lt_C1_floor
#check minkowski_sqrt_C1_lt_B0
#check C1_floor_lt_B0_pow_two
#check sqrt_C1_sq_eq_C1
#check sqrt_C1_sq_gt_B0
#check log_nat_approx
#check log_nat_approx_le_C1_of_B_le
#check lll_lattice_B_det
#check integer_form_kernel
#check nat_int_form_has_kernel
#check displayed_form_vanishes
#check displayed_kernel_in_box
#check lll_short_vector_exists_without_sol
#check LLL_reduces_bound_to_B0_zero_axiom
#check beal_gap3_4_4_13_unconditional_zero_axiom
#check p_adic_lll_zero_axiom_unconditional_nogo
#print axioms C1_floor_eq
#print axioms B0_nat_eq
#print axioms B0_lt_C1_floor
#print axioms minkowski_sqrt_C1_lt_B0
#print axioms C1_floor_lt_B0_pow_two
#print axioms sqrt_C1_sq_eq_C1
#print axioms integer_form_kernel
#print axioms nat_int_form_has_kernel
#print axioms displayed_form_vanishes
#print axioms displayed_kernel_in_box
#print axioms lll_lattice_B_det
#print axioms p_adic_lll_zero_axiom_unconditional_nogo

end BealMatveevBeal.PAdicLLL_ZeroAxiom
