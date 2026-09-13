/-
Beal Level 26 - Matveev 2000 Thm 1.4 General + Gap3 Instance
v24.4.0 db7a556 / 22732209 closed |Λ| ≤ B^4/A^4, 0<exp(C)<1e-12,
conditional B^4(1+exp(C))>exp(C)(B+3)^13 toward B0=10^6
Goal: inhabit matveev_inequality_real_target = matveev_theorem_1_4_gap3_target
for v25 B≤B0 unconditional
Axioms: [propext, Classical.choice, Quot.sound] only
0 sorry when done (sorry now intentional on matveev_gap3_lower)
-/
import Mathlib
import BealConjecture.Level26.BealLevel26Foundations.BealMatveevThm14
import BealConjecture.Level26.BealLevel26Foundations.BealBakerB0ReductionCertificate
import BealLevel26Foundations.Beal.FullProof.BealMatveevConstants
import BealLevel26Foundations.Beal.FullProof.BealMatveevInequality
import BealLevel26Foundations.Beal.FullProof.BealMatveevInequalityReal
import BealLevel26Foundations.Beal.FullProof.BealMatveevThm14
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

namespace BealMatveevBeal

open Real
open BealLevel26Foundations.BealMatveevConstants
open BealLevel26Foundations.BealMatveevInequality
open BealLevel26Foundations.BealMatveevInequalityReal
open BealLevel26Foundations.BealMatveevThm14
open BealLevel26Foundations.BealGap3BakerUpperBound

/-! ## v24.4.0 Nat constants, 0-axiom decide -/

def C1_floor : ℕ := 143186215390
def thirty_pow_six : ℕ := 729000000 -- 30^6
def height_B0_nat : ℕ := 104382751019310000000 -- C1_floor * 30^6

theorem C1_floor_eq : C1_floor = 143186215390 := by
  decide

theorem thirty_pow_six_eq : thirty_pow_six = 729000000 := by
  decide

theorem thirty_pow_six_eq_30_pow_6 : thirty_pow_six = Nat.pow 30 6 := by
  decide

theorem height_B0_eq : height_B0_nat = C1_floor * thirty_pow_six := by
  decide

theorem height_B0_nat_eq_numeral :
    height_B0_nat = 104382751019310000000 := by
  decide

theorem C1_floor_eq_level26 : C1_floor = matveev_C1_floor :=
  rfl

theorem thirty_pow_six_eq_level26 : thirty_pow_six = matveev_thirty_pow :=
  rfl

theorem height_B0_nat_eq_level26 : height_B0_nat = matveev_height_B0 :=
  rfl

/-! ## Real versions -/

noncomputable def C1_floor_real : ℝ := (C1_floor : ℝ)
noncomputable def height_B0_real : ℝ := (height_B0_nat : ℝ)
noncomputable def C_exp_bound_real : ℝ :=
  -height_B0_real * Real.log height_B0_real

theorem C_exp_bound_real_eq_level26 :
    C_exp_bound_real = matveev_C_exp_bound := by
  have h := matveev_C_exp_bound_eq_neg_height_mul_log
  simpa [C_exp_bound_real, height_B0_real, height_B0_nat_eq_level26,
    mul_comm, mul_left_comm, mul_assoc, neg_mul] using h.symm

/-! ## Level 26 Λ form: 4 log A − 13 log(B+3) -/

noncomputable def Lambda_gap3_real (A B : ℝ) : ℝ :=
  4 * Real.log A - 13 * Real.log (B + 3)

theorem Lambda_gap3_real_nat (A B : ℕ) :
    Lambda_gap3_real (A : ℝ) (B : ℝ) = matveev_log_form A B := by
  have hcast : ((B : ℝ) + 3) = ((B + 3 : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_ofNat]
  unfold Lambda_gap3_real matveev_log_form
  rw [hcast]

/-! ## Matveev 2000 Thm 1.4 general, gap-3 n=2 heights

    α₁ = A, α₂ = B+3, b₁ = 4, b₂ = −13, D = 1.
    Heights are the displayed logs (not Mathlib Weil heights).
    Still a def Prop. Mathlib 4.12 has no Matveev theorem. -/

def matveev_theorem_1_4_general : Prop :=
  ∀ (A B : ℝ) (_hA : 1 < A) (_hB : 1 < B),
    let A1 := Real.log A
    let A2 := Real.log (B + 3)
    let b : ℝ := ((max (4 : ℕ) 13 : ℕ) : ℝ)
    let B0 := Real.log b + Real.log (Real.log b) + A1 + A2
    |Lambda_gap3_real A B| >
      Real.exp (-C1_floor_real * (A1 * A2) * B0)

/-- Instantiation sketch: on a gap-3 solution the logs are
    bounded by log(B+3), |bᵢ| ≤ 13, and the product is
    intended ≤ height_B0_real. Still a def Prop. -/
def matveev_gap3_of_general : Prop :=
  matveev_theorem_1_4_general →
    BealLevel26Foundations.BealMatveevThm14.matveev_inequality_real_target

/-! ## Gap-3 target = Level26 `matveev_inequality_real_target`

    Displayed with `Lambda_gap3_real` / `C_exp_bound_real`.
    The named target itself is the Level26 def so the
    `rfl` link stays definitional. -/

def matveev_theorem_1_4_gap3_target : Prop :=
  BealLevel26Foundations.BealMatveevThm14.matveev_inequality_real_target

theorem gap3_target_eq_matveev_inequality :
    matveev_theorem_1_4_gap3_target =
      BealLevel26Foundations.BealMatveevThm14.matveev_inequality_real_target := by
  rfl

/-- User-facing expanded body (Nat solution, Real Λ). -/
def matveev_theorem_1_4_gap3_target_expanded : Prop :=
  ∀ A B : ℕ,
    0 < B →
      A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
        |Lambda_gap3_real (A : ℝ) (B : ℝ)| > Real.exp C_exp_bound_real

theorem gap3_target_expanded_eq_level26 :
    matveev_theorem_1_4_gap3_target_expanded =
      BealLevel26Foundations.BealMatveevThm14.matveev_inequality_real_target := by
  apply propext
  constructor
  · intro h A B hB hsol
    have hΛ := h A B hB hsol
    rw [Lambda_gap3_real_nat, C_exp_bound_real_eq_level26] at hΛ
    exact hΛ
  · intro h A B hB hsol
    have hΛ := h A B hB hsol
    rw [← Lambda_gap3_real_nat, ← C_exp_bound_real_eq_level26] at hΛ
    exact hΛ

/-- The v25 goal. Exactly `matveev_inequality_real_target`.
    One intentional `sorry`. Not v25. -/
theorem matveev_gap3_lower : matveev_theorem_1_4_gap3_target := by
  sorry

/-! ## Type-correct v25 wiring (no extra sorry)

    `baker_conditional_gap3_full` takes `baker_bound_gap3`.
    The LLL step `matveev_inequality_real_target → baker_bound_gap3`
    is still an uninhabited def Prop. See
    beal-conjecture `Level26/BakerBoundGap3Holds.lean`. -/

def baker_bound_gap3_of_matveev_gap3_lower : Prop :=
  matveev_theorem_1_4_gap3_target → baker_bound_gap3

def baker_bound_gap3_holds : Prop := baker_bound_gap3

theorem baker_bound_gap3_holds_of
    (hImp : matveev_theorem_1_4_gap3_target → baker_bound_gap3)
    (hLower : matveev_theorem_1_4_gap3_target) :
    baker_bound_gap3 :=
  hImp hLower

theorem gap3_forall_of_baker
    (hBaker : baker_bound_gap3) :
    ∀ B : ℕ,
      ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 :=
  baker_conditional_gap3_full hBaker

#check C1_floor
#check height_B0_nat
#check C_exp_bound_real
#check Lambda_gap3_real
#check matveev_theorem_1_4_general
#check matveev_theorem_1_4_gap3_target
#check matveev_gap3_lower
#check baker_bound_gap3_holds
#print axioms C1_floor_eq
#print axioms height_B0_eq
#print axioms gap3_target_eq_matveev_inequality
#print axioms C_exp_bound_real_eq_level26
#print axioms Lambda_gap3_real_nat

end BealMatveevBeal
