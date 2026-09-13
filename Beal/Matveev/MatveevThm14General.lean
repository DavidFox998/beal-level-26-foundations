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

/-! ## Height facts on a gap-3 solution

    `A < B+3` is false: `eq_implies_A_gt_B` gives `B < A`, and
    `A^4 = (B+3)^13 - B^4` so `A ≈ (B+3)^{13/4}`.
    Usable bounds: `1 < A`, `1 < B+3`, `A^4 < (B+3)^13`,
    and `log A < (13/4) log(B+3)`.
    `|Λ| = log(1 + B^4/A^4)` is already Level26. -/

lemma height_bound_gap3 (A B : ℕ)
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (0 : ℝ) < (A : ℝ) ∧
      (1 : ℝ) < (A : ℝ) ∧
      (1 : ℝ) < (B + 3 : ℝ) ∧
      A ^ 4 < (B + 3) ^ 13 := by
  have hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := h
  have hApos : 0 < A := matveev_gap3_A_pos_of_pos_B hsol hB
  have hAgt : B < A := eq_implies_A_gt_B hsol hB
  have hAgt1 : 1 < A := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) hAgt
  have hB4 : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hB
  have hApow : A ^ 4 < (B + 3) ^ 13 := by
    have hlt : A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
    rw [h] at hlt
    exact hlt
  refine ⟨?_, ?_, ?_, hApow⟩
  · exact_mod_cast hApos
  · exact_mod_cast hAgt1
  · have hBposR : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
    linarith

lemma logA_lt_thirteen_fourths_logB3 (A B : ℕ)
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    Real.log (A : ℝ) < (13 / 4 : ℝ) * Real.log ((B + 3 : ℕ) : ℝ) := by
  have hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := h
  have hΛ := (matveev_gap3_log_form_upper_bound hsol hB).1
  have hlt : (4 : ℝ) * Real.log (A : ℝ) <
      (13 : ℝ) * Real.log ((B + 3 : ℕ) : ℝ) := by
    unfold matveev_log_form at hΛ
    linarith
  calc
    Real.log (A : ℝ) = ((4 : ℝ) * Real.log (A : ℝ)) / 4 := by ring
    _ < ((13 : ℝ) * Real.log ((B + 3 : ℕ) : ℝ)) / 4 :=
      (div_lt_div_right (by norm_num : (0 : ℝ) < 4)).mpr hlt
    _ = (13 / 4 : ℝ) * Real.log ((B + 3 : ℕ) : ℝ) := by ring

lemma abs_Lambda_eq_log_one_plus (A B : ℕ)
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    |Lambda_gap3_real (A : ℝ) (B : ℝ)| =
      Real.log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := h
  rw [Lambda_gap3_real_nat, matveev_gap3_abs_lambda_eq_log_one_plus_ratio hsol]

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

/-- Instantiation sketch: on a gap-3 solution, `1 < A`, `1 < B+3`,
    `log A < (13/4) log(B+3)`, `|bᵢ| = 13`. The product
    `C1_floor * A1 * A2 * B0 ≤ height_B0 * log height_B0`
    is still a def Prop (not `A1 ≤ log(B+3)`). -/
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
#print axioms height_bound_gap3
#print axioms logA_lt_thirteen_fourths_logB3
#print axioms abs_Lambda_eq_log_one_plus
#print axioms gap3_target_eq_matveev_inequality
#print axioms C_exp_bound_real_eq_level26
#print axioms Lambda_gap3_real_nat

end BealMatveevBeal
