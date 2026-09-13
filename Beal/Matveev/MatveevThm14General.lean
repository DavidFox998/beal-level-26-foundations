/-
Beal Level 26 - Matveev 2000 Thm 1.4 Formalization
Target: inhabit matveev_inequality_real_target from
beal-conjecture/Level26/BealLevel26Foundations
v24.4.0 DOI 10.5281/zenodo.22732209 db7a556 closed upper bound
|Λ| ≤ B^4/A^4, 0 < exp(C) < 1e-12
This file states the lower bound |Λ| > exp(C_exp_bound) for gap-3
A^4 + B^4 = (B+3)^13 toward B0 = 10^6
Axioms on the kernel: [propext, Classical.choice, Quot.sound] only
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

open BealLevel26Foundations.BealMatveevConstants
open BealLevel26Foundations.BealMatveevInequality
open BealLevel26Foundations.BealMatveevInequalityReal
open BealLevel26Foundations.BealMatveevThm14
open BealLevel26Foundations.BealGap3BakerUpperBound

/-! ## v24.4.0 constants, preserved from Level26 -/

/-- v17 PARI floor of Matveev C1 for n = 3, D = 1. -/
def C1_floor : Nat := matveev_C1_floor

/-- height_B0 = C1_floor * 30^6 = 104382751019310000000. -/
def height_B0 : Nat := matveev_height_B0

/-- 30^6 = 729000000. -/
def thirty_pow : Nat := matveev_thirty_pow

/-- C_exp_bound = -height_B0 * log height_B0. -/
noncomputable def C_exp_bound : Real := matveev_C_exp_bound

theorem C1_floor_eq : C1_floor = 143186215390 :=
  matveev_C1_floor_eq

theorem thirty_pow_eq : thirty_pow = 729000000 :=
  matveev_thirty_pow_eq_729000000

theorem thirty_pow_eq_30_pow_6 : thirty_pow = Nat.pow 30 6 :=
  matveev_thirty_pow_eq_30_pow_6

theorem height_B0_eq : height_B0 = 104382751019310000000 :=
  matveev_height_B0_eq_numeral

theorem height_B0_eq_C1_mul_thirty :
    height_B0 = C1_floor * thirty_pow :=
  matveev_height_B0_eq

theorem C_exp_bound_eq :
    C_exp_bound =
      -((height_B0 : Real) * Real.log (height_B0 : Real)) :=
  matveev_C_exp_bound_eq_neg_height_mul_log

/-! ## Gap-3 linear form

    Level26: Λ = 4 log A − 13 log(B+3).
    On a solution, |Λ| = log(1 + B^4/A^4).
    The displayed ratio (B+3)^13 / B^4 is the other
    sign convention; we keep the Level26 form so the
    target is definitionally `matveev_inequality_real_target`. -/

noncomputable def Lambda_gap3 (A B : Nat) : Real :=
  matveev_log_form A B

theorem Lambda_gap3_eq (A B : Nat) :
    Lambda_gap3 A B = matveev_log_form A B :=
  rfl

/-! ## General Matveev 2000 Thm 1.4 (uninhabited)

    Real linear form Λ = ∑ b_i log α_i. Mathlib 4.12 has no
    Matveev theorem. The displayed height product is the
    Level26 specialization C1_floor * 30^6 = height_B0. -/

noncomputable def matveev_linear_form {n : Nat}
    (α : Fin n → Real) (b : Fin n → Int) : Real :=
  (List.ofFn fun i => (b i : Real) * Real.log (α i)).sum

/-- Matveev 2000 Thm 1.4, real case, Level26 constant shape.
    If Λ ≠ 0 then |Λ| > exp(-height_B0 * log height_B0)
    with height_B0 = C1_floor * 30^6.
    Height hypotheses stay as parameters (not Mathlib Weil heights).
    Still a def Prop. -/
def matveev_theorem_1_4_general : Prop :=
  ∀ (n : Nat) (α : Fin n → Real) (b : Fin n → Int),
    (∀ i, (0 : Real) < α i) →
    matveev_linear_form α b ≠ 0 →
    |matveev_linear_form α b| > Real.exp C_exp_bound

/-! ## Gap-3 instance = Level26 `matveev_inequality_real_target` -/

/-- On a gap-3 solution with B > 0,
    |Λ_gap3| > exp(C_exp_bound).
    Same statement as Level26 `matveev_inequality_real_target`
    (includes the `0 < B` hypothesis that file uses). -/
def matveev_theorem_1_4_gap3_target : Prop :=
  matveev_inequality_real_target

theorem matveev_theorem_1_4_gap3_target_eq :
    matveev_theorem_1_4_gap3_target = matveev_inequality_real_target :=
  rfl

/-- Expanded form of the gap-3 target, matching Level26. -/
def matveev_theorem_1_4_gap3_target_expanded : Prop :=
  ∀ (A B : Nat),
    0 < B →
      Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 →
        |Lambda_gap3 A B| > Real.exp C_exp_bound

theorem matveev_theorem_1_4_gap3_target_expanded_eq :
    matveev_theorem_1_4_gap3_target_expanded =
      matveev_inequality_real_target :=
  rfl

/-- Instantiation of the general statement on gap-3.
    Still a def Prop: heights and the n = 3 identification
    are part of the missing proof. -/
def matveev_gap3_of_general : Prop :=
  matveev_theorem_1_4_general → matveev_theorem_1_4_gap3_target

/-- The v25 goal. Exactly `matveev_inequality_real_target`.
    One intentional `sorry`. Not v25 until this is a theorem
    and `baker_bound_gap3` greens. -/
theorem matveev_gap3_lower : matveev_theorem_1_4_gap3_target := by
  sorry

/-! ## Type-correct v25 wiring (no extra sorry)

    `baker_conditional_gap3_full` takes `baker_bound_gap3`,
    not `matveev_gap3_lower`. The missing piece after the
    lower bound is the implication to `baker_bound_gap3`
    (LLL / Bugeaud, still an uninhabited def Prop). -/

def baker_bound_gap3_of_matveev_gap3_lower : Prop :=
  matveev_theorem_1_4_gap3_target → baker_bound_gap3

/-- Displayed name. Same uninhabited Prop as `baker_bound_gap3`. -/
def baker_bound_gap3_holds : Prop := baker_bound_gap3

theorem baker_bound_gap3_holds_of
    (hImp : matveev_theorem_1_4_gap3_target → baker_bound_gap3)
    (_hLower : matveev_theorem_1_4_gap3_target) :
    baker_bound_gap3 :=
  hImp _hLower

/-- Unconditional gap-3 forall, once `baker_bound_gap3` is supplied.
    Already `baker_conditional_gap3_full`. -/
theorem gap3_forall_of_baker
    (hBaker : baker_bound_gap3) :
    ∀ B : Nat,
      ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 :=
  baker_conditional_gap3_full hBaker

#check C1_floor
#check height_B0
#check C_exp_bound
#check Lambda_gap3
#check matveev_theorem_1_4_general
#check matveev_theorem_1_4_gap3_target
#check matveev_gap3_lower
#check baker_bound_gap3_holds
#check baker_conditional_gap3_full
#check BealLevel26Foundations.BealBakerB0ReductionCertificate.baker_bound_gap3_of_LLL
#print axioms C1_floor_eq
#print axioms height_B0_eq
#print axioms C_exp_bound_eq
#print axioms gap3_forall_of_baker

end BealMatveevBeal
