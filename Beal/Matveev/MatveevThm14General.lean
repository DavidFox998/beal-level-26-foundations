/-
Beal Level 26 - Matveev 2000 Thm 1.4 General + Gap3 Instance
v24.4.0 db7a556 / 22732209 closed |Λ| ≤ B^4/A^4, 0<exp(C)<1e-12,
conditional B^4(1+exp(C))>exp(C)(B+3)^13 toward B0=10^6
Goal: inhabit matveev_inequality_real_target = matveev_theorem_1_4_gap3_target
for v25 B≤B0 unconditional
Axioms: [propext, Classical.choice, Quot.sound] only
0 sorry except matveev_gap3_lower. Product inhabited only for B+3 ≤ height_B0.
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

/-- Honest gap-3 bounds. Not `A < B+3`: `eq_implies_A_gt_B` gives
    `B < A`, and `A ≈ (B+3)^{13/4}`. -/
lemma gap3_A_bounds (A B : ℕ)
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    0 < A ∧
      1 < A ∧
      1 < B + 3 ∧
      A ^ 4 < (B + 3) ^ 13 ∧
      Real.log (A : ℝ) < (13 / 4 : ℝ) * Real.log (B + 3 : ℝ) := by
  have hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := h
  have hb := height_bound_gap3 A B h hB
  have hApos : 0 < A := matveev_gap3_A_pos_of_pos_B hsol hB
  have hAgt : B < A := eq_implies_A_gt_B hsol hB
  have hAgt1 : 1 < A := Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) hAgt
  have hB3 : 1 < B + 3 :=
    Nat.lt_of_lt_of_le (by decide : 1 < 4)
      (Nat.add_le_add_right (Nat.succ_le_of_lt hB) 3)
  refine ⟨hApos, hAgt1, hB3, hb.2.2.2, ?_⟩
  have hlog := logA_lt_thirteen_fourths_logB3 A B h hB
  have hcast : ((B + 3 : ℕ) : ℝ) = (B + 3 : ℝ) := by
    rw [Nat.cast_add, Nat.cast_ofNat]
  rwa [hcast] at hlog

lemma abs_Lambda_eq_log_one_plus (A B : ℕ)
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    |Lambda_gap3_real (A : ℝ) (B : ℝ)| =
      Real.log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have hsol : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := h
  rw [Lambda_gap3_real_nat, matveev_gap3_abs_lambda_eq_log_one_plus_ratio hsol]

/-! ## Log comparisons used by the height-restricted product

    `log 13 < 3`, `log(log 13) < 1`, `log height_B0 < 63`.
    No `A < B+3`. -/

lemma twenty_seven_div_ten_lt_exp_one : (27 / 10 : ℝ) < Real.exp 1 :=
  lt_trans (by norm_num) Real.exp_one_gt_d9

lemma exp_one_pow_eq_exp_nat (n : ℕ) : Real.exp 1 ^ n = Real.exp n := by
  rw [← Real.exp_nat_mul, mul_one]

lemma exp_three_gt_twenty_seven_div_ten_pow :
    (27 / 10 : ℝ) ^ 3 < Real.exp 3 := by
  have hpow : (27 / 10 : ℝ) ^ 3 < Real.exp 1 ^ 3 :=
    pow_lt_pow_left twenty_seven_div_ten_lt_exp_one (by norm_num)
      (by decide : (3 : ℕ) ≠ 0)
  rwa [exp_one_pow_eq_exp_nat 3] at hpow

lemma exp_three_gt_thirteen : (13 : ℝ) < Real.exp 3 :=
  lt_trans (by norm_num : (13 : ℝ) < (27 / 10 : ℝ) ^ 3)
    exp_three_gt_twenty_seven_div_ten_pow

lemma log_thirteen_lt_three : Real.log (13 : ℝ) < 3 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 13)).2 exp_three_gt_thirteen

lemma log_thirteen_gt_one : (1 : ℝ) < Real.log (13 : ℝ) := by
  have hpos : (0 : ℝ) < (13 : ℝ) := by norm_num
  have hexp : Real.exp 1 < (13 : ℝ) :=
    lt_trans Real.exp_one_lt_d9 (by norm_num)
  exact (Real.lt_log_iff_exp_lt hpos).2 hexp

lemma exp_two_gt_twenty_seven_div_ten_pow :
    (27 / 10 : ℝ) ^ 2 < Real.exp 2 := by
  have hpow : (27 / 10 : ℝ) ^ 2 < Real.exp 1 ^ 2 :=
    pow_lt_pow_left twenty_seven_div_ten_lt_exp_one (by norm_num)
      (by decide : (2 : ℕ) ≠ 0)
  rwa [exp_one_pow_eq_exp_nat 2] at hpow

lemma two_lt_exp_seven_div_ten : (2 : ℝ) < Real.exp (7 / 10) := by
  have hlog : Real.log 2 < (7 / 10 : ℝ) :=
    lt_trans Real.log_two_lt_d9 (by norm_num)
  exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 2)).1 hlog

lemma thirteen_lt_exp_twenty_seven_div_ten :
    (13 : ℝ) < Real.exp (27 / 10) := by
  have hadd : Real.exp (27 / 10) = Real.exp 2 * Real.exp (7 / 10) := by
    rw [← Real.exp_add]
    norm_num
  have hmul : (27 / 10 : ℝ) ^ 2 * (2 : ℝ) <
      Real.exp 2 * Real.exp (7 / 10) :=
    mul_lt_mul exp_two_gt_twenty_seven_div_ten_pow
      (le_of_lt two_lt_exp_seven_div_ten) (by norm_num)
      (le_of_lt (Real.exp_pos 2))
  have hnum : (13 : ℝ) < (27 / 10 : ℝ) ^ 2 * 2 := by norm_num
  calc
    (13 : ℝ) < (27 / 10 : ℝ) ^ 2 * 2 := hnum
    _ < Real.exp 2 * Real.exp (7 / 10) := hmul
    _ = Real.exp (27 / 10) := hadd.symm

lemma log_log_thirteen_lt_one :
    Real.log (Real.log (13 : ℝ)) < 1 := by
  have hlogpos : (0 : ℝ) < Real.log (13 : ℝ) :=
    lt_trans (by norm_num) log_thirteen_gt_one
  have hinner : Real.log (13 : ℝ) < Real.exp 1 := by
    have h13 : (13 : ℝ) < Real.exp (Real.exp 1) :=
      lt_trans thirteen_lt_exp_twenty_seven_div_ten
        (Real.exp_lt_exp.mpr twenty_seven_div_ten_lt_exp_one)
    exact (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 13)).2 h13
  exact (Real.log_lt_iff_lt_exp hlogpos).2 hinner

lemma log_ten_lt_three : Real.log (10 : ℝ) < 3 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 10)).2
    (lt_trans (by norm_num : (10 : ℝ) < 13) exp_three_gt_thirteen)

lemma height_B0_nat_lt_ten_pow_21 :
    height_B0_nat < Nat.pow 10 21 := by
  decide

lemma C1_floor_real_pos : (0 : ℝ) < C1_floor_real := by
  unfold C1_floor_real C1_floor
  norm_num

lemma height_B0_real_pos : (0 : ℝ) < height_B0_real := by
  unfold height_B0_real height_B0_nat
  norm_num

lemma height_B0_real_gt_one : (1 : ℝ) < height_B0_real := by
  unfold height_B0_real height_B0_nat
  norm_num

lemma log_height_B0_pos : (0 : ℝ) < Real.log height_B0_real :=
  Real.log_pos height_B0_real_gt_one

lemma height_B0_real_eq_C1_mul_thirty :
    height_B0_real = C1_floor_real * (thirty_pow_six : ℝ) := by
  unfold height_B0_real C1_floor_real
  rw [height_B0_eq, Nat.cast_mul]

lemma log_height_B0_lt_sixty_three :
    Real.log height_B0_real < 63 := by
  have hHlt : height_B0_real < (10 : ℝ) ^ 21 := by
    have hnat := height_B0_nat_lt_ten_pow_21
    unfold height_B0_real
    exact_mod_cast hnat
  have hlog : Real.log height_B0_real < Real.log ((10 : ℝ) ^ 21) :=
    Real.log_lt_log height_B0_real_pos hHlt
  have hpow : Real.log ((10 : ℝ) ^ 21) = (21 : ℝ) * Real.log 10 :=
    Real.log_pow (10 : ℝ) 21
  have h21 : (21 : ℝ) * Real.log 10 < (21 : ℝ) * 3 :=
    mul_lt_mul_of_pos_left log_ten_lt_three (by norm_num)
  have h63 : (21 : ℝ) * 3 = 63 := by norm_num
  calc
    Real.log height_B0_real < Real.log ((10 : ℝ) ^ 21) := hlog
    _ = (21 : ℝ) * Real.log 10 := hpow
    _ < (21 : ℝ) * 3 := h21
    _ = 63 := h63

/-! ## Matveev 2000 Thm 1.4 general, gap-3 n=2 heights

    α₁ = A, α₂ = B+3 (not the Nat `B`), b₁ = 4, b₂ = −13, D = 1.
    `1 < B` is the wrong hyp: Nat `B = 1` occurs, while `1 < B+3`.
    Heights are the displayed logs (not Mathlib Weil heights).
    Still a def Prop. Mathlib 4.12 has no Matveev theorem. -/

noncomputable def matveev_height_product (α1 α2 : ℝ) : ℝ :=
  C1_floor_real * Real.log α1 * Real.log α2 *
    (Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ)) +
      Real.log α1 + Real.log α2)

def matveev_theorem_1_4_general : Prop :=
  ∀ (α1 α2 : ℝ) (_h1 : 1 < α1) (_h2 : 1 < α2),
    |4 * Real.log α1 - 13 * Real.log α2| >
      Real.exp (-matveev_height_product α1 α2)

/-- Unrestricted product on every gap-3 solution. Not a theorem:
    the left side is O((log(B+3))³) and the right side is constant,
    so a hypothetical huge solution would violate it. Bounding `B`
    is the Baker goal, so this stays a `def Prop`. -/
def matveev_product_bound_gap3 : Prop :=
  ∀ A B : ℕ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
      0 < B →
        matveev_height_product (A : ℝ) (B + 3 : ℝ) ≤
          height_B0_real * Real.log height_B0_real

/-- Instantiation: general + unrestricted product ⇒ target.
    Proved as `matveev_gap3_lower_of`. -/
def matveev_gap3_of_general : Prop :=
  matveev_theorem_1_4_general →
    matveev_product_bound_gap3 →
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

/-- Crude majorant used when `B+3 ≤ height_B0`:
    `(13/4) log H · (4 + (17/4) log H) < 30^6`. -/
lemma matveev_height_majorant_lt_thirty_pow_six :
    (13 / 4 : ℝ) * Real.log height_B0_real *
      (4 + (17 / 4 : ℝ) * Real.log height_B0_real) <
      (thirty_pow_six : ℝ) := by
  have hlog := log_height_B0_lt_sixty_three
  have hlogpos := log_height_B0_pos
  have hleft : (13 / 4 : ℝ) * Real.log height_B0_real < (819 / 4 : ℝ) := by
    have : (13 / 4 : ℝ) * 63 = (819 / 4 : ℝ) := by norm_num
    calc
      (13 / 4 : ℝ) * Real.log height_B0_real
          < (13 / 4 : ℝ) * 63 :=
        mul_lt_mul_of_pos_left hlog (by norm_num)
      _ = 819 / 4 := this
  have hsum : 4 + (17 / 4 : ℝ) * Real.log height_B0_real < (1087 / 4 : ℝ) := by
    have hinner : (17 / 4 : ℝ) * Real.log height_B0_real < (1071 / 4 : ℝ) := by
      have : (17 / 4 : ℝ) * 63 = (1071 / 4 : ℝ) := by norm_num
      calc
        (17 / 4 : ℝ) * Real.log height_B0_real
            < (17 / 4 : ℝ) * 63 :=
          mul_lt_mul_of_pos_left hlog (by norm_num)
        _ = 1071 / 4 := this
    have : (4 : ℝ) + 1071 / 4 = 1087 / 4 := by norm_num
    linarith [hinner]
  have hsumpos : (0 : ℝ) < 4 + (17 / 4 : ℝ) * Real.log height_B0_real := by
    nlinarith
  have hprod : (13 / 4 : ℝ) * Real.log height_B0_real *
      (4 + (17 / 4 : ℝ) * Real.log height_B0_real) <
      (819 / 4 : ℝ) * (1087 / 4 : ℝ) :=
    mul_lt_mul hleft (le_of_lt hsum) hsumpos (by norm_num)
  have hnum : (819 / 4 : ℝ) * (1087 / 4 : ℝ) = (890253 / 16 : ℝ) := by
    norm_num
  have hlt : (890253 / 16 : ℝ) < (thirty_pow_six : ℝ) := by
    unfold thirty_pow_six
    norm_num
  calc
    (13 / 4 : ℝ) * Real.log height_B0_real *
        (4 + (17 / 4 : ℝ) * Real.log height_B0_real)
        < (819 / 4 : ℝ) * (1087 / 4 : ℝ) := hprod
    _ = 890253 / 16 := hnum
    _ < (thirty_pow_six : ℝ) := hlt

/-- The product that *is* a theorem: on a gap-3 solution with
    `B+3 ≤ height_B0` (which includes the v25 range `B ≤ 10^6`).
    Uses `log A < (13/4) log(B+3)`, never `A < B+3`. -/
theorem matveev_product_bound_of_B3_le_height (A B : ℕ)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B)
    (hB3 : B + 3 ≤ height_B0_nat) :
    matveev_height_product (A : ℝ) (B + 3 : ℝ) ≤
      height_B0_real * Real.log height_B0_real := by
  have hb := gap3_A_bounds A B hsol hB
  have hAgt1 : (1 : ℝ) < (A : ℝ) := by exact_mod_cast hb.2.1
  have hB3gt1 : (1 : ℝ) < (B + 3 : ℝ) := by exact_mod_cast hb.2.2.1
  have hB3pos : (0 : ℝ) < (B + 3 : ℝ) := lt_trans (by norm_num) hB3gt1
  have hlogApos : (0 : ℝ) < Real.log (A : ℝ) := Real.log_pos hAgt1
  have hlogB3pos : (0 : ℝ) < Real.log (B + 3 : ℝ) := Real.log_pos hB3gt1
  have hlog13pos : (0 : ℝ) < Real.log (13 : ℝ) :=
    lt_trans (by norm_num) log_thirteen_gt_one
  have hloglog13pos : (0 : ℝ) < Real.log (Real.log (13 : ℝ)) :=
    Real.log_pos log_thirteen_gt_one
  have hB3R : (B + 3 : ℝ) ≤ height_B0_real := by
    unfold height_B0_real
    exact_mod_cast hB3
  have hlogB3le : Real.log (B + 3 : ℝ) ≤ Real.log height_B0_real :=
    Real.log_le_log hB3pos hB3R
  have hlogAlt : Real.log (A : ℝ) < (13 / 4 : ℝ) * Real.log (B + 3 : ℝ) :=
    hb.2.2.2.2
  have hlogAle : Real.log (A : ℝ) ≤ (13 / 4 : ℝ) * Real.log height_B0_real := by
    have hmid : (13 / 4 : ℝ) * Real.log (B + 3 : ℝ) ≤
        (13 / 4 : ℝ) * Real.log height_B0_real :=
      mul_le_mul_of_nonneg_left hlogB3le (by norm_num)
    exact le_trans (le_of_lt hlogAlt) hmid
  have hB0 : Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ)) +
      Real.log (A : ℝ) + Real.log (B + 3 : ℝ) ≤
      Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ)) +
        (13 / 4 : ℝ) * Real.log height_B0_real + Real.log height_B0_real :=
    add_le_add
      (add_le_add (le_refl _) hlogAle) hlogB3le
  have hB0' : Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ)) +
      (13 / 4 : ℝ) * Real.log height_B0_real + Real.log height_B0_real ≤
      4 + (17 / 4 : ℝ) * Real.log height_B0_real := by
    have hc : Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ)) < 4 := by
      have := add_lt_add log_thirteen_lt_three log_log_thirteen_lt_one
      linarith
    calc
      Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ)) +
          (13 / 4 : ℝ) * Real.log height_B0_real + Real.log height_B0_real
          = (Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ))) +
              ((13 / 4 : ℝ) * Real.log height_B0_real +
                Real.log height_B0_real) := by
        ring
      _ ≤ 4 + ((13 / 4 : ℝ) * Real.log height_B0_real +
            Real.log height_B0_real) :=
        add_le_add (le_of_lt hc) (le_refl _)
      _ = 4 + (17 / 4 : ℝ) * Real.log height_B0_real := by
        ring
  have hB0le : Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ)) +
      Real.log (A : ℝ) + Real.log (B + 3 : ℝ) ≤
      4 + (17 / 4 : ℝ) * Real.log height_B0_real :=
    le_trans hB0 hB0'
  have hB0pos : (0 : ℝ) ≤
      Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ)) +
        Real.log (A : ℝ) + Real.log (B + 3 : ℝ) :=
    add_nonneg (add_nonneg (add_nonneg (le_of_lt hlog13pos)
      (le_of_lt hloglog13pos)) (le_of_lt hlogApos)) (le_of_lt hlogB3pos)
  have hprod : C1_floor_real * Real.log (A : ℝ) * Real.log (B + 3 : ℝ) *
      (Real.log (13 : ℝ) + Real.log (Real.log (13 : ℝ)) +
        Real.log (A : ℝ) + Real.log (B + 3 : ℝ)) ≤
      C1_floor_real * ((13 / 4 : ℝ) * Real.log height_B0_real) *
        Real.log height_B0_real *
        (4 + (17 / 4 : ℝ) * Real.log height_B0_real) := by
    have h1 : C1_floor_real * Real.log (A : ℝ) ≤
        C1_floor_real * ((13 / 4 : ℝ) * Real.log height_B0_real) :=
      mul_le_mul_of_nonneg_left hlogAle (le_of_lt C1_floor_real_pos)
    have h2 : C1_floor_real * Real.log (A : ℝ) * Real.log (B + 3 : ℝ) ≤
        C1_floor_real * ((13 / 4 : ℝ) * Real.log height_B0_real) *
          Real.log height_B0_real :=
      mul_le_mul h1 hlogB3le (le_of_lt hlogB3pos)
        (mul_nonneg (le_of_lt C1_floor_real_pos)
          (mul_nonneg (by norm_num) (le_of_lt log_height_B0_pos)))
    exact mul_le_mul h2 hB0le hB0pos
      (mul_nonneg (mul_nonneg (le_of_lt C1_floor_real_pos)
          (mul_nonneg (by norm_num) (le_of_lt log_height_B0_pos)))
        (le_of_lt log_height_B0_pos))
  have hmajor : C1_floor_real * ((13 / 4 : ℝ) * Real.log height_B0_real) *
      Real.log height_B0_real *
      (4 + (17 / 4 : ℝ) * Real.log height_B0_real) ≤
      height_B0_real * Real.log height_B0_real := by
    have hfactor : (13 / 4 : ℝ) * Real.log height_B0_real *
        (4 + (17 / 4 : ℝ) * Real.log height_B0_real) <
        (thirty_pow_six : ℝ) :=
      matveev_height_majorant_lt_thirty_pow_six
    have hreassoc :
        C1_floor_real * ((13 / 4 : ℝ) * Real.log height_B0_real) *
          Real.log height_B0_real *
          (4 + (17 / 4 : ℝ) * Real.log height_B0_real) =
          C1_floor_real * Real.log height_B0_real *
            ((13 / 4 : ℝ) * Real.log height_B0_real *
              (4 + (17 / 4 : ℝ) * Real.log height_B0_real)) := by
      ring
    have hrhs : height_B0_real * Real.log height_B0_real =
        C1_floor_real * Real.log height_B0_real * (thirty_pow_six : ℝ) := by
      rw [height_B0_real_eq_C1_mul_thirty]
      ring
    have hscale : C1_floor_real * Real.log height_B0_real *
        ((13 / 4 : ℝ) * Real.log height_B0_real *
          (4 + (17 / 4 : ℝ) * Real.log height_B0_real)) ≤
        C1_floor_real * Real.log height_B0_real * (thirty_pow_six : ℝ) :=
      mul_le_mul_of_nonneg_left (le_of_lt hfactor)
        (mul_nonneg (le_of_lt C1_floor_real_pos) (le_of_lt log_height_B0_pos))
    calc
      C1_floor_real * ((13 / 4 : ℝ) * Real.log height_B0_real) *
          Real.log height_B0_real *
          (4 + (17 / 4 : ℝ) * Real.log height_B0_real) =
          C1_floor_real * Real.log height_B0_real *
            ((13 / 4 : ℝ) * Real.log height_B0_real *
              (4 + (17 / 4 : ℝ) * Real.log height_B0_real)) := hreassoc
      _ ≤ C1_floor_real * Real.log height_B0_real * (thirty_pow_six : ℝ) :=
        hscale
      _ = height_B0_real * Real.log height_B0_real := hrhs.symm
  unfold matveev_height_product
  exact le_trans hprod hmajor

/-- v25 range: `B ≤ 10^6` implies `B+3 ≤ height_B0`. -/
theorem matveev_product_bound_of_B_le_B0 (A B : ℕ)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B)
    (hB0 : B ≤ 1000000) :
    matveev_height_product (A : ℝ) (B + 3 : ℝ) ≤
      height_B0_real * Real.log height_B0_real := by
  have hB3 : B + 3 ≤ height_B0_nat := by
    have h1 : B + 3 ≤ 1000003 := Nat.add_le_add_right hB0 3
    have h2 : 1000003 ≤ height_B0_nat := by
      unfold height_B0_nat
      decide
    exact h1.trans h2
  exact matveev_product_bound_of_B3_le_height A B hsol hB hB3

lemma Lambda_gap3_real_eq_alpha (A B : ℕ) :
    Lambda_gap3_real (A : ℝ) (B : ℝ) =
      4 * Real.log (A : ℝ) - 13 * Real.log (B + 3 : ℝ) := by
  unfold Lambda_gap3_real
  rfl

/-- Composition: Matveev 1.4 general + unrestricted product ⇒ target.
    Sorry-free. Does not inhabit either hypothesis. -/
theorem matveev_gap3_lower_of
    (hGen : matveev_theorem_1_4_general)
    (hProd : matveev_product_bound_gap3) :
    matveev_theorem_1_4_gap3_target := by
  have hexpanded : matveev_theorem_1_4_gap3_target_expanded := by
    intro A B hB hsol
    have hb := gap3_A_bounds A B hsol hB
    have hA1 : (1 : ℝ) < (A : ℝ) := by exact_mod_cast hb.2.1
    have hA2 : (1 : ℝ) < (B + 3 : ℝ) := by exact_mod_cast hb.2.2.1
    have hG := hGen (A : ℝ) (B + 3 : ℝ) hA1 hA2
    have hP := hProd A B hsol hB
    have hneg : -matveev_height_product (A : ℝ) (B + 3 : ℝ) ≥
        C_exp_bound_real := by
      unfold C_exp_bound_real
      have := neg_le_neg hP
      simpa [neg_mul] using this
    have hexp : Real.exp C_exp_bound_real ≤
        Real.exp (-matveev_height_product (A : ℝ) (B + 3 : ℝ)) :=
      Real.exp_le_exp.mpr hneg
    exact lt_of_le_of_lt hexp hG
  change matveev_inequality_real_target
  exact gap3_target_expanded_eq_level26 ▸ hexpanded

/-- The v25 goal. Exactly `matveev_inequality_real_target`.
    One intentional `sorry`: Mathlib has no Matveev 2000 Thm 1.4, and
    the unrestricted product is not a theorem. Not v25. -/
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
#check gap3_A_bounds
#check matveev_theorem_1_4_general
#check matveev_product_bound_gap3
#check matveev_product_bound_of_B3_le_height
#check matveev_product_bound_of_B_le_B0
#check matveev_gap3_lower_of
#check matveev_theorem_1_4_gap3_target
#check matveev_gap3_lower
#check baker_bound_gap3_holds
#print axioms C1_floor_eq
#print axioms height_B0_eq
#print axioms height_bound_gap3
#print axioms logA_lt_thirteen_fourths_logB3
#print axioms gap3_A_bounds
#print axioms abs_Lambda_eq_log_one_plus
#print axioms log_thirteen_lt_three
#print axioms log_log_thirteen_lt_one
#print axioms log_height_B0_lt_sixty_three
#print axioms matveev_product_bound_of_B3_le_height
#print axioms matveev_product_bound_of_B_le_B0
#print axioms matveev_gap3_lower_of
#print axioms gap3_target_eq_matveev_inequality
#print axioms C_exp_bound_real_eq_level26
#print axioms Lambda_gap3_real_nat

end BealMatveevBeal
