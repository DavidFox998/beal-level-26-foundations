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
import WuestholzProduct
import MatveevLLL
import MatveevThm14Proof
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

/-!
# Linear-forms-in-logs no-go (not a `B ≤ 10⁶` close)

Successor of `2a17664` (`v24-v24x-final-LLL-nogo-product`).
Padding `Λ` with a dummy `0 · log 2` does not produce a new
lower bound: `Lambda3 = Lambda`. A Matveev-style exponential
`exp(−C1 log A log(B+3))` beats `B⁴/A⁴` at `B ≥ B0` only if
`C1 < 1` (in fact `C1 < 4 / log B0 < 1`). Every constant we
actually have — `C1_floor = 143186215390`, the jet dimension
`242`, even the ideal `C1 = 1` — is too large, so the lower
bound is strictly smaller than the ratio and cannot cut off
`B ≤ 10⁶`.

A four-factor jet `(L+1)(N1+1)(N2+1)(N3+1)` is cubic in the
`G_m` degrees; there is still no uniform `c` of shape `c L K`.
Philippon for `𝐆_a × 𝐆_m³` is not in Mathlib 4.12.

`baker_bound_gap3`, `wuestholz_product_theorem_exp`, and
`baker_davenport_reduction` stay uninhabited `def Prop`. Not v25.
`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

open Real
open BealMatveevBeal.MatveevLLL
open BealMatveevBeal.MatveevThm14Proof
open BealMatveevBeal.WuestholzProduct
open BealLevel26Foundations.BealGap3BakerUpperBound

namespace BealMatveevBeal.MatveevThreeLogs

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_proof :
    C1_floor = BealMatveevBeal.MatveevThm14Proof.C1_floor := rfl

theorem B0_nat_eq_lll :
    B0_nat = BealMatveevBeal.MatveevLLL.B0_nat := rfl

/-! ## Dummy third logarithm does not change `Λ` -/

/-- Same linear form with a dummy `0 · log 2`. Not a three-log
    lower bound: the extra term is zero. -/
noncomputable def Lambda3 (A B : ℕ) : ℝ :=
  (4 : ℝ) * log (A : ℝ) - 13 * log ((B + 3 : ℕ) : ℝ) + 0 * log 2

theorem Lambda3_eq_Lambda (A B : ℕ) :
    Lambda3 A B = Lambda A B := by
  simp [Lambda3, Lambda]

theorem Lambda3_eq_log_ratio (A B : ℕ) :
    Lambda3 A B = 4 * log (A : ℝ) - 13 * log ((B + 3 : ℕ) : ℝ) := by
  simp [Lambda3]

/-! ## `log B0 > 13`, so any `C1 ≥ 1` is already too large -/

theorem log_two_gt_thirteen_div_nineteen :
    (13 / 19 : ℝ) < log 2 :=
  lt_trans (by norm_num) Real.log_two_gt_d9

theorem exp_thirteen_lt_two_pow_nineteen :
    exp 13 < (2 : ℝ) ^ 19 := by
  have h19 : (0 : ℝ) < 19 := by norm_num
  have hdiv := log_two_gt_thirteen_div_nineteen
  have hmul : (13 : ℝ) < log 2 * 19 := (div_lt_iff h19).mp hdiv
  have hmul' : (13 : ℝ) < (19 : ℕ) * log 2 := by
    rwa [mul_comm] at hmul
  have hexp : exp 13 < exp ((19 : ℕ) * log 2) :=
    Real.exp_lt_exp.mpr hmul'
  have hrw : exp ((19 : ℕ) * log 2) = (2 : ℝ) ^ 19 := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  rwa [hrw] at hexp

theorem two_pow_nineteen_lt_B0 :
    (2 : ℝ) ^ 19 < (B0_nat : ℝ) := by
  rw [B0_nat_eq]
  norm_num

theorem log_B0_gt_thirteen :
    (13 : ℝ) < log (B0_nat : ℝ) := by
  have hpos : (0 : ℝ) < (B0_nat : ℝ) := by
    rw [B0_nat_eq]
    norm_num
  have hlt : exp 13 < (B0_nat : ℝ) :=
    lt_trans exp_thirteen_lt_two_pow_nineteen two_pow_nineteen_lt_B0
  exact (Real.lt_log_iff_exp_lt hpos).2 hlt

theorem four_div_log_B0_lt_one :
    (4 : ℝ) / log (B0_nat : ℝ) < 1 := by
  have hlog := log_B0_gt_thirteen
  have hpos : (0 : ℝ) < log (B0_nat : ℝ) := lt_trans (by norm_num) hlog
  have : (4 : ℝ) < log (B0_nat : ℝ) := lt_trans (by norm_num) hlog
  exact (div_lt_one hpos).2 this

theorem C1_floor_gt_one : (1 : ℝ) < (C1_floor : ℝ) := by
  rw [C1_floor_eq]
  norm_num

theorem two_forty_two_gt_one : (1 : ℝ) < (242 : ℝ) := by
  norm_num

/-! ## On a solution with `B ≥ B0`, `log A > 13` -/

theorem A_gt_B_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    B < A := by
  have hpow : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := hsol
  exact eq_implies_A_gt_B hpow hB

theorem logA_gt_thirteen_of_B_ge_B0 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (13 : ℝ) < log (A : ℝ) := by
  have hAgt := A_gt_B_of_sol hsol hB
  have hA : (B0_nat : ℝ) < (A : ℝ) := by
    have : B0_nat < A := Nat.lt_of_le_of_lt hB0 hAgt
    exact_mod_cast this
  have hB0pos : (1 : ℝ) < (B0_nat : ℝ) := by
    rw [B0_nat_eq]
    norm_num
  have hlog := Real.log_lt_log (lt_trans (by norm_num) hB0pos) hA
  exact lt_trans log_B0_gt_thirteen hlog

theorem A_pow_lt_B3_pow {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    (A : ℝ) ^ 4 < ((B + 3 : ℕ) : ℝ) ^ 13 := by
  have hB4 : 0 < B ^ 4 :=
    Nat.lt_of_lt_of_le hB (Nat.le_self_pow (by decide : 4 ≠ 0) B)
  have hlt : A ^ 4 < (B + 3) ^ 13 :=
    calc
      A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
      _ = (B + 3) ^ 13 := hsol
  exact_mod_cast hlt

/-! ## Exponential lower bound is strictly below the ratio -/

/-- `exp(−C1 log A log(B+3)) = (B+3)^{−C1 log A}`. For `C1 ≥ 1`
    and `B ≥ B0` one has `C1 log A > 13`, so this is
    `< 1/(B+3)¹³ < B⁴/(B+3)¹³ < B⁴/A⁴`. -/
theorem baker_bound_gap3_nogo_logs
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + 3 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  set a : ℝ := log (A : ℝ)
  set c : ℝ := log ((B + 3 : ℕ) : ℝ)
  set C : ℝ := ((B + 3 : ℕ) : ℝ)
  have hAgt1 : 1 < A := (gap3_A_gt_one A B hsol hB).1
  have hCgt1 : 1 < B + 3 := (gap3_A_gt_one A B hsol hB).2
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (0 : ℕ) < A := lt_trans Nat.zero_lt_one hAgt1
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C := by
    have : 0 < ((B + 3 : ℕ) : ℝ) := by
      have h : 0 < B + 3 := lt_trans Nat.zero_lt_one hCgt1
      exact_mod_cast h
    simpa [C] using this
  have hCgt : (1 : ℝ) < C := by
    have : (1 : ℝ) < ((B + 3 : ℕ) : ℝ) := by exact_mod_cast hCgt1
    simpa [C] using this
  have ha : (13 : ℝ) < a := logA_gt_thirteen_of_B_ge_B0 hsol hB hB0
  have hapos : (0 : ℝ) < a := lt_trans (by norm_num) ha
  have hcpos : (0 : ℝ) < c := Real.log_pos hCgt
  have hC1a : (13 : ℝ) < C1 * a := by
    have hle : a ≤ C1 * a := le_mul_of_one_le_left (le_of_lt hapos) hC1
    linarith [ha, hle]
  have hmul : -C1 * a * c < -13 * c := by
    have : (13 : ℝ) * c < C1 * a * c :=
      mul_lt_mul_of_pos_right hC1a hcpos
    linarith
  have hexp : exp (-C1 * a * c) < exp (-13 * c) :=
    Real.exp_lt_exp.mpr hmul
  have h13 : exp (-(13 : ℝ) * c) = 1 / C ^ 13 := by
    have hpow : exp ((13 : ℕ) * c) = C ^ 13 := by
      rw [Real.exp_nat_mul, Real.exp_log hCpos]
    have hneg : -(13 : ℝ) * c = -((13 : ℕ) * c) := by
      push_cast
      ring
    rw [hneg, Real.exp_neg, hpow, inv_eq_one_div]
  have hinv : (1 : ℝ) / C ^ 13 < (B : ℝ) ^ 4 / C ^ 13 := by
    have hC13 : (0 : ℝ) < C ^ 13 := pow_pos hCpos 13
    have hB4 : (1 : ℝ) < (B : ℝ) ^ 4 := by
      have hB2 : (2 : ℕ) ≤ B :=
        le_trans (by decide : 2 ≤ 1000000)
          (by simpa [B0_nat_eq] using hB0)
      have h16 : (2 : ℕ) ^ 4 ≤ B ^ 4 :=
        Nat.pow_le_pow_left hB2 4
      have h16R : (16 : ℝ) ≤ (B : ℝ) ^ 4 := by
        have h16n : (16 : ℕ) ≤ B ^ 4 := by
          simpa using h16
        exact_mod_cast h16n
      linarith
    exact (div_lt_div_right hC13).mpr hB4
  have hratio : (B : ℝ) ^ 4 / C ^ 13 < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
    have hA4pos : (0 : ℝ) < (A : ℝ) ^ 4 := pow_pos hApos 4
    have hB4pos : (0 : ℝ) < (B : ℝ) ^ 4 := by
      have : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
      exact pow_pos this 4
    have hlt := A_pow_lt_B3_pow hsol hB
    exact div_lt_div_of_pos_left hB4pos hA4pos hlt
  have hchain : exp (-C1 * a * c) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    lt_trans (hexp.trans_eq h13) (lt_trans hinv hratio)
  simpa [a, c] using hchain

/-- Same comparison for the displayed Bugeaud floor. -/
theorem C1_floor_exp_lt_ratio
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + 3 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  baker_bound_gap3_nogo_logs (le_of_lt C1_floor_gt_one) hsol hB hB0

/-- Same comparison for the displayed jet dimension `242`. -/
theorem two_forty_two_exp_lt_ratio
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(242 : ℝ) * log (A : ℝ) * log ((B + 3 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  baker_bound_gap3_nogo_logs (le_of_lt two_forty_two_gt_one) hsol hB hB0

/-- Ideal product-theorem constant `C1 = 1` still loses. -/
theorem one_exp_lt_ratio
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(1 : ℝ) * log (A : ℝ) * log ((B + 3 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  baker_bound_gap3_nogo_logs (le_refl (1 : ℝ)) hsol hB hB0

/-- Re-export name requested in the successor sketch. -/
theorem matveev_lower_nogo_logs
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + 3 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  baker_bound_gap3_nogo_logs hC1 hsol hB hB0

/-- Ratio upper bound is `< 1/B0` whenever `B ≥ B0`. Not a cutoff
    by itself: the same bound is `< 1/B` for every `B > 0`. -/
theorem Lambda_upper_lt_inv_B0
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    |Lambda A B| < 1 / (B0_nat : ℝ) := by
  have hΛ := abs_Lambda_le_inv_B hsol hB
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    rw [B0_nat_eq]
    norm_num
  have hBle : (B0_nat : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB0
  have hinv : (1 : ℝ) / (B : ℝ) ≤ 1 / (B0_nat : ℝ) :=
    one_div_le_one_div_of_le hB0pos hBle
  exact lt_of_lt_of_le hΛ hinv

/-! ## Four-factor jet (`𝐆_a × 𝐆_m³`) is cubic; still no uniform `c` -/

def coeffCount3 (L N1 N2 N3 : ℕ) : ℕ :=
  (L + 1) * (N1 + 1) * (N2 + 1) * (N3 + 1)

theorem coeffCount3_one_ten_ten_ten :
    coeffCount3 1 10 10 10 = 2662 := by
  simp [coeffCount3]

theorem coeffCount3_zero_ten_ten_ten :
    coeffCount3 0 10 10 10 = 1331 := by
  simp [coeffCount3]

/-- Displayed `L = 0`, `N1 = N2 = N3 = 10`: jet dimension `11³ = 1331`.
    Not a product theorem: this is only the count. -/
theorem coeffCount3_zero_ten_ten_ten_pow :
    coeffCount3 0 10 10 10 = 11 ^ 3 := by
  simp [coeffCount3]

/-- No uniform `c` makes `c L K` dominate a four-factor jet:
    the count is cubic in the `G_m` degrees. -/
theorem no_uniform_c_cubic_in_N :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) := by
  rintro ⟨c, _hc, hforall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (3 * c)
  have h := hforall 0 n n n
  have hcnt : (coeffCount3 0 n n n : ℝ) =
      (n + 1 : ℝ) * (n + 1) * (n + 1) := by
    simp [coeffCount3]
  have hle : (n + 1 : ℝ) * (n + 1) * (n + 1) ≤
      c * (0 + 1 : ℝ) *
        ((n + 1 : ℝ) + (n + 1 : ℝ) + (n + 1 : ℝ)) := by
    simpa [hcnt] using h
  have hrhs : c * (0 + 1 : ℝ) *
        ((n + 1 : ℝ) + (n + 1 : ℝ) + (n + 1 : ℝ)) =
      (3 * c) * (n + 1 : ℝ) := by
    ring
  have hn1 : (3 * c) < (n + 1 : ℝ) := by
    have : (n : ℝ) < n + 1 := lt_add_one _
    linarith [hn]
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hx : (1 : ℝ) ≤ n + 1 := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hx2 : (n + 1 : ℝ) ≤ (n + 1 : ℝ) * (n + 1) :=
    le_mul_of_one_le_left (le_of_lt hpos) hx
  have hsq : (3 * c) < (n + 1 : ℝ) * (n + 1) :=
    lt_of_lt_of_le hn1 hx2
  have hlt : (3 * c) * (n + 1 : ℝ) <
      (n + 1 : ℝ) * (n + 1) * (n + 1) :=
    (mul_lt_mul_right hpos).mpr hsq
  exact not_le_of_gt (hrhs ▸ hlt) hle

/-! ## Locked uninhabited Props -/

def wuestholz_product_theorem_exp : Prop :=
  BealMatveevBeal.WuestholzProduct.wuestholz_product_theorem_exp

def wuestholz_subgroup_theorem : Prop :=
  BealMatveevBeal.WuestholzProduct.wuestholz_subgroup_theorem

def baker_davenport_reduction : Prop :=
  BealMatveevBeal.WuestholzProduct.baker_davenport_reduction

def bugeaud_LLL_reduction_proof : Prop :=
  BealMatveevBeal.WuestholzProduct.bugeaud_LLL_reduction_proof

def baker_bound_gap3 : Prop :=
  BealLevel26Foundations.BealGap3BakerUpperBound.baker_bound_gap3

/-- Uniform product theorem on `𝐆_a × 𝐆_m³`. Not in Mathlib 4.12. -/
def wuestholz_product_theorem_exp_Gm3 : Prop :=
  ∃ c : ℝ, 0 < c ∧
    ∀ L N1 N2 N3 K : ℕ,
      (coeffCount3 L N1 N2 N3 : ℝ) ≤ c * (L : ℝ) * (K : ℝ)

#check C1_floor_eq
#check B0_nat_eq
#check Lambda3_eq_Lambda
#check log_B0_gt_thirteen
#check four_div_log_B0_lt_one
#check baker_bound_gap3_nogo_logs
#check C1_floor_exp_lt_ratio
#check two_forty_two_exp_lt_ratio
#check one_exp_lt_ratio
#check matveev_lower_nogo_logs
#check Lambda_upper_lt_inv_B0
#check coeffCount3_one_ten_ten_ten
#check coeffCount3_zero_ten_ten_ten
#check no_uniform_c_cubic_in_N
#check wuestholz_product_theorem_exp
#check baker_bound_gap3
#check wuestholz_product_theorem_exp_Gm3
#print axioms log_B0_gt_thirteen
#print axioms baker_bound_gap3_nogo_logs
#print axioms C1_floor_exp_lt_ratio
#print axioms two_forty_two_exp_lt_ratio
#print axioms one_exp_lt_ratio
#print axioms Lambda_upper_lt_inv_B0
#print axioms no_uniform_c_cubic_in_N
#print axioms Lambda3_eq_Lambda

end BealMatveevBeal.MatveevThreeLogs
