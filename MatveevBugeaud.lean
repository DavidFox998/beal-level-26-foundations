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
import MatveevThm14Proof
import MatveevLLL
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

/-!
# Displayed-lattice Baker–Davenport no-go (not a `B ≤ 10⁶` close)

Successor of `c78b413` (`v24-v24x-final-LLL-svt-det`). This file is
the honest Bugeaud / LLL *reduction proof* for the displayed
`C = 10³⁰` lattice: Baker–Davenport on `v = 4 b₁ − 13 b₂` **cannot**
inhabit `baker_bound_gap3`.

The floor-form error `|v₃ − C Λ| < 17` rearranges to the triangle
`|v₃| < 17 + C|Λ|`. Any witness `17 < r ≤ |v₃|` therefore satisfies
`(r − 17)/C < |Λ|`. That lower bound is strictly weaker than `|Λ|`
itself, so it cannot contradict `|Λ| < 1/B` or `|Λ| ≤ B⁴/A⁴`.
On a solution with `B > 10⁶` one also has `C|Λ| < 1`, hence
`|v₃| < 18` and `(r − 17)/C < 10⁻³⁰ < 10⁻⁶`.

The same lattice always contains the short vector `v`, so
`λ₁ < 32` and every LLL-reduced generating first vector has
`‖b₁‖ ≤ 2 λ₁ < 64`. Baker–Davenport would need
`r ≥ 17 + C/B` to beat `1/B`; at `B = B0` this is `≈ 10²⁴`.
Raising `C` or swapping columns does not help: `v` stays short
by construction. Wüstholz / `C1_floor = 143186215390` cannot
close the gap either (`exp(−C1 log A log B)` is far smaller than
`B⁴/A⁴`).

`bugeaud_LLL_reduction_proof`, `baker_davenport_reduction`,
`baker_bound_gap3_from_ratio`, and Level 26 `baker_bound_gap3`
stay uninhabited `def Prop`. The uniform-`C` method-failure
theorems `floor_form_approx_of_C`, `baker_davenport_reduction_nogo`,
and `bugeaud_LLL_method_fails` are the honest close of this LLL
setup: no scaling `C > 0` produces a Baker–Davenport witness
above `17 + C/B0` on solutions with `B ≥ B0`. Not a minted v25 tag.
-/

noncomputable section

open Real
open BealMatveevBeal.MatveevLLL
open BealLevel26Foundations.BealGap3BakerUpperBound

namespace BealMatveevBeal.MatveevBugeaud

/-! ## Locked numerals -/

theorem C1_floor_eq :
    BealMatveevBeal.MatveevThm14Proof.C1_floor = 143186215390 :=
  BealMatveevBeal.MatveevThm14Proof.C1_floor_numeral

theorem B0_nat_eq_numeral : B0_nat = 1000000 := B0_nat_eq

theorem LLL_C_div_B0_eq :
    LLL_C_real / (B0_nat : ℝ) = (10 : ℝ) ^ 24 := by
  rw [LLL_C_real_eq, B0_nat_eq]
  norm_num

/-! ## Triangle from the floor-form error -/

/-- `|v₃ − C Λ| < 17` implies `|v₃| < 17 + C|Λ|`, for every `A, B`. -/
theorem LLL_v_third_abs_lt_C_mul_abs_Lambda_add (A B : ℕ) :
    |LLL_v A B 2| < 17 + LLL_C_real * |Lambda A B| := by
  have happ := LLL_v_third_approx A B
  have hmul : |LLL_C_real * Lambda A B| = LLL_C_real * |Lambda A B| := by
    rw [abs_mul, abs_of_pos LLL_C_real_pos]
  have htri : |LLL_v A B 2| ≤
      |LLL_v A B 2 - LLL_C_real * Lambda A B| +
        |LLL_C_real * Lambda A B| := by
    simpa [sub_eq_add_neg] using
      abs_add (LLL_v A B 2 - LLL_C_real * Lambda A B)
        (LLL_C_real * Lambda A B)
  linarith [happ, htri, hmul]

/-- On a gap-3 solution, `|Λ| < 1/B` upgrades the triangle to
    `|v₃| < 17 + C/B`. Uniform in `B > 0`, not only `B > B0`. -/
theorem bugeaud_third_lt_seventeen_add_C_div_B
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    |LLL_v A B 2| < 17 + LLL_C_real / (B : ℝ) := by
  have ht := LLL_v_third_abs_lt_C_mul_abs_Lambda_add A B
  have hΛ := abs_Lambda_le_inv_B hsol hB
  have hC := LLL_C_real_pos
  have hmid :
      17 + LLL_C_real * |Lambda A B| <
        17 + LLL_C_real * (1 / (B : ℝ)) := by
    have := mul_lt_mul_of_pos_left hΛ hC
    linarith
  have hrew : 17 + LLL_C_real * (1 / (B : ℝ)) =
      17 + LLL_C_real / (B : ℝ) := by
    rw [mul_one_div]
  exact lt_trans ht (hmid.trans_eq hrew)

/-- Same triangle against the ratio upper bound. -/
theorem bugeaud_third_lt_seventeen_add_C_mul_ratio
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    |LLL_v A B 2| <
      17 + LLL_C_real * ((B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have ht := LLL_v_third_abs_lt_C_mul_abs_Lambda_add A B
  have hsand := abs_Lambda_tight_sandwich hsol hB
  have hC := LLL_C_real_pos
  have hmid :
      17 + LLL_C_real * |Lambda A B| ≤
        17 + LLL_C_real * ((B : ℝ) ^ 4 / (A : ℝ) ^ 4) :=
    add_le_add_left
      (mul_le_mul_of_nonneg_left hsand.2.1 (le_of_lt hC)) _
  exact lt_of_lt_of_le ht hmid

/-! ## Baker–Davenport is strictly weaker than `|Λ|` -/

/-- Usable Baker–Davenport on this `v` never meets `|Λ|`: if
    `17 < r ≤ |v₃|` then `(r − 17)/C < |Λ|`. The rearrangement
    cannot contradict any upper bound on `|Λ|`. -/
theorem bugeaud_bd_lower_lt_abs_Lambda
    (A B : ℕ) (r : ℝ)
    (hle : r ≤ |LLL_v A B 2|) (_h17 : 17 < r) :
    (r - 17) / LLL_C_real < |Lambda A B| := by
  have ht := LLL_v_third_abs_lt_C_mul_abs_Lambda_add A B
  have hr : r < 17 + LLL_C_real * |Lambda A B| := lt_of_le_of_lt hle ht
  have hC := LLL_C_real_pos
  have hsub : r - 17 < LLL_C_real * |Lambda A B| := by linarith [hr]
  have hcomm : LLL_C_real * |Lambda A B| = |Lambda A B| * LLL_C_real := by
    ring
  rw [hcomm] at hsub
  exact (div_lt_iff hC).mpr hsub

/-- Uniform no-go versus `|Λ| < 1/B`. Holds for every `B > 0`. -/
theorem bugeaud_bd_lower_lt_inv_B
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B)
    (r : ℝ) (hle : r ≤ |LLL_v A B 2|) (h17 : 17 < r) :
    (r - 17) / LLL_C_real < 1 / (B : ℝ) :=
  lt_trans (bugeaud_bd_lower_lt_abs_Lambda A B r hle h17)
    (abs_Lambda_le_inv_B hsol hB)

/-- Uniform no-go versus the ratio upper bound. -/
theorem bugeaud_bd_lower_lt_ratio
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B)
    (r : ℝ) (hle : r ≤ |LLL_v A B 2|) (h17 : 17 < r) :
    (r - 17) / LLL_C_real < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  lt_of_lt_of_le (bugeaud_bd_lower_lt_abs_Lambda A B r hle h17)
    (abs_Lambda_tight_sandwich hsol hB).2.1

/-! ## Required `r` versus the displayed short vector -/

/-- To have `(r − 17)/C ≥ 1/B` one needs `r ≥ 17 + C/B`. -/
theorem bugeaud_required_r
    {B : ℕ} (hB : 0 < B) {r : ℝ}
    (h : (1 : ℝ) / B ≤ (r - 17) / LLL_C_real) :
    17 + LLL_C_real / B ≤ r := by
  have hC := LLL_C_real_pos
  have hBpos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have hmul : (1 : ℝ) * LLL_C_real ≤ (r - 17) * B := by
    rwa [div_le_div_iff hBpos hC] at h
  have hdiv : LLL_C_real / B ≤ r - 17 := by
    rw [div_le_iff₀ hBpos]
    linarith [hmul]
  linarith [hdiv]

/-- If `B < C` then the required witness already exceeds `18`. -/
theorem bugeaud_required_r_gt_eighteen_of_B_lt_C
    {B : ℕ} (hB : 0 < B) (hBC : (B : ℝ) < LLL_C_real) :
    18 < 17 + LLL_C_real / B := by
  have hBpos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have : (1 : ℝ) < LLL_C_real / B := (one_lt_div hBpos).mpr hBC
  linarith

/-- If `B < C/47` then the required witness already exceeds `64`. -/
theorem bugeaud_required_r_gt_sixty_four_of_B_lt_C_div_forty_seven
    {B : ℕ} (hB : 0 < B) (hBlt : (B : ℝ) < LLL_C_real / 47) :
    64 < 17 + LLL_C_real / B := by
  have hBpos : (0 : ℝ) < (B : ℝ) := Nat.cast_pos.mpr hB
  have h47 : (0 : ℝ) < 47 := by norm_num
  have hgt : 47 < LLL_C_real / B := by
    have hmul : (B : ℝ) * 47 < LLL_C_real := (lt_div_iff h47).mp hBlt
    have hmul' : (47 : ℝ) * (B : ℝ) < LLL_C_real := by
      rwa [mul_comm] at hmul
    exact (lt_div_iff hBpos).mpr hmul'
  linarith [hgt]

/-- Naive GS length `< 64` still loses to `1/B0`:
    `(‖b₁‖ − 17)/C < 47/C < 10⁻⁶`. -/
theorem bugeaud_naive_gs_lt_inv_B0 {b1 : Fin 3 → ℝ}
    (hb : lllNorm b1 < 64) :
    (lllNorm b1 - 17) / LLL_C_real < 1 / (B0_nat : ℝ) := by
  have hC := LLL_C_real_pos
  have h47 : lllNorm b1 - 17 < 47 := by linarith [hb]
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hmid : (lllNorm b1 - 17) / LLL_C_real < 47 / LLL_C_real := by
    rw [div_lt_div_iff hC hC]
    exact mul_lt_mul_of_pos_right h47 hC
  have hquot : (47 : ℝ) / LLL_C_real < 1 / (B0_nat : ℝ) := by
    rw [div_lt_div_iff hC hB0pos, one_mul]
    rw [LLL_C_real_eq, B0_nat_eq]
    norm_num
  exact lt_trans hmid hquot

/-- On a solution with `B > 10⁶`, an LLL-reduced generating first
    vector is short: `‖b₁‖ ≤ 2 λ₁ < 64`. -/
theorem exists_reduced_b1_lt_sixty_four
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B) :
    ∃ b1 b2 b3 : Fin 3 → ℝ,
      mem_LLL_lattice A B b1 ∧
        lllGenerates A B b1 b2 b3 ∧
          lllIsReducedBasis b1 b2 b3 ∧
            lllNorm b1 < 64 := by
  obtain ⟨b1, b2, b3, hmem1, _hmem2, _hmem3, hgen, hred⟩ :=
    lll_algorithm_terminates A B
  refine ⟨b1, b2, b3, hmem1, hgen, hred, ?_⟩
  have hsvt := lll_svt_bound A B hmem1 hgen hred
  have hlam := LLL_lambda1_lt_thirty_two hsol hB hB0
  linarith [hsvt, hlam]

/-- For `B0 < B < C/47`, no reduced generating first vector can
    meet the Baker–Davenport length `17 + C/B` needed to beat `1/B`. -/
theorem not_exists_reduced_b1_gt_required_r
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B)
    (hBlt : (B : ℝ) < LLL_C_real / 47)
    (b1 b2 b3 : Fin 3 → ℝ)
    (hmem : mem_LLL_lattice A B b1)
    (hgen : lllGenerates A B b1 b2 b3)
    (hred : lllIsReducedBasis b1 b2 b3) :
    ¬ (17 + LLL_C_real / B < lllNorm b1) := by
  intro hgt
  have hsvt := lll_svt_bound A B hmem hgen hred
  have hlam := LLL_lambda1_lt_thirty_two hsol hB hB0
  have h64 : lllNorm b1 < 64 := by linarith [hsvt, hlam]
  have hreq :=
    bugeaud_required_r_gt_sixty_four_of_B_lt_C_div_forty_seven hB hBlt
  linarith [hgt, h64, hreq]

/-- On `B > 10⁶` the usable third coordinate is `< 18`, so the
    required `r ≥ 17 + C/B` is unavailable whenever `B < C`. -/
theorem bugeaud_usable_third_lt_required_r_of_B_lt_C
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat < B)
    (hBC : (B : ℝ) < LLL_C_real) :
    |LLL_v A B 2| < 17 + LLL_C_real / B := by
  have ht := LLL_v_third_abs_lt_eighteen hsol hB hB0
  have hreq := bugeaud_required_r_gt_eighteen_of_B_lt_C hB hBC
  linarith [ht, hreq]

/-! ## Uniform-`C` Baker–Davenport no-go (beyond the displayed `10³⁰`)

The floor error `|4⌊C log A⌋ − 13⌊C log(B+3)⌋ − C Λ| < 17` holds
for **every** `C > 0` (`floor_form_approx_of_C`). Any usable
Baker–Davenport witness `17 < r ≤ |third|` therefore satisfies
`(r − 17)/C < |Λ|`, independently of the scaling. In particular
no choice of `C` (including `C = B^k`) produces a witness
`r > 17 + C/B0` on a solution with `B ≥ B0`. This is the
method-failure theorem: it does **not** inhabit
`baker_davenport_reduction` / `bugeaud_LLL_reduction_proof`.
-/

/-- Triangle for an arbitrary scaling: `|third| < 17 + C|Λ|`. -/
theorem floor_form_third_abs_lt {C : ℝ} (hC : 0 < C) (A B : ℕ) :
    |floorFormThird C A B| < 17 + C * |Lambda A B| := by
  have happ := floor_form_approx_of_C C A B
  have hmul : |C * Lambda A B| = C * |Lambda A B| := by
    rw [abs_mul, abs_of_pos hC]
  have htri : |floorFormThird C A B| ≤
      |floorFormThird C A B - C * Lambda A B| + |C * Lambda A B| := by
    simpa [sub_eq_add_neg] using
      abs_add (floorFormThird C A B - C * Lambda A B)
        (C * Lambda A B)
  linarith [happ, htri, hmul]

/-- Uniform Baker–Davenport no-go: if `17 < r ≤ |third|` then
    `(r − 17)/C < |Λ|`. Independent of the scaling `C`. -/
theorem baker_davenport_reduction_nogo
    {C : ℝ} (hC : 0 < C) (A B : ℕ) (r : ℝ)
    (hle : r ≤ |floorFormThird C A B|) (_h17 : 17 < r) :
    (r - 17) / C < |Lambda A B| := by
  have ht := floor_form_third_abs_lt hC A B
  have hr : r < 17 + C * |Lambda A B| := lt_of_le_of_lt hle ht
  have hsub : r - 17 < C * |Lambda A B| := by linarith [hr]
  have hcomm : C * |Lambda A B| = |Lambda A B| * C := by
    ring
  rw [hcomm] at hsub
  exact (div_lt_iff hC).mpr hsub

/-- Same rearrangement versus `|Λ| < 1/B`. -/
theorem baker_davenport_reduction_nogo_inv_B
    {C : ℝ} (hC : 0 < C) {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B)
    (r : ℝ) (hle : r ≤ |floorFormThird C A B|) (h17 : 17 < r) :
    (r - 17) / C < 1 / (B : ℝ) :=
  lt_trans (baker_davenport_reduction_nogo hC A B r hle h17)
    (abs_Lambda_le_inv_B hsol hB)

/-- Same rearrangement versus the ratio upper bound. -/
theorem baker_davenport_reduction_nogo_ratio
    {C : ℝ} (hC : 0 < C) {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B)
    (r : ℝ) (hle : r ≤ |floorFormThird C A B|) (h17 : 17 < r) :
    (r - 17) / C < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  lt_of_lt_of_le (baker_davenport_reduction_nogo hC A B r hle h17)
    (abs_Lambda_tight_sandwich hsol hB).2.1

/-- On a solution with `B ≥ B0`, no real `r` can satisfy both
    `r > 17 + C/B0` and `r ≤ |third|`. -/
theorem baker_davenport_no_witness_above_C_div_B0
    {C : ℝ} (hC : 0 < C) {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) (r : ℝ) :
    ¬ (17 + C / (B0_nat : ℝ) < r ∧ r ≤ |floorFormThird C A B|) := by
  rintro ⟨hgt, hle⟩
  have htri := floor_form_third_abs_lt hC A B
  have hLam := abs_Lambda_le_inv_B hsol hB
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hBle : (B0_nat : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hB0
  have hCΛ : C * |Lambda A B| < C / (B0_nat : ℝ) := by
    have hmid : C * |Lambda A B| < C * (1 / (B : ℝ)) :=
      mul_lt_mul_of_pos_left hLam hC
    have hrew : C * (1 / (B : ℝ)) = C / (B : ℝ) := mul_one_div _ _
    have hCB : C / (B : ℝ) ≤ C / (B0_nat : ℝ) :=
      div_le_div_of_le_left (le_of_lt hC) hB0pos hBle
    linarith [hmid, hrew, hCB]
  have hthird : |floorFormThird C A B| < 17 + C / (B0_nat : ℝ) := by
    linarith [htri, hCΛ]
  linarith [hgt, hle, hthird]

/-- Method-failure theorem: no scaling `C > 0` of this floor form
    yields a Baker–Davenport witness above `17 + C/B0` on solutions
    with `B ≥ B0`. Not `baker_davenport_reduction` (that name stays
    the uninhabited v25 Prop). -/
theorem bugeaud_LLL_method_fails :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |floorFormThird C A B| := by
  intro C hC A B hsol hB hB0
  rintro ⟨r, hr⟩
  exact baker_davenport_no_witness_above_C_div_B0 hC hsol hB hB0 r hr

/-! ## Locked uninhabited Props (v25 remains open) -/

/-- Same implication as `MatveevLLL.bugeaud_LLL_reduction_proof`.
    Not a theorem: the displayed lattice cannot inhabit it. -/
def bugeaud_LLL_reduction_proof : Prop :=
  BealMatveevBeal.MatveevLLL.bugeaud_LLL_reduction_proof

def baker_davenport_reduction : Prop :=
  BealMatveevBeal.MatveevLLL.baker_davenport_reduction

def baker_bound_gap3_from_ratio : Prop :=
  BealMatveevBeal.MatveevLLL.baker_bound_gap3_from_ratio

#check C1_floor_eq
#check B0_nat_eq_numeral
#check LLL_C_div_B0_eq
#check LLL_v_third_abs_lt_C_mul_abs_Lambda_add
#check bugeaud_third_lt_seventeen_add_C_div_B
#check bugeaud_third_lt_seventeen_add_C_mul_ratio
#check bugeaud_bd_lower_lt_abs_Lambda
#check bugeaud_bd_lower_lt_inv_B
#check bugeaud_bd_lower_lt_ratio
#check bugeaud_required_r
#check bugeaud_required_r_gt_eighteen_of_B_lt_C
#check bugeaud_required_r_gt_sixty_four_of_B_lt_C_div_forty_seven
#check bugeaud_naive_gs_lt_inv_B0
#check exists_reduced_b1_lt_sixty_four
#check not_exists_reduced_b1_gt_required_r
#check bugeaud_usable_third_lt_required_r_of_B_lt_C
#check floor_form_third_abs_lt
#check baker_davenport_reduction_nogo
#check baker_davenport_reduction_nogo_inv_B
#check baker_davenport_reduction_nogo_ratio
#check baker_davenport_no_witness_above_C_div_B0
#check bugeaud_LLL_method_fails
#check bugeaud_LLL_reduction_proof
#check baker_davenport_reduction
#check baker_bound_gap3_from_ratio
#check baker_bound_gap3
#print axioms LLL_v_third_abs_lt_C_mul_abs_Lambda_add
#print axioms bugeaud_bd_lower_lt_inv_B
#print axioms bugeaud_bd_lower_lt_ratio
#print axioms exists_reduced_b1_lt_sixty_four
#print axioms not_exists_reduced_b1_gt_required_r
#print axioms LLL_C_div_B0_eq
#print axioms baker_davenport_reduction_nogo
#print axioms bugeaud_LLL_method_fails

end BealMatveevBeal.MatveevBugeaud
