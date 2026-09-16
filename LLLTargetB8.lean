/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Separate Lake target `BealMatveevBealV25B0Search`
  (same lib as `BealMatveevBealV25B0Search.lean`). Do **not** add
  `Beal/Matveev/LLLTargetB8.lean`: `.submodules Beal.Matveev`
  would pull it into the default glob. Do **not** import
  `Beal.Matveev.MatveevThm14General`. Do **not** import
  `Beal.Matveev.PAdicLLL` from this root module (LEAN_PATH); the
  floor lattice `b1=(1,0)` is defined here and already nogo'd
  for Euclidean `≥ B0` in root `PAdicLLL.lean`.
-/
import BealMatveevBealV25B0Search

/-!
# LLL target `|Λ| ≥ B⁻⁸` (not a v25 mint)

On a gap-3 solution with `B ≥ 100` one already has
`|Λ| ≤ 2/B⁹` (`abs_Lambda_lt_two_div_B_pow_nine` at `f12ad03`).
If LLL lifted Matveev’s `B^{−C1}` lower bound with
`C1 = 143186215390` down to `|Λ| ≥ B⁻⁸`, then
`1/B⁸ ≤ 2/B⁹`, hence `B ≤ 2`, contradicting `B ≥ B0 = 10⁶`.
That would close the infinite branch `B ≥ B0`. The finite
branch `B ≤ B0` still needs Darmon–Merel `(4,4,13)` (the extra
axiom in `BealTrueV25`, not the default glob). This file does
**not** inhabit the LLL lift, does **not** inhabit
`LLL_reduces_bound_to_B0_v25`, and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

Phase-lift lattice (same `C = 10³⁰` as `MatveevLLL.LLL_C_nat`):
`b1 = (1,0)`, `b2 = (⌊C log(B+3)⌋, 1)`. Arithmetic
`C·B⁻⁸ ≤ 10⁻¹⁸ < 1/2` and `C·(2/B⁹) < 1` are theorems.
`λ₁ ≥ 1` is a theorem on this integer lattice. The missing
piece is a **nonzero** `v ∈ L` with Euclidean length
`C·|Λ| < 1`. No such integer vector exists:
`euc v < 1 ↔ v = 0`. That is the same obstruction as
`PAdicLLL.floor_lattice_nogo` / `lll_euclidean_lower_bound_fails`
(length-1 `b1`), not a false `|Λ| ≥ B0/C` lower bound.
The implication `LLL_lift_to_B8_of_short_vector` is therefore
honest and uninhabited in the `h_exists` hypothesis.

0 sorry. Tag `v24-v24x-final-rank3-shape-nogo` stays at `c1d173e`.
-/

namespace BealMatveevBeal.LLLTargetB8

open BealMatveevBeal.BealMatveevBealV25B0Search

/-- Honest LLL goal: `|Λ| ≥ B⁻⁸` on a solution with `B ≥ 100`.
    Same statement as `abs_Lambda_ge_inv_B_pow_eight`. Uninhabited. -/
noncomputable def abs_Lambda_ge_B_pow_neg_eight : Prop :=
  abs_Lambda_ge_inv_B_pow_eight

theorem abs_Lambda_ge_B_pow_neg_eight_eq :
    abs_Lambda_ge_B_pow_neg_eight = abs_Lambda_ge_inv_B_pow_eight :=
  rfl

/-- Reduce Matveev `C1 = 143186215390` to an exponent `< 9`.
    Uninhabited: Bugeaud–Laurent typically reaches `10²`–`10³`,
    not `< 9`. Equivalent to `|Λ| ≥ B⁻⁸`. -/
noncomputable def LLL_reduces_C1_to_lt_nine : Prop :=
  abs_Lambda_ge_B_pow_neg_eight

/-- Packaged v25 LLL close. Uninhabited: the first two conjuncts
    are the missing lower bound; the third is the large-`B`
    nogo they would imply. Rank-3
    `BealMatveevBealV25Rank3.LLL_reduces_bound_to_B0_v25` is a
    different `def Prop` in another target. -/
noncomputable def LLL_reduces_bound_to_B0_v25 : Prop :=
  abs_Lambda_ge_B_pow_neg_eight ∧
    LLL_reduces_C1_to_lt_nine ∧
      ∀ {A B : ℕ}, B0_nat ≤ B → A ^ 4 + B ^ 4 = (B + 3) ^ 13 → False

theorem one_div_pow_eight_le_two_div_pow_nine_implies_B_le_two
    {B : ℕ} (hB : 1 ≤ B)
    (hle : (1 : ℝ) / (B : ℝ) ^ 8 ≤ 2 / (B : ℝ) ^ 9) : B ≤ 2 := by
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mp hB)
  have h8 : (0 : ℝ) < (B : ℝ) ^ 8 := pow_pos hBpos 8
  have h9 : (0 : ℝ) < (B : ℝ) ^ 9 := pow_pos hBpos 9
  have hmul : (1 : ℝ) * (B : ℝ) ^ 9 ≤ 2 * (B : ℝ) ^ 8 :=
    (div_le_div_iff h8 h9).mp hle
  simp only [one_mul] at hmul
  have hcancel : (B : ℝ) ^ 8 * (B : ℝ) ≤ (B : ℝ) ^ 8 * 2 := by
    convert hmul using 1; ring
  have hB2 : (B : ℝ) ≤ 2 := le_of_mul_le_mul_left hcancel h8
  exact_mod_cast hB2

/-- If LLL inhabits `|Λ| ≥ B⁻⁸`, the proved `|Λ| ≤ 2/B⁹` forces
    `B ≤ 2`, contradicting `B ≥ B0 = 10⁶`. Does **not** inhabit
    the LLL hypothesis. -/
theorem no_sol_of_abs_Lambda_ge_B_pow_neg_eight
    (hge : abs_Lambda_ge_B_pow_neg_eight)
    {A B : ℕ} (hB0 : B0_nat ≤ B)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) : False := by
  have h100B0 : 100 ≤ B0_nat := by
    rw [B0_nat_eq]
    decide
  have h100 : 100 ≤ B := h100B0.trans hB0
  have hup := abs_Lambda_lt_two_div_B_pow_nine h100 hsol
  have hlow := hge h100 hsol
  have hle : (1 : ℝ) / (B : ℝ) ^ 8 ≤ 2 / (B : ℝ) ^ 9 :=
    hlow.trans hup
  have h1 : 1 ≤ B := le_trans (by decide : (1 : ℕ) ≤ 100) h100
  have hB2 : B ≤ 2 :=
    one_div_pow_eight_le_two_div_pow_nine_implies_B_le_two h1 hle
  have hB0le2 : B0_nat ≤ 2 := hB0.trans hB2
  rw [B0_nat_eq] at hB0le2
  exact (by decide : ¬((1000000 : ℕ) ≤ 2)) hB0le2

/-- Same implication, packaged as the large-`B` nogo. -/
theorem LLL_closes_B_ge_B0_of_pow_neg_eight
    (hge : abs_Lambda_ge_B_pow_neg_eight) :
    ∀ {A B : ℕ}, B0_nat ≤ B → A ^ 4 + B ^ 4 = (B + 3) ^ 13 → False :=
  no_sol_of_abs_Lambda_ge_B_pow_neg_eight hge

/-- Correct `by_cases` shape. Does **not** inhabit either
    branch: `B ≤ B0` is still `gap3_B_le_B0_no_solution`
    (`def Prop`, or Darmon–Merel in `BealTrueV25`), and
    `B ≥ B0` still needs `abs_Lambda_ge_B_pow_neg_eight`. -/
theorem future_v25_shape_of_B8_lift :
    gap3_B_le_B0_no_solution →
      abs_Lambda_ge_B_pow_neg_eight →
        ∀ B A : ℕ, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro hLe hge B A hsol
  by_cases h : B ≤ B0_nat
  · exact hLe B h A hsol
  · exact no_sol_of_abs_Lambda_ge_B_pow_neg_eight hge (le_of_not_le h) hsol

/-! ## Phase-lift lattice `C = 10³⁰`, `b1 = (1,0)`

    Same Euclidean `(1,0)` that `PAdicLLL` already showed has
    length `1 < B0`. Here the target is `|Λ| ≥ B⁻⁸`, not
    Euclidean `≥ B0`. `C · B⁻⁸ = 10⁻¹⁸ < 1 = λ₁` is true
    arithmetic. It does **not** produce a nonzero lattice
    vector of length `C·|Λ|`: integer pairs satisfy
    `euc v < 1 ↔ v = 0`. -/

/-- Lattice scale. Same numeral as `MatveevLLL.LLL_C_nat`.
    Not `C1_floor` and not `PAdicLLL.C_LLL = C1_floor²`. -/
def C_LLL : ℕ := 10 ^ 30

theorem C_LLL_eq : C_LLL = 10 ^ 30 := rfl

def b1 : ℤ × ℤ := (1, 0)

noncomputable def cLog (B : ℕ) : ℤ :=
  ⌊(C_LLL : ℝ) * Real.log ((B : ℝ) + 3)⌋

noncomputable def b2 (B : ℕ) : ℤ × ℤ := (cLog B, 1)

theorem b1_eq : b1 = (1, 0) := rfl

theorem b2_snd (B : ℕ) : (b2 B).2 = 1 := rfl

/-- `ℤ b1 + ℤ b2`. A general vector is `(k + l · cLog B, l)`. -/
noncomputable def L (B : ℕ) : Set (ℤ × ℤ) :=
  { v | ∃ k l : ℤ, v = (k + l * cLog B, l) }

noncomputable def euc (v : ℤ × ℤ) : ℝ :=
  Real.sqrt ((v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2)

theorem euc_nonneg (v : ℤ × ℤ) : 0 ≤ euc v :=
  Real.sqrt_nonneg _

theorem euc_sq (v : ℤ × ℤ) :
    euc v ^ 2 = (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by
  unfold euc
  exact Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))

theorem euc_b1 : euc b1 = 1 := by
  unfold euc b1
  simp [Real.sqrt_one]

theorem b1_mem_L (B : ℕ) : b1 ∈ L B := by
  refine ⟨1, 0, ?_⟩
  simp [b1]

theorem L_eq_combo (B : ℕ) (v : ℤ × ℤ) :
    v ∈ L B ↔ ∃ k l : ℤ, v = (k + l * cLog B, l) :=
  Iff.rfl

theorem million_eq_ten_pow_six : (1000000 : ℝ) = 10 ^ 6 := by
  norm_num

theorem million_pow_eight : (1000000 : ℝ) ^ 8 = (10 : ℝ) ^ 48 := by
  rw [million_eq_ten_pow_six, ← pow_mul]

theorem million_pow_nine : (1000000 : ℝ) ^ 9 = (10 : ℝ) ^ 54 := by
  rw [million_eq_ten_pow_six, ← pow_mul]

theorem C_LLL_real : (C_LLL : ℝ) = (10 : ℝ) ^ 30 := by
  rw [C_LLL_eq]
  exact Nat.cast_pow (10 : ℕ) 30

theorem ten_pow_thirty_div_forty_eight :
    (10 : ℝ) ^ 30 / (10 : ℝ) ^ 48 = 1 / (10 : ℝ) ^ 18 := by
  have h10 : (10 : ℝ) ≠ 0 := by norm_num
  field_simp [h10]
  rw [← pow_add]

theorem one_div_ten_pow_eighteen_lt_half :
    1 / (10 : ℝ) ^ 18 < 1 / 2 := by
  norm_num

/-- `C · B⁻⁸ ≤ 10⁻¹⁸ < 1/2` on `B ≥ B0`. This is the arithmetic
    `C · B⁻⁸ < λ₁` for `λ₁ ≥ 1`. -/
theorem C_LLL_mul_inv_B_pow_eight_lt_half {B : ℕ} (hB : B0_nat ≤ B) :
    (C_LLL : ℝ) / (B : ℝ) ^ 8 < 1 / 2 := by
  have hB0 : (1000000 : ℕ) ≤ B := by
    simpa [B0_nat_eq] using hB
  have hBreal : (1000000 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB0
  have hpow : (1000000 : ℝ) ^ 8 ≤ (B : ℝ) ^ 8 :=
    pow_le_pow_left (by norm_num) hBreal 8
  have hnum : 0 ≤ (C_LLL : ℝ) := Nat.cast_nonneg _
  have hle : (C_LLL : ℝ) / (B : ℝ) ^ 8 ≤ (C_LLL : ℝ) / (1000000 : ℝ) ^ 8 :=
    div_le_div_of_nonneg_left hnum (pow_pos (by norm_num) 8) hpow
  have hC : (C_LLL : ℝ) / (1000000 : ℝ) ^ 8 =
      (10 : ℝ) ^ 30 / (10 : ℝ) ^ 48 := by
    rw [C_LLL_real, million_pow_eight]
  have hlt : (10 : ℝ) ^ 30 / (10 : ℝ) ^ 48 < 1 / 2 := by
    rw [ten_pow_thirty_div_forty_eight]
    exact one_div_ten_pow_eighteen_lt_half
  exact lt_of_le_of_lt (hle.trans_eq hC) hlt

/-- `λ₁(L) > C · (2/B⁹)` as arithmetic: `C · 2/B⁹ ≤ 2·10⁻²⁴ < 1`. -/
theorem C_LLL_mul_two_div_B_pow_nine_lt_one {B : ℕ} (hB : B0_nat ≤ B) :
    (C_LLL : ℝ) * (2 / (B : ℝ) ^ 9) < 1 := by
  have hB0 : (1000000 : ℕ) ≤ B := by
    simpa [B0_nat_eq] using hB
  have hBreal : (1000000 : ℝ) ≤ (B : ℝ) := by exact_mod_cast hB0
  have hpow : (1000000 : ℝ) ^ 9 ≤ (B : ℝ) ^ 9 :=
    pow_le_pow_left (by norm_num) hBreal 9
  have hfrac : 2 / (B : ℝ) ^ 9 ≤ 2 / (1000000 : ℝ) ^ 9 :=
    div_le_div_of_nonneg_left (by norm_num) (pow_pos (by norm_num) 9) hpow
  have hle : (C_LLL : ℝ) * (2 / (B : ℝ) ^ 9) ≤
      (C_LLL : ℝ) * (2 / (1000000 : ℝ) ^ 9) :=
    mul_le_mul_of_nonneg_left hfrac (Nat.cast_nonneg _)
  have hval : (C_LLL : ℝ) * (2 / (1000000 : ℝ) ^ 9) =
      2 * (10 : ℝ) ^ 30 / (10 : ℝ) ^ 54 := by
    rw [C_LLL_real, million_pow_nine]
    ring
  have hlt : 2 * (10 : ℝ) ^ 30 / (10 : ℝ) ^ 54 < 1 := by
    rw [div_lt_one (pow_pos (by norm_num) 54)]
    norm_num
  exact lt_of_le_of_lt (hle.trans_eq hval) hlt

theorem int_sq_ge_one_of_ne_zero {z : ℤ} (hz : z ≠ 0) : (1 : ℤ) ≤ z ^ 2 :=
  Int.add_one_le_of_lt (sq_pos_of_ne_zero hz)

/-- Nonzero integer pairs have Euclidean length `≥ 1`. -/
theorem euc_ge_one_of_ne_zero (v : ℤ × ℤ) (hne : v ≠ 0) : 1 ≤ euc v := by
  have hsum : (1 : ℝ) ≤ (v.1 : ℝ) ^ 2 + (v.2 : ℝ) ^ 2 := by
    rcases em (v.1 = 0) with h1 | h1
    · rcases em (v.2 = 0) with h2 | h2
      · exact (hne (Prod.ext h1 h2)).elim
      · have : (1 : ℤ) ≤ v.2 ^ 2 := int_sq_ge_one_of_ne_zero h2
        have : (1 : ℝ) ≤ (v.2 : ℝ) ^ 2 := by
          exact_mod_cast this
        have hx : (0 : ℝ) ≤ (v.1 : ℝ) ^ 2 := sq_nonneg _
        linarith
    · have : (1 : ℤ) ≤ v.1 ^ 2 := int_sq_ge_one_of_ne_zero h1
      have : (1 : ℝ) ≤ (v.1 : ℝ) ^ 2 := by
        exact_mod_cast this
      have hy : (0 : ℝ) ≤ (v.2 : ℝ) ^ 2 := sq_nonneg _
      linarith
  have hsqrt := Real.sqrt_le_sqrt hsum
  simpa [euc, Real.sqrt_one] using hsqrt

/-- `λ₁ ≥ 1` from `b1 = (1,0)` and the integer lattice. -/
theorem lambda1_ge_one {B : ℕ} : ∀ v ∈ L B, v ≠ 0 → 1 ≤ euc v := by
  intro v _ hv
  exact euc_ge_one_of_ne_zero v hv

theorem euc_lt_one_iff_eq_zero (v : ℤ × ℤ) : euc v < 1 ↔ v = 0 := by
  constructor
  · intro hlt
    by_contra hne
    exact (not_lt.mpr (euc_ge_one_of_ne_zero v hne)) hlt
  · intro hv
    subst hv
    unfold euc
    simp [Real.sqrt_zero]

/-- No nonzero integer vector (hence no lattice vector) has
    Euclidean length in `(0,1)`. This is the hole in
    “`C·|Λ|` is a lattice length”. -/
theorem not_exists_nonzero_euc_lt_one (B : ℕ) :
    ¬ ∃ v ∈ L B, v ≠ 0 ∧ euc v < 1 := by
  intro ⟨v, _, hne, hlt⟩
  exact hne ((euc_lt_one_iff_eq_zero v).mp hlt)

/-- Candidate “short” vector: second coordinate `0`, so it is a
    multiple of `b1`. The extra integer `k` can always cancel
    the first coordinate. -/
noncomputable def v_short (A B : ℕ) (k : ℤ) : ℤ × ℤ :=
  (⌊(C_LLL : ℝ) * Real.log (A : ℝ)⌋ - 13 * cLog B - k, 0)

theorem v_short_snd (A B : ℕ) (k : ℤ) : (v_short A B k).2 = 0 := rfl

theorem v_short_mem_L (A B : ℕ) (k : ℤ) : v_short A B k ∈ L B := by
  refine ⟨⌊(C_LLL : ℝ) * Real.log (A : ℝ)⌋ - 13 * cLog B - k, 0, ?_⟩
  simp [v_short]

theorem v_short_eq_zero_iff (A B : ℕ) (k : ℤ) :
    v_short A B k = 0 ↔
      k = ⌊(C_LLL : ℝ) * Real.log (A : ℝ)⌋ - 13 * cLog B := by
  constructor
  · intro h
    have h1 := congrArg Prod.fst h
    simp [v_short] at h1
    linarith
  · intro hk
    simp [v_short, hk]

/-- `∃ k` with `euc (v_short k) < 1` is true because some `k`
    makes `v_short = 0`. This does **not** use `|Λ|` and does
    **not** produce a nonzero short vector. -/
theorem exists_k_v_short_euc_lt_one (A B : ℕ) :
    ∃ k : ℤ, euc (v_short A B k) < 1 := by
  refine ⟨⌊(C_LLL : ℝ) * Real.log (A : ℝ)⌋ - 13 * cLog B, ?_⟩
  have hz : v_short A B
      (⌊(C_LLL : ℝ) * Real.log (A : ℝ)⌋ - 13 * cLog B) = 0 :=
    (v_short_eq_zero_iff A B _).mpr rfl
  rw [hz]
  exact (euc_lt_one_iff_eq_zero 0).mpr rfl

theorem v_short_euc_lt_one_iff_zero (A B : ℕ) (k : ℤ) :
    euc (v_short A B k) < 1 ↔ v_short A B k = 0 :=
  euc_lt_one_iff_eq_zero _

/-- The `h_exists` hypothesis of the lift: a small `|Λ|` would
    have to produce a *nonzero* lattice vector of length `< 1`.
    Uninhabited — that vector cannot exist in `ℤ×ℤ`. -/
noncomputable def short_vector_from_Lambda_lt_B8 (A B : ℕ) : Prop :=
  |4 * Real.log (A : ℝ) - 13 * Real.log ((B : ℝ) + 3)| <
      1 / (B : ℝ) ^ 8 →
    ∃ v ∈ L B, v ≠ 0 ∧ euc v < 1

/-- If a small `|Λ|` produced a nonzero `v ∈ L` of length `< 1`,
    then `|Λ| ≥ B⁻⁸`. Instantiating `h_short` is `lambda1_ge_one`.
    Instantiating `h_exists` is `short_vector_from_Lambda_lt_B8`,
    which `not_exists_nonzero_euc_lt_one` refutes. -/
theorem LLL_lift_to_B8_of_short_vector {A B : ℕ} (_hB : B0_nat ≤ B)
    (h_short : ∀ v ∈ L B, v ≠ 0 → 1 ≤ euc v)
    (h_exists :
      |4 * Real.log (A : ℝ) - 13 * Real.log ((B : ℝ) + 3)| <
          1 / (B : ℝ) ^ 8 →
        ∃ v ∈ L B, v ≠ 0 ∧ euc v < 1) :
    1 / (B : ℝ) ^ 8 ≤
      |4 * Real.log (A : ℝ) - 13 * Real.log ((B : ℝ) + 3)| := by
  by_contra hlt
  have ⟨v, hvL, hv_ne, hv_lt⟩ := h_exists (lt_of_not_ge hlt)
  have hge := h_short v hvL hv_ne
  linarith

/-- Same implication with `lambda1_ge_one` already plugged in. -/
theorem LLL_lift_to_B8_of_exists_short {A B : ℕ} (hB : B0_nat ≤ B)
    (h_exists : short_vector_from_Lambda_lt_B8 A B) :
    1 / (B : ℝ) ^ 8 ≤
      |4 * Real.log (A : ℝ) - 13 * Real.log ((B : ℝ) + 3)| :=
  LLL_lift_to_B8_of_short_vector hB lambda1_ge_one h_exists

/-- Floor error `< 1` on `C log(B+3)`. Kills an integer kernel;
    it does not produce a vector of length `C·|Λ|`. -/
theorem cLog_error_lt_one (B : ℕ) :
    |(C_LLL : ℝ) * Real.log ((B : ℝ) + 3) - cLog B| < 1 := by
  unfold cLog
  rw [Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg _)]
  exact Int.fract_lt_one _

/-- On a solution with `B ≥ B0`, `|Λ| ≤ 2/B⁹` so
    `C·|Λ| ≤ C·2/B⁹ < 1`. Combined with `λ₁ ≥ 1` this shows
    `C·|Λ|` is **smaller than every nonzero lattice length**,
    hence cannot itself be a lattice length. -/
theorem C_LLL_mul_abs_Lambda_lt_one_of_sol {A B : ℕ}
    (hB : B0_nat ≤ B) (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (C_LLL : ℝ) *
      |4 * Real.log (A : ℝ) - 13 * Real.log ((B : ℝ) + 3)| < 1 := by
  have h100B0 : 100 ≤ B0_nat := by
    rw [B0_nat_eq]
    decide
  have h100 : 100 ≤ B := h100B0.trans hB
  have hup := abs_Lambda_lt_two_div_B_pow_nine h100 hsol
  have hC : 0 ≤ (C_LLL : ℝ) := Nat.cast_nonneg _
  have hmul :
      (C_LLL : ℝ) *
        |4 * Real.log (A : ℝ) - 13 * Real.log ((B : ℝ) + 3)| ≤
      (C_LLL : ℝ) * (2 / (B : ℝ) ^ 9) :=
    mul_le_mul_of_nonneg_left hup hC
  exact lt_of_le_of_lt hmul (C_LLL_mul_two_div_B_pow_nine_lt_one hB)

#check abs_Lambda_ge_B_pow_neg_eight
#check LLL_reduces_C1_to_lt_nine
#check LLL_reduces_bound_to_B0_v25
#check no_sol_of_abs_Lambda_ge_B_pow_neg_eight
#check LLL_closes_B_ge_B0_of_pow_neg_eight
#check future_v25_shape_of_B8_lift
#check C_LLL_eq
#check lambda1_ge_one
#check v_short_mem_L
#check not_exists_nonzero_euc_lt_one
#check LLL_lift_to_B8_of_short_vector
#check C_LLL_mul_inv_B_pow_eight_lt_half
#check C_LLL_mul_two_div_B_pow_nine_lt_one
#check C_LLL_mul_abs_Lambda_lt_one_of_sol
#print axioms no_sol_of_abs_Lambda_ge_B_pow_neg_eight
#print axioms future_v25_shape_of_B8_lift
#print axioms lambda1_ge_one
#print axioms not_exists_nonzero_euc_lt_one
#print axioms LLL_lift_to_B8_of_short_vector
#print axioms C_LLL_mul_inv_B_pow_eight_lt_half

end BealMatveevBeal.LLLTargetB8
