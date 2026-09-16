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
import BugeaudLaurent

/-!
# p-adic LLL / `A ∈ [B, B+10]` no-go (not a v25 mint)

Successor of `v24-v24x-final-bugeaud-laurent-nogo`. This file
records that Mathlib 4.12 already has `PadicInt` / `ℤ_[p]`, but
**not** LLL over `ℤ_p` (there is no LLL module at all). It does **not** fork Mathlib,
does **not** open a Mathlib PR, and does **not** change `lean-toolchain`.
It does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

It also kills the false brute-force window `A ∈ [B, B+10]`
proposed for sharding `matveev_gap3_lower`: on a gap-`k` solution
with `k ≥ 1` and `B ≥ 2` one has `¬ A ≤ B+10`, because
`2 (B+10)⁴ < (B+1)¹³ ≤ (B+k)¹³`. That window contradicts
`gap3_A_bounds` (`B < A` and `A ≈ (B+3)^{13/4}`).
`matveev_gap3_lower` is already the integer-gap close, 0 sorry;
do **not** rewrite `MatveevLLL.lean` with 977 `native_decide`
shards, and do **not** touch `BealLevel26FoundationsScaffold`.

The floor lattice `b1=(1,0)`, `b2=(⌊C_LLL α⌋, C_LLL)` with
`C_LLL = C1_floor^2` still contains `(1,0)` of Euclidean length
`1 < B0`, so the draft `lll_lower_bound` is false. Floor error
`< 1` kills the integer kernel; it does not kill `(1,0)`.
`LLL_reduces_bound_to_B0_theorem` /
`beal_gap3_4_4_13_unconditional_v25_draft` stay `def Prop`.
`matveev_gap3_lower` is not `¬∃ A`. v25 is not minted.

`p_adic_LLL_reduction` / `hLLL_padic` / `baker_bound_B0_1e6` /
`LLL_reduces_bound_to_B0` stay `def Prop`. Defining the reduced
predicate as the constant true proposition would inhabit
`∀ L, ∃ L', reduced L'` and is forbidden. The toy comparison
`4 ≤ 1000` does **not** bound `B`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
Do **not** delete `BealGap1`–`BealGap15`, `BealGapK`,
`EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6`, or
`BugeaudLaurent`.
-/

noncomputable section

set_option maxHeartbeats 400000

open Real

namespace BealMatveevBeal.PAdicLLL

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_bl :
    C1_floor = BealMatveevBeal.BugeaudLaurent.C1_floor :=
  rfl

theorem B0_nat_eq_bl :
    B0_nat = BealMatveevBeal.BugeaudLaurent.B0_nat :=
  rfl

def C1_padic_floor_placeholder : ℕ := 1000

theorem C1_padic_floor_placeholder_eq :
    C1_padic_floor_placeholder = 1000 :=
  rfl

/-- Naive `4 ≤ 1000` comparison that does **not** bound `B`.
    The skeleton `4 v_p(A) ≤ 1000 · log A1 · log A2 · log b` is
    true for this placeholder and proves nothing about `B ≤ B0`. -/
theorem four_le_C1_padic_placeholder :
    4 ≤ C1_padic_floor_placeholder := by
  rw [C1_padic_floor_placeholder_eq]
  decide

theorem four_le_thousand : 4 ≤ 1000 := four_le_C1_padic_placeholder

/-! ## Kernel claims stay `def Prop` -/

def is_gapK_sol (k A B : ℕ) : Prop :=
  BealMatveevBeal.BugeaudLaurent.is_gapK_sol k A B

def baker_bound_B0_1e6 : Prop :=
  BealMatveevBeal.BugeaudLaurent.baker_bound_B0_1e6

def hGen_padic : Prop :=
  BealMatveevBeal.BugeaudLaurent.hGen_padic

def hLLL_padic : Prop :=
  BealMatveevBeal.BugeaudLaurent.hLLL_padic

/-- p-adic LLL / Baker–Davenport close. Mathlib 4.12 has
    `PadicInt` / `ℤ_[p]` but no LLL module, p-adic or
    archimedean. Stays uninhabited. -/
def p_adic_LLL_reduction : Prop :=
  BealMatveevBeal.BugeaudLaurent.p_adic_LLL_reduction

/-- Alias of `p_adic_LLL_reduction`. Must **not** be `True`:
    that would inhabit `∀ L, ∃ L', reduced L'`. -/
def p_adic_LLL_reduced : Prop :=
  p_adic_LLL_reduction

/-- The skeleton `∀ A B C, A⁴+B⁴=C¹³ → B ≤ 10⁶`. Same claim as
    `baker_bound_B0_1e6`; stays uninhabited. -/
def LLL_reduces_bound_to_B0 : Prop :=
  baker_bound_B0_1e6

def bugeaud_laurent_1996_two_logs : Prop :=
  BealMatveevBeal.BugeaudLaurent.bugeaud_laurent_1996_two_logs

def baker_bound_B0_1e6_of_bugeaud_lll : Prop :=
  bugeaud_laurent_1996_two_logs →
    p_adic_LLL_reduction →
      baker_bound_B0_1e6

/-! ## What Mathlib 4.12 *does* give: `ℤ_p = PadicInt` -/

/-- Mathlib 4.12 already has this ring. It is **not** an LLL
    lattice and does not inhabit `p_adic_LLL_reduction`. -/
abbrev Z_p (p : ℕ) [Fact p.Prime] := PadicInt p

theorem Z_p_norm_le_one {p : ℕ} [Fact p.Prime] (x : Z_p p) :
    ‖(x : ℚ_[p])‖ ≤ 1 :=
  x.2

/-! ## Size lemma: a gap solution cannot have `A ≤ B+10` -/

theorem n_add_nine_le_four_mul {n : ℕ} (hn : 3 ≤ n) :
    n + 9 ≤ 4 * n := by omega

theorem five_hundred_twelve_lt_pow_nine {n : ℕ} (hn : 3 ≤ n) :
    512 < n ^ 9 := by
  have h3 : 512 < 3 ^ 9 := by decide
  exact lt_of_lt_of_le h3 (Nat.pow_le_pow_left hn 9)

/-- For `n ≥ 3`, `2(n+9)⁴ < n¹³`. No expansion of a large
    thirteenth power of `B+k`. -/
theorem two_mul_succ_add_nine_pow_four_lt_pow_thirteen {n : ℕ}
    (hn : 3 ≤ n) : 2 * (n + 9) ^ 4 < n ^ 13 := by
  have hle : n + 9 ≤ 4 * n := n_add_nine_le_four_mul hn
  have hpow : (n + 9) ^ 4 ≤ (4 * n) ^ 4 := Nat.pow_le_pow_left hle 4
  have h2 : 2 * (n + 9) ^ 4 ≤ 2 * (4 * n) ^ 4 :=
    Nat.mul_le_mul_left 2 hpow
  have h4pow : (4 * n) ^ 4 = 4 ^ 4 * n ^ 4 := mul_pow 4 n 4
  have h512eq : 2 * (4 * n) ^ 4 = 512 * n ^ 4 := by
    rw [h4pow]
    have : (4 : ℕ) ^ 4 = 256 := by decide
    rw [this, ← mul_assoc]
    norm_num
  have hpos : 0 < n ^ 4 :=
    Nat.pos_pow_of_pos 4 (lt_of_lt_of_le (by decide : 0 < 3) hn)
  have hmul : 512 * n ^ 4 < n ^ 9 * n ^ 4 :=
    Nat.mul_lt_mul_of_pos_right (five_hundred_twelve_lt_pow_nine hn) hpos
  have h13 : n ^ 9 * n ^ 4 = n ^ 13 := by
    rw [← pow_add n 9 4]
  have hlt : 2 * (4 * n) ^ 4 < n ^ 13 := by
    rw [h512eq, ← h13]
    exact hmul
  exact lt_of_le_of_lt h2 hlt

theorem B_add_ten_eq_succ_add_nine (B : ℕ) :
    B + 10 = B + 1 + 9 := by omega

theorem two_mul_B_add_ten_pow_four_lt_succ_pow_thirteen {B : ℕ}
    (hB : 2 ≤ B) : 2 * (B + 10) ^ 4 < (B + 1) ^ 13 := by
  have hn : 3 ≤ B + 1 := Nat.succ_le_succ hB
  simpa [B_add_ten_eq_succ_add_nine] using
    two_mul_succ_add_nine_pow_four_lt_pow_thirteen hn

/-- On a positive-gap solution with `B ≥ 2`, `A` cannot lie in
    `[B, B+10]`. Combined with `A_gt_B_of_sol` this kills the
    proposed `[B, B+10]` search. -/
theorem not_A_le_B_add_ten_of_sol {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 2 ≤ B) :
    ¬ A ≤ B + 10 := by
  intro hA
  have hA4 : A ^ 4 ≤ (B + 10) ^ 4 := Nat.pow_le_pow_left hA 4
  have hB4 : B ^ 4 ≤ (B + 10) ^ 4 :=
    Nat.pow_le_pow_left (Nat.le_add_right B 10) 4
  have hsum : A ^ 4 + B ^ 4 ≤ 2 * (B + 10) ^ 4 := by
    have := Nat.add_le_add hA4 hB4
    simpa [two_mul] using this
  have hlt1 := two_mul_B_add_ten_pow_four_lt_succ_pow_thirteen hB
  have hleC : B + 1 ≤ B + k := Nat.add_le_add_left hk B
  have hpow : (B + 1) ^ 13 ≤ (B + k) ^ 13 :=
    Nat.pow_le_pow_left hleC 13
  have hlt : A ^ 4 + B ^ 4 < (B + k) ^ 13 :=
    lt_of_le_of_lt hsum (lt_of_lt_of_le hlt1 hpow)
  exact (ne_of_lt hlt) h

theorem A_gt_B_of_sol {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 0 < B) : B < A :=
  BealMatveevBeal.BealGapK.A_gt_B_of_sol hk h hB

/-- The proposed native_decide window is empty of solutions. -/
theorem not_A_in_B_B_add_ten_of_sol {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 2 ≤ B) :
    ¬ (B ≤ A ∧ A ≤ B + 10) := by
  intro hwin
  exact not_A_le_B_add_ten_of_sol hk h hB hwin.2

/-- Gap-3 specialisation: `A ∈ [B, B+10]` cannot contain a
    solution of `A⁴+B⁴=(B+3)¹³` when `B ≥ 2`. This is why
    `check_gap3_range` with that window cannot close
    `matveev_gap3_lower` (already the integer-gap theorem). -/
theorem not_A_le_B_add_ten_of_gap3 {A B : ℕ}
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 2 ≤ B) :
    ¬ A ≤ B + 10 :=
  not_A_le_B_add_ten_of_sol (by decide : (1 : ℕ) ≤ 3) h hB

theorem two_le_of_B_ge_B0 {B : ℕ} (hB0 : B0_nat ≤ B) : 2 ≤ B := by
  have h2 : 2 ≤ B0_nat := by
    rw [B0_nat_eq]
    decide
  exact Nat.le_trans h2 hB0

/-! ## Wrapped Bugeaud–Laurent facts -/

theorem two_val_equation_compatible_odd_k {k A B : ℕ}
    (hk : Odd k) (h : is_gapK_sol k A B) (hB : 0 < B) :
    padicValNat 2 (A ^ 4 + B ^ 4) = 0 ∧
      padicValNat 2 ((B + k) ^ 13) = 0 :=
  BealMatveevBeal.BugeaudLaurent.two_val_equation_compatible_odd_k hk h hB

theorem hGen_exp_lt_ratio_gapK
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {k A B : ℕ} (hk : 1 ≤ k) (hsol : is_gapK_sol k A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  BealMatveevBeal.BugeaudLaurent.hGen_exp_lt_ratio_gapK hC1 hk hsol hB hB0

theorem C1_padic_placeholder_loses_in_reals {k A B : ℕ}
    (hk : 1 ≤ k) (hsol : is_gapK_sol k A B) (hB : 0 < B)
    (hB0 : B0_nat ≤ B) :
    exp (-(C1_padic_floor_placeholder : ℝ) * log (A : ℝ) *
        log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  BealMatveevBeal.BugeaudLaurent.C1_padic_placeholder_loses_in_reals
    hk hsol hB hB0

theorem C_lt_hundred_of_A_B_le_B0 {A B C : ℕ}
    (h : A ^ 4 + B ^ 4 = C ^ 13)
    (hA : A ≤ B0_nat) (hB : B ≤ B0_nat) :
    C < 100 :=
  BealMatveevBeal.BugeaudLaurent.C_lt_hundred_of_A_B_le_B0 h hA hB

/-! ## Combined no-go: p-adic LLL stays uninhabited; window false -/

theorem p_adic_LLL_unconditional_nogo {k A B : ℕ}
    (hk : 1 ≤ k) (hsol : is_gapK_sol k A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (Odd k →
      padicValNat 2 (A ^ 4 + B ^ 4) = 0 ∧
        padicValNat 2 ((B + k) ^ 13) = 0) ∧
    100 ≤ B + k ∧
    ¬ B + k ≤ 73 ∧
    ¬ A ≤ B + 10 ∧
    (hGen_padic → False) ∧
    (bugeaud_laurent_1996_two_logs → False) ∧
    (baker_bound_B0_1e6 → B ≤ B0_nat) ∧
    (LLL_reduces_bound_to_B0 → B ≤ B0_nat) := by
  have hnogo :=
    BealMatveevBeal.BugeaudLaurent.bugeaud_laurent_unconditional_nogo
      hk hsol hB hB0
  obtain ⟨hlogs, h2, hC, h73, hp, hbl, hb, _⟩ := hnogo
  refine ⟨hlogs, h2, hC, h73, ?_, hp, hbl, hb, hb⟩
  exact not_A_le_B_add_ten_of_sol hk hsol (two_le_of_B_ge_B0 hB0)

/-! ## Floor lattice `b1=(1,0)` still has length 1 — not a B0 cutoff -/

/-- Rank-2 Bugeaud–Laurent *shape* with `det = C1²`. The first
    displayed vector is `(1,0)`. -/
def C_LLL : ℕ := C1_floor * C1_floor

theorem C_LLL_eq : C_LLL = C1_floor * C1_floor := rfl

noncomputable def alpha (B : ℕ) : ℝ := Real.log ((B + 3 : ℕ) : ℝ)

noncomputable def LLL_basis (B : ℕ) : (ℤ × ℤ) × (ℤ × ℤ) :=
  ((1, 0), (⌊(C_LLL : ℝ) * alpha B⌋, (C_LLL : ℤ)))

theorem LLL_basis_b1 (B : ℕ) : (LLL_basis B).1 = (1, 0) := rfl

/-- The naive integer form has a kernel. Same fact as
    `PAdicLLL_ZeroAxiom.nat_int_form_has_kernel`. -/
theorem nat_int_form_has_kernel (a C1 : ℤ) (hC1 : C1 ≠ 0) :
    ∃ u v : ℤ, (u, v) ≠ (0, 0) ∧ u * a + v * C1 = 0 := by
  refine ⟨C1, -a, ?_, ?_⟩
  · intro h
    exact hC1 (congrArg Prod.fst h)
  · ring

theorem C1_div_two_gt_B0 : B0_nat < C1_floor / 2 := by
  rw [B0_nat_eq, C1_floor_eq]
  decide

/-- Euclidean square of the `(u,v)=(1,0)` combination is `1`,
    independently of the floor coordinate. -/
theorem displayed_combo_one_zero_sq (B : ℕ) :
    let fl : ℤ := ⌊(C_LLL : ℝ) * alpha B⌋
    ((1 : ℝ) + (0 : ℝ) * (fl : ℝ)) ^ 2 + ((0 : ℝ) * (C_LLL : ℝ)) ^ 2 = 1 := by
  simp

/-- Same identity with the `ℤ` coercions that appear when the
    draft lower bound is instantiated at `(u,v)=(1,0)`. -/
theorem combo_one_zero_sq_cast (B : ℕ) :
    ((((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * (⌊(C_LLL : ℝ) * alpha B⌋ : ℝ)) ^ 2 +
      (((0 : ℤ) : ℝ) * (C_LLL : ℝ)) ^ 2) = (1 : ℝ) := by
  simp

theorem combo_one_zero_length (B : ℕ) :
    Real.sqrt
        ((((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * (⌊(C_LLL : ℝ) * alpha B⌋ : ℝ)) ^ 2 +
          (((0 : ℤ) : ℝ) * (C_LLL : ℝ)) ^ 2) = (1 : ℝ) := by
  rw [combo_one_zero_sq_cast B, Real.sqrt_one]

theorem one_lt_B0_nat : 1 < B0_nat := by
  rw [B0_nat_eq]
  decide

theorem one_lt_B0_real : (1 : ℝ) < (B0_nat : ℝ) := by
  rw [B0_nat_eq]
  norm_num

/-- Floor error is strictly less than `1`. This kills the integer
    kernel `u a + v C1 = 0`, but it does not kill `(1,0)`. -/
theorem floor_C_alpha_error_lt_one (B : ℕ) :
    |(C_LLL : ℝ) * alpha B - ⌊(C_LLL : ℝ) * alpha B⌋| < 1 := by
  rw [Int.self_sub_floor, abs_of_nonneg (Int.fract_nonneg _)]
  exact Int.fract_lt_one _

/-- `(1,0)` is the displayed combination `1·b1 + 0·b2`. -/
theorem LLL_b1_is_combo (B : ℕ) :
    ((1 : ℤ) * (LLL_basis B).1.1 + (0 : ℤ) * (LLL_basis B).2.1,
      (1 : ℤ) * (LLL_basis B).1.2 + (0 : ℤ) * (LLL_basis B).2.2) = (1, 0) := by
  simp [LLL_basis]

/-- The draft `lll_lower_bound` (`‖u b1 + v b2‖ ≥ B0` for all
    nonzero `(u,v)`) is **false**: `(1,0)` has length `1 < B0`.
    Floor error `< 1` kills the integer kernel, but it does not
    kill the lattice vector `(1,0)`. `C1_floor / 2 > B0` is a
    numeral, not `λ₁`. -/
theorem lll_euclidean_lower_bound_fails (B : ℕ) :
    ¬ (∀ u v : ℤ, (u, v) ≠ (0, 0) →
        Real.sqrt
            (((u : ℝ) + (v : ℝ) * (⌊(C_LLL : ℝ) * alpha B⌋ : ℝ)) ^ 2 +
              ((v : ℝ) * (C_LLL : ℝ)) ^ 2) ≥
          (B0_nat : ℝ)) := by
  intro h
  have hge := h (1 : ℤ) (0 : ℤ) (by decide : ((1 : ℤ), (0 : ℤ)) ≠ (0, 0))
  rw [combo_one_zero_length B] at hge
  exact (not_le.mpr one_lt_B0_real) hge

/-- Packaged floor-lattice no-go: first basis vector is `(1,0)`,
    its Euclidean length is `1`, and `1 < B0`. The numeral
    `C1_floor / 2 > B0` is recorded separately and is not `λ₁`. -/
theorem floor_lattice_nogo (B : ℕ) :
    (LLL_basis B).1 = (1, 0) ∧
      Real.sqrt
          ((((1 : ℤ) : ℝ) + ((0 : ℤ) : ℝ) * (⌊(C_LLL : ℝ) * alpha B⌋ : ℝ)) ^ 2 +
            (((0 : ℤ) : ℝ) * (C_LLL : ℝ)) ^ 2) = (1 : ℝ) ∧
        (1 : ℝ) < (B0_nat : ℝ) ∧
          B0_nat < C1_floor / 2 :=
  ⟨LLL_basis_b1 B, combo_one_zero_length B, one_lt_B0_real, C1_div_two_gt_B0⟩

/-- Draft `LLL_reduces_bound_to_B0_theorem`. Uninhabited: the
    displayed Euclidean lower bound is false, Matveev+LLL already
    lose on `B ≥ B0`, and `matveev_gap3_lower` is not `¬∃ A`. -/
def LLL_reduces_bound_to_B0_theorem : Prop :=
  ∀ B : ℕ, B0_nat < B → B ≤ C1_floor →
    ∀ A : ℕ, B < A → A ^ 4 + B ^ 4 = (B + 3) ^ 13 → False

/-- Draft unconditional v25. Uninhabited. -/
def beal_gap3_4_4_13_unconditional_v25_draft : Prop :=
  ∀ B : ℕ, ¬ ∃ A : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13

#check C1_floor_eq
#check B0_nat_eq
#check C1_padic_floor_placeholder_eq
#check four_le_C1_padic_placeholder
#check four_le_thousand
#check Z_p_norm_le_one
#check n_add_nine_le_four_mul
#check five_hundred_twelve_lt_pow_nine
#check two_mul_succ_add_nine_pow_four_lt_pow_thirteen
#check two_mul_B_add_ten_pow_four_lt_succ_pow_thirteen
#check not_A_le_B_add_ten_of_sol
#check A_gt_B_of_sol
#check not_A_in_B_B_add_ten_of_sol
#check not_A_le_B_add_ten_of_gap3
#check two_val_equation_compatible_odd_k
#check C1_padic_placeholder_loses_in_reals
#check C_lt_hundred_of_A_B_le_B0
#check p_adic_LLL_reduction
#check p_adic_LLL_reduced
#check LLL_reduces_bound_to_B0
#check baker_bound_B0_1e6
#check hGen_padic
#check hLLL_padic
#check baker_bound_B0_1e6_of_bugeaud_lll
#check p_adic_LLL_unconditional_nogo
#check nat_int_form_has_kernel
#check LLL_basis_b1
#check C1_div_two_gt_B0
#check displayed_combo_one_zero_sq
#check combo_one_zero_sq_cast
#check combo_one_zero_length
#check one_lt_B0_real
#check floor_C_alpha_error_lt_one
#check LLL_b1_is_combo
#check lll_euclidean_lower_bound_fails
#check floor_lattice_nogo
#check LLL_reduces_bound_to_B0_theorem
#check beal_gap3_4_4_13_unconditional_v25_draft
#print axioms C1_floor_eq
#print axioms B0_nat_eq
#print axioms four_le_C1_padic_placeholder
#print axioms two_mul_B_add_ten_pow_four_lt_succ_pow_thirteen
#print axioms not_A_le_B_add_ten_of_sol
#print axioms not_A_le_B_add_ten_of_gap3
#print axioms A_gt_B_of_sol
#print axioms Z_p_norm_le_one
#print axioms p_adic_LLL_unconditional_nogo
#print axioms nat_int_form_has_kernel
#print axioms lll_euclidean_lower_bound_fails
#print axioms combo_one_zero_length
#print axioms floor_C_alpha_error_lt_one
#print axioms floor_lattice_nogo
#print axioms C1_div_two_gt_B0

end BealMatveevBeal.PAdicLLL
