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
import EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6

/-!
# Bugeaud–Laurent / p-adic LLL / Frey-32 import plan (not a v25 mint)

Successor of `v24-v24x-final-effective-padic-nogo`. This file
records **what Mathlib 4.12 actually has** and **what would be
needed** to inhabit `baker_bound_B0_1e6`. It does **not** fork
Mathlib, does **not** open a Mathlib PR, does **not** change
`lean-toolchain`, and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

Mathlib 4.12 supplies `ℚ_[p]`, `padicNorm`, `padicValNat`,
`WeierstrassCurve` / `EllipticCurve`, and the abstract
`ModularForm` space. It does **not** supply:

* an Iwasawa p-adic logarithm `log_p : ℚ_[p] → ℚ_[p]`;
* Bugeaud–Laurent 1996 explicit linear forms in two p-adic logs;
* LLL over `ℤ_p` (there is no LLL module at all);
* Tate's algorithm / Néron conductor;
* Ribet level-lowering, Mazur torsion on this Frey curve,
  or `dim S₂(32) = 1` / newform `32a1`.

Real-log Matveev / LLL already lose every `C1 ≥ 1` on gap
solutions with `B ≥ B0`, including `C1_floor` **and** the
placeholder numeral `1000`. The 2-adic valuation of
`A⁴+B⁴=C¹³` is compatible when `k` is odd (`B` even, `A` odd,
`C` odd, both sides have `v₂ = 0`), so a valuation identity
does not replace p-adic logs. The conditional `C < 100` lemma
needs `A,B ≤ B0` already; on `B ≥ B0` one has `C ≥ 1000001`.

`bugeaud_laurent_1996_two_logs` / `p_adic_LLL_reduction` /
`baker_bound_B0_1e6` stay `def Prop`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
Do **not** delete `BealGap1`–`BealGap15`, `BealGapK`, or
`EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6`.
-/

noncomputable section

set_option maxHeartbeats 400000

open Real

namespace BealMatveevBeal.BugeaudLaurent

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_eff :
    C1_floor =
      BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.C1_floor :=
  rfl

theorem B0_nat_eq_eff :
    B0_nat =
      BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.B0_nat :=
  rfl

/-- Placeholder numeral sometimes quoted as a hoped-for p-adic
    `C1`. It is **not** a Bugeaud–Laurent constant. Real logs
    already lose at `C1 = 1`, so this numeral does not close
    `hGen_padic` either. -/
def C1_padic_floor_placeholder : ℕ := 1000

theorem C1_padic_floor_placeholder_eq :
    C1_padic_floor_placeholder = 1000 :=
  rfl

theorem C1_padic_floor_placeholder_ge_one :
    (1 : ℝ) ≤ C1_padic_floor_placeholder := by
  rw [C1_padic_floor_placeholder_eq]
  norm_num

/-! ## Kernel claims stay `def Prop` -/

def is_gapK_sol (k A B : ℕ) : Prop :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.is_gapK_sol
    k A B

def baker_bound_B0_1e6 : Prop :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.baker_bound_B0_1e6

def hGen_padic : Prop :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.hGen_padic

def hLLL_padic : Prop :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.hLLL_padic

def baker_bound_gapK_unconditional_wins : Prop :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.baker_bound_gapK_unconditional_wins

def beal_conjecture_4413 : Prop :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.beal_conjecture_4413

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealTrueV25.darmon_merel_44_13_no_coprime

def fermat_last_theorem_thirteen : Prop :=
  BealMatveevBeal.BealTrueV25.fermat_last_theorem_thirteen

def ribet_level_lowering_to_32 : Prop :=
  BealMatveevBeal.BealTrueV25.ribet_level_lowering_to_32

/-- Bugeaud–Laurent 1996 Thm 1, specialised to a cutoff
    `B ≤ 10⁶` on `A⁴+B⁴=C¹³`. Not in Mathlib 4.12: there is no
    Iwasawa `log_p` and no explicit `c(p)`. -/
def bugeaud_laurent_1996_two_logs : Prop :=
  hGen_padic

/-- p-adic LLL / Baker–Davenport close. Mathlib 4.12 has no LLL
    module, p-adic or archimedean. -/
def p_adic_LLL_reduction : Prop :=
  hLLL_padic

/-- Displayed Frey conductor `32 · rad(ABC)`. This is **not** the
    Néron conductor; Tate's algorithm is not in Mathlib 4.12. -/
def frey_conductor_eq_32_rad : Prop :=
  ribet_level_lowering_to_32

/-- `dim S₂(32) = 1` / newform `32a1`. Mathlib 4.12 has
    `ModularForm` spaces but no dimension formula at level 32. -/
def S2_32_dimension_one : Prop :=
  darmon_merel_44_13_no_coprime

/-- Mazur: no rational 13-torsion on the displayed Frey curve.
    Not in Mathlib 4.12 for this model. -/
def mazur_no_13_torsion_Frey : Prop :=
  darmon_merel_44_13_no_coprime

/-- Kraus elimination against `32a1` mod 13. Not in Mathlib 4.12. -/
def kraus_elimination_32a1 : Prop :=
  darmon_merel_44_13_no_coprime

def baker_bound_B0_1e6_of_bugeaud_lll : Prop :=
  bugeaud_laurent_1996_two_logs →
    p_adic_LLL_reduction →
      baker_bound_B0_1e6

/-! ## What Mathlib 4.12 *does* give: 2-adic valuations -/

theorem two_val_eq_zero_of_odd {n : ℕ} (h : Odd n) :
    padicValNat 2 n = 0 :=
  padicValNat.eq_zero_of_not_dvd (fun hd =>
    Nat.not_even_iff_odd.2 h (even_iff_two_dvd.2 hd))

theorem two_val_pos_of_even_pos {n : ℕ} (hpos : 0 < n) (he : Even n) :
    1 ≤ padicValNat 2 n := by
  have hne : padicValNat 2 n ≠ 0 := by
    intro h0
    have := (padicValNat.eq_zero_iff (p := 2) (n := n)).1 h0
    rcases this with h1 | hn | hd
    · exact (by decide : (2 : ℕ) ≠ 1) h1
    · exact (Nat.pos_iff_ne_zero.mp hpos) hn
    · exact hd (even_iff_two_dvd.mp he)
  exact Nat.succ_le_of_lt (Nat.pos_of_ne_zero hne)

theorem two_val_pow_four {n : ℕ} (hne : n ≠ 0) :
    padicValNat 2 (n ^ 4) = 4 * padicValNat 2 n := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact padicValNat.pow 4 hne

theorem two_val_B_pow_four_ge_four {B : ℕ}
    (hB : 0 < B) (he : Even B) :
    4 ≤ padicValNat 2 (B ^ 4) := by
  have hpow := two_val_pow_four (Nat.pos_iff_ne_zero.mp hB)
  have hge := two_val_pos_of_even_pos hB he
  have : 4 * 1 ≤ 4 * padicValNat 2 B := Nat.mul_le_mul_left 4 hge
  simpa [hpow] using this

theorem C_odd_of_odd_k_even_B {k B : ℕ}
    (hk : Odd k) (hB : Even B) :
    Odd (B + k) :=
  hB.add_odd hk

/-- On an odd-gap solution the 2-adic valuation of both sides is
    `0`. A valuation identity therefore does **not** kill
    `A⁴+B⁴=C¹³`; that is why Bugeaud–Laurent logs are missing. -/
theorem two_val_equation_compatible_odd_k {k A B : ℕ}
    (hk : Odd k) (h : is_gapK_sol k A B) (_hBpos : 0 < B) :
    padicValNat 2 (A ^ 4 + B ^ 4) = 0 ∧
      padicValNat 2 ((B + k) ^ 13) = 0 := by
  have hpar :=
    BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.parity_odd_k_gapK
      h hk
  have hAodd : Odd A := hpar.2
  have hBeven : Even B := hpar.1
  have hCodd : Odd (B + k) := C_odd_of_odd_k_even_B hk hBeven
  have hA4 : Odd (A ^ 4) := hAodd.pow
  have hC13 : Odd ((B + k) ^ 13) := hCodd.pow
  have hB4 : Even (B ^ 4) :=
    (Nat.even_pow' (by decide : 4 ≠ 0)).2 hBeven
  have hsum : Odd (A ^ 4 + B ^ 4) := hA4.add_even hB4
  refine ⟨two_val_eq_zero_of_odd hsum, two_val_eq_zero_of_odd hC13⟩

/-! ## Real logs still lose, including the p-adic placeholder -/

theorem hGen_exp_lt_ratio_gapK
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {k A B : ℕ} (hk : 1 ≤ k) (hsol : is_gapK_sol k A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.hGen_exp_lt_ratio_gapK
    hC1 hk hsol hB hB0

theorem C1_floor_hGen_loses_gapK {k A B : ℕ}
    (hk : 1 ≤ k) (hsol : is_gapK_sol k A B) (hB : 0 < B)
    (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.C1_floor_hGen_loses_gapK
    hk hsol hB hB0

theorem C1_one_loses_in_reals {k A B : ℕ}
    (hk : 1 ≤ k) (hsol : is_gapK_sol k A B) (hB : 0 < B)
    (hB0 : B0_nat ≤ B) :
    exp (-(1 : ℝ) * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio_gapK (le_refl (1 : ℝ)) hk hsol hB hB0

theorem C1_padic_placeholder_loses_in_reals {k A B : ℕ}
    (hk : 1 ≤ k) (hsol : is_gapK_sol k A B) (hB : 0 < B)
    (hB0 : B0_nat ≤ B) :
    exp (-(C1_padic_floor_placeholder : ℝ) * log (A : ℝ) *
        log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio_gapK C1_padic_floor_placeholder_ge_one hk hsol hB hB0

theorem C_lt_hundred_of_A_B_le_B0 {A B C : ℕ}
    (h : A ^ 4 + B ^ 4 = C ^ 13)
    (hA : A ≤ B0_nat) (hB : B ≤ B0_nat) :
    C < 100 :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.C_lt_hundred_of_A_B_le_B0
    h hA hB

theorem C_ge_hundred_of_B_ge_B0 {k B : ℕ}
    (hk : 1 ≤ k) (hB : B0_nat ≤ B) :
    100 ≤ B + k :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.C_ge_hundred_of_B_ge_B0
    hk hB

theorem not_C_le_seventy_three_of_B_ge_B0 {k B : ℕ}
    (hk : 1 ≤ k) (hB : B0_nat ≤ B) :
    ¬ B + k ≤ 73 :=
  BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.not_C_le_seventy_three_of_B_ge_B0
    hk hB

/-! ## Combined no-go: missing p-adic / modular ingredients stay uninhabited -/

theorem bugeaud_laurent_unconditional_nogo {k A B : ℕ}
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
    (hGen_padic → False) ∧
    (bugeaud_laurent_1996_two_logs → False) ∧
    (baker_bound_B0_1e6 → B ≤ B0_nat) ∧
    (baker_bound_gapK_unconditional_wins → B ≤ B0_nat) := by
  have hnogo :=
    BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.baker_bound_B0_1e6_unconditional_nogo
      hk hsol hB hB0
  obtain ⟨hlogs, _, _, hC, h73, hp, hb, hw, _⟩ := hnogo
  refine ⟨hlogs, ?_, hC, h73, hp, hp, hb, hw⟩
  intro hodd
  exact two_val_equation_compatible_odd_k hodd hsol hB

#check C1_floor_eq
#check B0_nat_eq
#check C1_padic_floor_placeholder_eq
#check two_val_eq_zero_of_odd
#check two_val_B_pow_four_ge_four
#check C_odd_of_odd_k_even_B
#check two_val_equation_compatible_odd_k
#check C1_one_loses_in_reals
#check C1_padic_placeholder_loses_in_reals
#check C_lt_hundred_of_A_B_le_B0
#check C_ge_hundred_of_B_ge_B0
#check bugeaud_laurent_1996_two_logs
#check p_adic_LLL_reduction
#check baker_bound_B0_1e6
#check hGen_padic
#check hLLL_padic
#check baker_bound_B0_1e6_of_bugeaud_lll
#check S2_32_dimension_one
#check bugeaud_laurent_unconditional_nogo
#print axioms C1_floor_eq
#print axioms B0_nat_eq
#print axioms two_val_eq_zero_of_odd
#print axioms two_val_equation_compatible_odd_k
#print axioms C1_padic_placeholder_loses_in_reals
#print axioms C_lt_hundred_of_A_B_le_B0
#print axioms bugeaud_laurent_unconditional_nogo

end BealMatveevBeal.BugeaudLaurent
