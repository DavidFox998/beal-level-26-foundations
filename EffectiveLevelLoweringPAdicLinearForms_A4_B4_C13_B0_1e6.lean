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
import BealGapK

/-!
# Effective level-lowering / p-adic linear forms (not a v25 mint)

Successor of `v24-v24x-final-gapK-generic-nogo`. Re-exports the
honest `BealGapK` infrastructure and records the displayed
Bugeaud / Kraus / Oesterlé / Ribet-to-32 / FLT 13 claims as
**uninhabited `def Prop`**. This does **not** replace
`darmon_merel_4413_axiom`, does **not** inhabit
`baker_bound_B0_1e6`, and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

None of Bugeaud–Laurent 1996, Kraus 1997, Oesterlé, Ribet
level-lowering, Kummer's regular-prime FLT, or a p-adic LLL
witness is in Mathlib 4.12. Real-log Matveev / LLL already lose
every `C1 ≥ 1` on gap solutions with `B ≥ B0` (`BealGapK`).
A displayed p-adic lower bound that would beat `B⁴/A⁴` is the
same missing inhabitant.

The estimate `C ≤ 73` for `B ≤ 10⁶` assumes `A ≤ 10⁶` as well
and is therefore circular as an unconditional Baker close.
Under `A ≤ B0` and `B ≤ B0` one does get `C < 100`, because
`C¹³ ≤ 2 · B0⁴ = 2 · 10²⁴ < 10²⁶ = 100¹³`. That is conditional
on both coordinates already sitting under the Baker cutoff, not
a substitute for it. Positive `k` does **not** force `B ≤ 72`:
`C = B+k` grows with `B`. On any gap solution with `B ≥ B0` and
`k ≥ 1` one has `100 ≤ C` and `¬ C ≤ 73`.

`hGen_padic` / `hLLL_padic` / `baker_bound_B0_1e6` stay
`def Prop`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
Do **not** delete `BealGap1`–`BealGap15` or `BealGapK`.
-/

noncomputable section

set_option maxHeartbeats 400000

open Real

namespace BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_gapK :
    C1_floor = BealMatveevBeal.BealGapK.C1_floor := rfl

theorem B0_nat_eq_gapK :
    B0_nat = BealMatveevBeal.BealGapK.B0_nat := rfl

/-! ## Equations -/

def is_A4_B4_C13_sol (A B C : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = C ^ 13 ∧ 0 < A ∧ 0 < B ∧ 0 < C

def is_gapK_sol (k A B : ℕ) : Prop :=
  BealMatveevBeal.BealGapK.is_gapK_sol k A B

theorem is_gapK_sol_iff (k A B : ℕ) :
    is_gapK_sol k A B ↔ A ^ 4 + B ^ 4 = (B + k) ^ 13 :=
  Iff.rfl

theorem gapK_of_C_eq_B_add_k {k A B : ℕ}
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) :
    is_gapK_sol k A B :=
  h

/-! ## Kernel claims stay `def Prop` -/

/-- Unrestricted Baker bound `B ≤ 10⁶` on `A⁴+B⁴=C¹³`.
    Stays a `def Prop`. -/
def baker_bound_B0_1e6 : Prop :=
  ∀ A B C : ℕ, A ^ 4 + B ^ 4 = C ^ 13 → B ≤ B0_nat

def baker_bound_gapK_unconditional_wins : Prop :=
  ∀ k A B : ℕ, is_gapK_sol k A B → B ≤ B0_nat

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealTrueV25.darmon_merel_44_13_no_coprime

def fermat_last_theorem_thirteen : Prop :=
  BealMatveevBeal.BealTrueV25.fermat_last_theorem_thirteen

def ribet_level_lowering_to_32 : Prop :=
  BealMatveevBeal.BealTrueV25.ribet_level_lowering_to_32

/-- Displayed Bugeaud–Laurent p-adic lower bound that would
    rule out every `B ≥ B0` solution. Not in Mathlib 4.12. -/
def hGen_padic : Prop :=
  ∀ A B C : ℕ,
    A ^ 4 + B ^ 4 = C ^ 13 →
      0 < A →
        0 < B →
          B0_nat ≤ B →
            False

/-- p-adic LLL / Baker–Davenport close for `B ≤ B0`.
    The displayed lattice does not inhabit it. -/
def hLLL_padic : Prop :=
  hGen_padic → baker_bound_B0_1e6

def baker_bound_B0_1e6_of_hGen_hLLL : Prop :=
  hGen_padic → hLLL_padic → baker_bound_B0_1e6

def beal_conjecture_4413 : Prop :=
  ∀ A B C : ℕ,
    0 < A → 0 < B → 0 < C → Nat.gcd A B = 1 →
      ¬ (A ^ 4 + B ^ 4 = C ^ 13)

/-! ## Section 1: parity and gcd (Even/Odd, from `BealGapK`) -/

theorem parity_odd_k_gapK {k A B : ℕ}
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) (hk : Odd k) :
    Even B ∧ Odd A :=
  ⟨BealMatveevBeal.BealGapK.B_even_of_sol_of_odd_k hk h,
    BealMatveevBeal.BealGapK.A_odd_of_sol_of_odd_k hk h⟩

theorem parity_even_k_gapK {k A B : ℕ}
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) (hk : Even k) :
    Even A :=
  BealMatveevBeal.BealGapK.A_even_of_sol_of_even_k hk h

theorem gcd_dvd_k_gapK (k B : ℕ) :
    Nat.gcd B (B + k) = Nat.gcd B k ∧ Nat.gcd B (B + k) ∣ k :=
  ⟨BealMatveevBeal.BealGapK.gcd_B_C_eq_gcd_k k B,
    BealMatveevBeal.BealGapK.gcd_B_C_dvd_k k B⟩

/-! ## Section 2: `p ∣ k` and `p ∣ B` force `p ∣ A` -/

theorem p_dvd_k_and_B_forces_p_dvd_A_gapK {k A B p : ℕ}
    (hp : Nat.Prime p) (hk : p ∣ k) (hB : p ∣ B)
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) : p ∣ A :=
  BealMatveevBeal.BealGapK.p_dvd_k_forces_p_dvd_A_gapK hp hk hB h

/-! ## Section 3: `v_p(k)=1` descents -/

theorem vp_one_descent_three_gapK {k A B : ℕ}
    (hk : 3 ∣ k) (hvp : ¬ 9 ∣ k) (hB : 3 ∣ B)
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) : False :=
  BealMatveevBeal.BealGapK.no_sol_when_p_dvd_k_three_gapK hk hvp h hB

theorem vp_one_descent_five_gapK {k A B : ℕ}
    (hk : 5 ∣ k) (hvp : ¬ 25 ∣ k) (hB : 5 ∣ B)
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) : False :=
  BealMatveevBeal.BealGapK.no_sol_when_p_dvd_k_five_gapK hk hvp h hB

theorem vp_one_descent_seven_gapK {k A B : ℕ}
    (hk : 7 ∣ k) (hvp : ¬ 49 ∣ k) (hB : 7 ∣ B)
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) : False :=
  BealMatveevBeal.BealGapK.no_sol_when_p_dvd_k_seven_gapK hk hvp h hB

theorem vp_one_descent_eleven_gapK {k A B : ℕ}
    (hk : 11 ∣ k) (hvp : ¬ 121 ∣ k) (hB : 11 ∣ B)
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) : False :=
  BealMatveevBeal.BealGapK.no_sol_when_p_dvd_k_eleven_gapK hk hvp h hB

theorem vp_one_descent_thirteen_gapK {k A B : ℕ}
    (hk : 13 ∣ k) (hvp : ¬ 169 ∣ k) (hB : 13 ∣ B)
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) : False :=
  BealMatveevBeal.BealGapK.no_sol_when_p_dvd_k_thirteen_gapK hk hvp h hB

/-! ## Section 4: residue kills with hypotheses -/

theorem residue_kill_three_k_eq_two_gapK {k A B : ℕ}
    (hk : ¬ 3 ∣ k) (hkmod : k % 3 = 2) (hB : 3 ∣ B)
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) : False :=
  BealMatveevBeal.BealGapK.no_sol_when_three_dvd_B_residue_gapK h hk hB hkmod

theorem residue_kill_five_k_eq_two_three_four_gapK {k A B : ℕ}
    (hk : ¬ 5 ∣ k)
    (hkmod : k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4)
    (hB : 5 ∣ B) (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) : False :=
  BealMatveevBeal.BealGapK.no_sol_when_five_dvd_B_residue_gapK h hk hB hkmod

theorem residue_kill_seven_k_eq_three_five_six_gapK {k A B : ℕ}
    (hk : ¬ 7 ∣ k)
    (hkmod : k % 7 = 3 ∨ k % 7 = 5 ∨ k % 7 = 6)
    (hB : 7 ∣ B) (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) : False :=
  BealMatveevBeal.BealGapK.no_sol_when_seven_dvd_B_residue_gapK h hk hB hkmod

theorem fourth_pow_mod3_uncond (a : ℕ) :
    a ^ 4 % 3 = 0 ∨ a ^ 4 % 3 = 1 :=
  BealMatveevBeal.BealGapK.fourth_pow_mod3 a

theorem fourth_pow_mod5_uncond (a : ℕ) :
    a ^ 4 % 5 = 0 ∨ a ^ 4 % 5 = 1 :=
  BealMatveevBeal.BealGapK.fourth_pow_mod5 a

theorem fourth_pow_mod7_uncond (a : ℕ) :
    a ^ 4 % 7 = 0 ∨ a ^ 4 % 7 = 1 ∨ a ^ 4 % 7 = 2 ∨ a ^ 4 % 7 = 4 :=
  BealMatveevBeal.BealGapK.fourth_pow_mod7 a

/-! ## Remaining coprime, axiom-relative Darmon–Merel -/

theorem gcd_A_B_eq_one_of_remaining {k A B : ℕ}
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13)
    (hforall : ∀ p : ℕ, Nat.Prime p → p ∣ k → ¬ p ∣ B) :
    Nat.gcd A B = 1 :=
  BealMatveevBeal.BealGapK.gcd_A_B_eq_one_of_remaining_gapK h hforall

theorem no_positive_coprime_of_axiom {k A B : ℕ}
    (h : A ^ 4 + B ^ 4 = (B + k) ^ 13) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcop : Nat.Coprime A B) : False :=
  BealMatveevBeal.BealGapK.no_positive_coprime_gapK_of_axiom h hA hB hcop

theorem no_positive_A4_B4_C13_coprime_of_axiom {A B C : ℕ}
    (h : A ^ 4 + B ^ 4 = C ^ 13) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcop : Nat.Coprime A B) : False := by
  have hDM := BealMatveevBeal.BealTrueV25.darmon_merel_4413_axiom
  have hA0 : A = 0 ∨ B = 0 := hDM A B C hcop h
  cases hA0 with
  | inl hA' => exact hA hA'
  | inr hB' => exact hB hB'

/-! ## Conditional size: `A,B ≤ B0` implies `C < 100` -/

theorem ten_pow_six_eq : (1000000 : ℕ) = 10 ^ 6 := rfl

theorem B0_pow_four_eq : B0_nat ^ 4 = 10 ^ 24 := by
  rw [B0_nat_eq, ten_pow_six_eq, ← pow_mul]

theorem hundred_eq_ten_pow_two : (100 : ℕ) = 10 ^ 2 := rfl

theorem hundred_pow_thirteen_eq : (100 : ℕ) ^ 13 = 10 ^ 26 := by
  rw [hundred_eq_ten_pow_two, ← pow_mul]

theorem two_mul_ten_pow_twenty_four_lt :
    2 * 10 ^ 24 < 10 ^ 26 := by
  have h100 : (10 : ℕ) ^ 26 = 100 * 10 ^ 24 := by
    rw [hundred_eq_ten_pow_two, ← pow_add]
  have hpos : 0 < (10 : ℕ) ^ 24 := Nat.pos_pow_of_pos 24 (by decide)
  have hlt : 2 * 10 ^ 24 < 100 * 10 ^ 24 :=
    (Nat.mul_lt_mul_right hpos).mpr (by decide : 2 < 100)
  rwa [← h100] at hlt

theorem two_mul_B0_pow_four_lt_hundred_pow_thirteen :
    2 * B0_nat ^ 4 < 100 ^ 13 := by
  rw [B0_pow_four_eq, hundred_pow_thirteen_eq]
  exact two_mul_ten_pow_twenty_four_lt

theorem sum_fourth_le_two_mul_max (A B : ℕ) :
    A ^ 4 + B ^ 4 ≤ 2 * (max A B) ^ 4 := by
  have hA : A ^ 4 ≤ (max A B) ^ 4 :=
    Nat.pow_le_pow_left (le_max_left A B) 4
  have hB : B ^ 4 ≤ (max A B) ^ 4 :=
    Nat.pow_le_pow_left (le_max_right A B) 4
  have := Nat.add_le_add hA hB
  simpa [two_mul] using this

theorem C_pow_le_two_mul_B0_of_le {A B C : ℕ}
    (h : A ^ 4 + B ^ 4 = C ^ 13)
    (hA : A ≤ B0_nat) (hB : B ≤ B0_nat) :
    C ^ 13 ≤ 2 * B0_nat ^ 4 := by
  have hmax : max A B ≤ B0_nat := max_le hA hB
  have hsum : A ^ 4 + B ^ 4 ≤ 2 * (max A B) ^ 4 :=
    sum_fourth_le_two_mul_max A B
  have hpow : 2 * (max A B) ^ 4 ≤ 2 * B0_nat ^ 4 :=
    Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hmax 4)
  have := le_trans hsum hpow
  rwa [h] at this

/-- Conditional on `A ≤ B0` and `B ≤ B0`, not an unconditional
    `C ≤ 73`. The `73` figure assumes both coordinates already
    sit under the Baker cutoff. -/
theorem C_lt_hundred_of_A_B_le_B0 {A B C : ℕ}
    (h : A ^ 4 + B ^ 4 = C ^ 13)
    (hA : A ≤ B0_nat) (hB : B ≤ B0_nat) :
    C < 100 := by
  have hle := C_pow_le_two_mul_B0_of_le h hA hB
  have hlt := two_mul_B0_pow_four_lt_hundred_pow_thirteen
  refine lt_of_not_ge ?_
  intro hC
  have hpow : (100 : ℕ) ^ 13 ≤ C ^ 13 :=
    Nat.pow_le_pow_left hC 13
  exact not_le_of_gt hlt (le_trans hpow hle)

/-- Positive `k` makes `C = B+k` grow with `B`. On `B ≥ B0`
    one already has `C ≥ 1000001`, so the `C ≤ 73` / `B ≤ 72`
    figures do not apply. -/
theorem C_ge_hundred_of_B_ge_B0 {k B : ℕ}
    (hk : 1 ≤ k) (hB : B0_nat ≤ B) :
    100 ≤ B + k := by
  have hsum : B0_nat + 1 ≤ B + k := Nat.add_le_add hB hk
  have hnum : 100 ≤ B0_nat + 1 := by
    rw [B0_nat_eq]
    decide
  exact le_trans hnum hsum

theorem not_C_le_seventy_three_of_B_ge_B0 {k B : ℕ}
    (hk : 1 ≤ k) (hB : B0_nat ≤ B) :
    ¬ B + k ≤ 73 := by
  intro h
  have hC : 1000001 ≤ B + k := by
    have : B0_nat + 1 ≤ B + k := Nat.add_le_add hB hk
    simpa [B0_nat_eq] using this
  exact (by decide : ¬ 1000001 ≤ 73) (le_trans hC h)

/-! ## Real-log / LLL still lose on gap form (`BealGapK`) -/

theorem hGen_exp_lt_ratio_gapK
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {k A B : ℕ} (hk : 1 ≤ k) (hsol : is_gapK_sol k A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  BealMatveevBeal.BealGapK.hGen_exp_lt_ratio_gapK hC1 hk hsol hB hB0

theorem C1_floor_hGen_loses_gapK {k A B : ℕ}
    (hk : 1 ≤ k) (hsol : is_gapK_sol k A B) (hB : 0 < B)
    (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  BealMatveevBeal.BealGapK.C1_floor_hGen_loses_gapK hk hsol hB hB0

theorem hLLL_method_fails_gapK {k : ℕ} (hk : 1 ≤ k) :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        is_gapK_sol k A B →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |BealMatveevBeal.BealGapK.floorFormThird_gapK k C A B| :=
  BealMatveevBeal.BealGapK.hLLL_method_fails_gapK hk

theorem no_uniform_c_cubic_in_N_gapK :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (BealMatveevBeal.MatveevThreeLogs.coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) :=
  BealMatveevBeal.BealGapK.no_uniform_c_cubic_in_N_gapK

theorem coeffCount3_zero_ten_ten_ten_gapK :
    BealMatveevBeal.MatveevThreeLogs.coeffCount3 0 10 10 10 = 1331 :=
  BealMatveevBeal.BealGapK.coeffCount3_zero_ten_ten_ten_gapK

/-! ## Combined unconditional no-go (no new axiom; p-adic stays `def Prop`) -/

/-- On a gap solution with `B ≥ B0` the real-log / LLL methods
    still lose, `C = B+k` is already `≥ 1000001` (so the
    conditional `C < 100` lemma does not apply), and the
    displayed p-adic / unrestricted Baker claims are false
    of that solution. Darmon–Merel stays the existing axiom. -/
theorem baker_bound_B0_1e6_unconditional_nogo {k A B : ℕ}
    (hk : 1 ≤ k) (hsol : is_gapK_sol k A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (∀ C : ℝ, 0 < C →
      ¬ ∃ r : ℝ,
        17 + C / (B0_nat : ℝ) < r ∧
          r ≤ |BealMatveevBeal.BealGapK.floorFormThird_gapK k C A B|) ∧
    B0_nat < A ∧
    100 ≤ B + k ∧
    ¬ B + k ≤ 73 ∧
    (hGen_padic → False) ∧
    (baker_bound_B0_1e6 → B ≤ B0_nat) ∧
    (baker_bound_gapK_unconditional_wins → B ≤ B0_nat) ∧
    ((∀ p : ℕ, Nat.Prime p → p ∣ k → ¬ p ∣ B) →
      darmon_merel_44_13_no_coprime → False) := by
  have hnogo :=
    BealMatveevBeal.BealGapK.baker_bound_gapK_unconditional_nogo
      hk hsol hB hB0
  obtain ⟨hlogs, hlll, hA, _, _, _, hDM⟩ := hnogo
  refine ⟨hlogs, hlll, hA, ?_, ?_, ?_, ?_, ?_, hDM⟩
  · exact C_ge_hundred_of_B_ge_B0 hk hB0
  · exact not_C_le_seventy_three_of_B_ge_B0 hk hB0
  · intro hp
    have hApos : 0 < A :=
      Nat.lt_trans hB (BealMatveevBeal.BealGapK.A_gt_B_of_sol hk hsol hB)
    exact hp A B (B + k) hsol hApos hB hB0
  · intro hb
    exact hb A B (B + k) hsol
  · intro hw
    exact hw k A B hsol

#check C1_floor_eq
#check B0_nat_eq
#check is_A4_B4_C13_sol
#check parity_odd_k_gapK
#check parity_even_k_gapK
#check gcd_dvd_k_gapK
#check p_dvd_k_and_B_forces_p_dvd_A_gapK
#check vp_one_descent_three_gapK
#check vp_one_descent_five_gapK
#check vp_one_descent_seven_gapK
#check vp_one_descent_eleven_gapK
#check vp_one_descent_thirteen_gapK
#check residue_kill_three_k_eq_two_gapK
#check residue_kill_five_k_eq_two_three_four_gapK
#check residue_kill_seven_k_eq_three_five_six_gapK
#check fourth_pow_mod3_uncond
#check fourth_pow_mod5_uncond
#check fourth_pow_mod7_uncond
#check gcd_A_B_eq_one_of_remaining
#check no_positive_coprime_of_axiom
#check no_positive_A4_B4_C13_coprime_of_axiom
#check C_lt_hundred_of_A_B_le_B0
#check C_ge_hundred_of_B_ge_B0
#check not_C_le_seventy_three_of_B_ge_B0
#check hGen_exp_lt_ratio_gapK
#check C1_floor_hGen_loses_gapK
#check hLLL_method_fails_gapK
#check no_uniform_c_cubic_in_N_gapK
#check baker_bound_B0_1e6
#check hGen_padic
#check hLLL_padic
#check baker_bound_B0_1e6_of_hGen_hLLL
#check baker_bound_gapK_unconditional_wins
#check beal_conjecture_4413
#check darmon_merel_44_13_no_coprime
#check fermat_last_theorem_thirteen
#check ribet_level_lowering_to_32
#check baker_bound_B0_1e6_unconditional_nogo
#print axioms C1_floor_eq
#print axioms B0_nat_eq
#print axioms parity_odd_k_gapK
#print axioms parity_even_k_gapK
#print axioms gcd_dvd_k_gapK
#print axioms p_dvd_k_and_B_forces_p_dvd_A_gapK
#print axioms C_lt_hundred_of_A_B_le_B0
#print axioms C_ge_hundred_of_B_ge_B0
#print axioms not_C_le_seventy_three_of_B_ge_B0
#print axioms hGen_exp_lt_ratio_gapK
#print axioms C1_floor_hGen_loses_gapK
#print axioms hLLL_method_fails_gapK
#print axioms baker_bound_B0_1e6_unconditional_nogo
#print axioms no_positive_A4_B4_C13_coprime_of_axiom

end BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6
