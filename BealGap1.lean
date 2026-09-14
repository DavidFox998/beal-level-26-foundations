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
import BealTrueV25
import BealCatalanZsig
import MatveevThreeLogs
import MatveevLLL

/-!
# Gap-1 `A⁴ + B⁴ = (B+1)¹³` (not a `B ≤ 10⁶` close)

Successor of `563e8e3` (`v24-v24x-final-unconditional-nogo`).
`C = B+1` so `gcd(B,C) = 1`. Any solution is coprime: a common
prime of `A` and `B` would divide `C`. Unlike gap-3, `3 ∣ B`
does **not** force a 3-adic contradiction (`C ≡ 1 mod 3`,
`A⁴ ≡ 1` is possible, so `3 ∤ A`). The remaining equation is
pure Darmon–Merel signature `(4,4,13)` for every `B > 0`.
`(A,B) = (1,0)` is a genuine solution with `B = 0 ≤ B0`.

`hGen_gap1` / `hLLL_gap1` stay `def Prop`. Every `C1 ≥ 1` loses
to `B⁴/A⁴` on `B ≥ B0`; no scaling yields a Baker–Davenport
witness above `17 + C/B0`. Named theorem `baker_bound_gap1`
stays a `def Prop`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

open Real

namespace BealMatveevBeal.BealGap1

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_logs :
    C1_floor = BealMatveevBeal.MatveevThreeLogs.C1_floor := rfl

theorem B0_nat_eq_logs :
    B0_nat = BealMatveevBeal.MatveevThreeLogs.B0_nat := rfl

/-! ## Gap-1 equation -/

def is_gap1_sol (A B : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = (B + 1) ^ 13

/-- Kernel Baker bound for gap-1. Stays a `def Prop`. -/
def baker_bound_gap1 : Prop :=
  ∀ A B : ℕ, is_gap1_sol A B → B ≤ B0_nat

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealTrueV25.darmon_merel_44_13_no_coprime

/-! ## `(1,0)` is a solution; `B = 0` is allowed by the bound -/

theorem gap1_one_zero : is_gap1_sol 1 0 := by
  unfold is_gap1_sol
  norm_num

theorem zero_le_B0 : 0 ≤ B0_nat := Nat.zero_le _

/-! ## `gcd(B, B+1) = 1` and coprimeness of solutions -/

theorem gcd_B_C_eq_one (B : ℕ) : Nat.gcd B (B + 1) = 1 := by
  rw [Nat.gcd_comm]
  simpa [Nat.gcd_one_left] using (Nat.gcd_add_self_left (1 : ℕ) B)

theorem gcd_A_B_eq_one_of_sol {A B : ℕ}
    (h : is_gap1_sol A B) : Nat.gcd A B = 1 := by
  set d := Nat.gcd A B
  have hdA : d ∣ A := Nat.gcd_dvd_left A B
  have hdB : d ∣ B := Nat.gcd_dvd_right A B
  have hdC13 : d ∣ (B + 1) ^ 13 := by
    have hA4 : d ∣ A ^ 4 := dvd_pow hdA (by decide)
    have hB4 : d ∣ B ^ 4 := dvd_pow hdB (by decide)
    have hsum : d ∣ A ^ 4 + B ^ 4 := Nat.dvd_add hA4 hB4
    simpa [is_gap1_sol] using (h ▸ hsum)
  have hcop : Nat.Coprime d (B + 1) := by
    have h1 : Nat.gcd d (B + 1) ∣ B :=
      dvd_trans (Nat.gcd_dvd_left d (B + 1)) hdB
    have h2 : Nat.gcd d (B + 1) ∣ (B + 1) := Nat.gcd_dvd_right d (B + 1)
    have hdiv : Nat.gcd d (B + 1) ∣ Nat.gcd B (B + 1) :=
      Nat.dvd_gcd h1 h2
    have hBC : Nat.gcd B (B + 1) = 1 := gcd_B_C_eq_one B
    rw [hBC] at hdiv
    exact Nat.eq_one_of_dvd_one hdiv
  have hcop13 : Nat.Coprime d ((B + 1) ^ 13) := hcop.pow_right 13
  have hd1 : d ∣ 1 := by
    have := Nat.dvd_gcd (dvd_refl d) hdC13
    rwa [show Nat.gcd d ((B + 1) ^ 13) = 1 from hcop13] at this
  exact Nat.eq_one_of_dvd_one hd1

theorem coprime_of_sol_gap1 {A B : ℕ}
    (h : is_gap1_sol A B) : Nat.Coprime A B :=
  gcd_A_B_eq_one_of_sol h

/-! ## Parity: `B` is even, `A` is odd -/

theorem B_even_of_sol_gap1 {A B : ℕ}
    (h : is_gap1_sol A B) : Even B := by
  by_contra hne
  have hBodd : Odd B := Nat.not_even_iff_odd.1 hne
  have hCeven : Even (B + 1) := hBodd.add_odd odd_one
  have h16C : 16 ∣ (B + 1) ^ 4 :=
    BealCatalanZsig.even_pow_four_dvd_sixteen hCeven
  have h16R : 16 ∣ (B + 1) ^ 13 :=
    dvd_trans h16C (pow_dvd_pow (B + 1) (by decide : 4 ≤ 13))
  have hR : (B + 1) ^ 13 % 16 = 0 := Nat.mod_eq_zero_of_dvd h16R
  have hB4 : B ^ 4 % 16 = 1 :=
    BealCatalanZsig.odd_pow_four_mod_sixteen hBodd
  by_cases hA : Even A
  · have hA4 : A ^ 4 % 16 = 0 :=
      Nat.mod_eq_zero_of_dvd
        (BealCatalanZsig.even_pow_four_dvd_sixteen hA)
    have hL : (A ^ 4 + B ^ 4) % 16 = 1 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + 1) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (1 : ℕ) ≠ 0) this
  · have hAodd : Odd A := Nat.not_even_iff_odd.1 hA
    have hA4 : A ^ 4 % 16 = 1 :=
      BealCatalanZsig.odd_pow_four_mod_sixteen hAodd
    have hL : (A ^ 4 + B ^ 4) % 16 = 2 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + 1) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (2 : ℕ) ≠ 0) this

theorem A_odd_of_sol_gap1 {A B : ℕ}
    (h : is_gap1_sol A B) : Odd A := by
  have hBeven := B_even_of_sol_gap1 h
  have hCodd : Odd (B + 1) := hBeven.add_odd odd_one
  have hC13 : Odd ((B + 1) ^ 13) := hCodd.pow
  have hB4 : Even (B ^ 4) := (Nat.even_pow' (by decide : 4 ≠ 0)).2 hBeven
  rw [← Nat.not_even_iff_odd]
  intro hAeven
  have hA4 : Even (A ^ 4) := (Nat.even_pow' (by decide : 4 ≠ 0)).2 hAeven
  have hL : Even (A ^ 4 + B ^ 4) := hA4.add hB4
  exact (Nat.not_even_iff_odd.2 (h ▸ hC13)) hL

/-! ## Size: `A > B` for `B > 0`; `A ≠ 0` on every solution -/

theorem two_mul_B_pow_four_lt_succ_pow {B : ℕ} (hB : 0 < B) :
    2 * B ^ 4 < (B + 1) ^ 13 := by
  have h2 : 2 ≤ B + 1 := Nat.succ_le_succ (Nat.succ_le_of_lt hB)
  have h2pow : 2 ≤ 2 ^ 9 := by decide
  have h29 : 2 ^ 9 ≤ (B + 1) ^ 9 := Nat.pow_le_pow_left h2 9
  have h2le : 2 ≤ (B + 1) ^ 9 := le_trans h2pow h29
  have hB4 : B ^ 4 < (B + 1) ^ 4 :=
    Nat.pow_lt_pow_left (Nat.lt_succ_self B) (by decide : 4 ≠ 0)
  have hle : 2 * B ^ 4 ≤ (B + 1) ^ 9 * B ^ 4 :=
    Nat.mul_le_mul_right (B ^ 4) h2le
  have hpos9 : 0 < (B + 1) ^ 9 := Nat.pos_pow_of_pos 9 (Nat.succ_pos B)
  have hlt : (B + 1) ^ 9 * B ^ 4 < (B + 1) ^ 9 * (B + 1) ^ 4 :=
    Nat.mul_lt_mul_of_pos_left hB4 hpos9
  have hsum : (B + 1) ^ 9 * (B + 1) ^ 4 = (B + 1) ^ 13 := by
    rw [← pow_add]
  exact lt_of_le_of_lt hle (hsum ▸ hlt)

theorem A_gt_B_of_sol {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 0 < B) : B < A := by
  by_contra hle
  have hAB : A ≤ B := Nat.not_lt.mp hle
  have hA4 : A ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hAB 4
  have hsum : A ^ 4 + B ^ 4 ≤ 2 * B ^ 4 := by
    have := Nat.add_le_add hA4 (le_refl (B ^ 4))
    simpa [two_mul] using this
  have hlt := two_mul_B_pow_four_lt_succ_pow hB
  have : A ^ 4 + B ^ 4 < (B + 1) ^ 13 := lt_of_le_of_lt hsum hlt
  exact (ne_of_lt this) h

theorem A_ne_zero_of_sol {A B : ℕ} (h : is_gap1_sol A B) : A ≠ 0 := by
  intro hA
  subst hA
  have heq : B ^ 4 = (B + 1) ^ 13 := by
    simpa [is_gap1_sol] using h
  by_cases hB : B = 0
  · subst hB
    exact (by decide : (0 : ℕ) ≠ 1) heq
  · have hpos : 0 < B := Nat.pos_of_ne_zero hB
    have hB4pos : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hpos
    have hlt1 : B ^ 4 < 2 * B ^ 4 := by
      have : 1 * B ^ 4 < 2 * B ^ 4 :=
        Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hB4pos
      simpa using this
    have hlt2 := two_mul_B_pow_four_lt_succ_pow hpos
    exact (ne_of_lt (lt_trans hlt1 hlt2)) heq

theorem A_gt_one_of_sol_pos {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 0 < B) : 1 < A :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) (A_gt_B_of_sol h hB)

/-! ## `mod 3` / `mod 5`: `3 ∣ B` is compatible, and forces `3 ∤ A` -/

theorem fourth_pow_mod3 (a : ℕ) : a ^ 4 % 3 = 0 ∨ a ^ 4 % 3 = 1 := by
  obtain h | h := BealCatalanZsig.pow_four_mod_three_of_mod (n := a)
  · exact Or.inl h.1
  · exact Or.inr h.1

theorem pow13_mod3_eq_self (c : ℕ) : c ^ 13 % 3 = c % 3 := by
  have hlt : c % 3 < 3 := Nat.mod_lt c (by decide)
  rw [Nat.pow_mod]
  interval_cases c % 3
  · norm_num
  · norm_num
  · norm_num

theorem A_pow_four_mod3_eq_one_of_three_dvd_B {A B : ℕ}
    (h : is_gap1_sol A B) (h3 : 3 ∣ B) : A ^ 4 % 3 = 1 := by
  have hB4 : B ^ 4 % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h3 (by decide))
  have hC : (B + 1) % 3 = 1 := by
    have : B % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    rw [Nat.add_mod, this]
  have hC13 : (B + 1) ^ 13 % 3 = 1 := by
    rw [pow13_mod3_eq_self, hC]
  have hsum : (A ^ 4 + B ^ 4) % 3 = (B + 1) ^ 13 % 3 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod3 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · exact h1

/-- Gap-1 opposite of gap-3: `3 ∣ B` forces `3 ∤ A` (coprime).
    Do **not** prove `no_sol_when_three_dvd_B` here — mod 3 does
    not kill `3 ∣ B`. -/
theorem not_three_dvd_A_of_three_dvd_B {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 3 ∣ B) : ¬ 3 ∣ A := by
  intro hA
  have : 3 ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
  rw [gcd_A_B_eq_one_of_sol h] at this
  exact (by decide : ¬ (3 ∣ 1)) this

theorem fourth_pow_mod5 (a : ℕ) : a ^ 4 % 5 = 0 ∨ a ^ 4 % 5 = 1 := by
  have hlt : a % 5 < 5 := Nat.mod_lt a (by decide)
  rw [Nat.pow_mod]
  interval_cases a % 5
  · exact Or.inl (by norm_num)
  · exact Or.inr (by norm_num)
  · exact Or.inr (by norm_num)
  · exact Or.inr (by norm_num)
  · exact Or.inr (by norm_num)

theorem pow13_mod5_eq_self (c : ℕ) : c ^ 13 % 5 = c % 5 := by
  have hlt : c % 5 < 5 := Nat.mod_lt c (by decide)
  rw [Nat.pow_mod]
  interval_cases c % 5
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-- If `5 ∣ B` then `A⁴ ≡ 1 mod 5`, so `5 ∤ A`. No contradiction. -/
theorem A_pow_four_mod5_eq_one_of_five_dvd_B {A B : ℕ}
    (h : is_gap1_sol A B) (h5 : 5 ∣ B) : A ^ 4 % 5 = 1 := by
  have hB4 : B ^ 4 % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h5 (by decide))
  have hC : (B + 1) % 5 = 1 := by
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [Nat.add_mod, this]
  have hC13 : (B + 1) ^ 13 % 5 = 1 := by
    rw [pow13_mod5_eq_self, hC]
  have hsum : (A ^ 4 + B ^ 4) % 5 = (B + 1) ^ 13 % 5 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod5 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · exact h1

theorem not_five_dvd_A_of_five_dvd_B {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 5 ∣ B) : ¬ 5 ∣ A := by
  intro hA
  have : 5 ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
  rw [gcd_A_B_eq_one_of_sol h] at this
  exact (by decide : ¬ (5 ∣ 1)) this

/-! ## Linear form `Λ = 4 log A − 13 log(B+1)` -/

noncomputable def Lambda_gap1 (A B : ℕ) : ℝ :=
  4 * log (A : ℝ) - 13 * log ((B + 1 : ℕ) : ℝ)

theorem A_pow_four_eq_sub {A B : ℕ} (h : is_gap1_sol A B) :
    A ^ 4 = (B + 1) ^ 13 - B ^ 4 := by
  rw [← h, add_comm, Nat.add_sub_cancel_left]

theorem A_pow_real_add {A B : ℕ} (h : is_gap1_sol A B) :
    (A : ℝ) ^ 4 + (B : ℝ) ^ 4 = ((B + 1 : ℕ) : ℝ) ^ 13 := by
  have h' : ((A ^ 4 + B ^ 4 : ℕ) : ℝ) = (((B + 1) ^ 13 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [Nat.cast_add, Nat.cast_pow] using h'

theorem A_pow_pos_of_sol {A B : ℕ} (h : is_gap1_sol A B) :
    (0 : ℝ) < (A : ℝ) ^ 4 := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  exact pow_pos hApos 4

theorem Lambda_gap1_eq_log_div {A B : ℕ}
    (h : is_gap1_sol A B) :
    Lambda_gap1 A B =
      log ((A : ℝ) ^ 4 / ((B + 1 : ℕ) : ℝ) ^ 13) := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hCpos : (0 : ℝ) < ((B + 1 : ℕ) : ℝ) := by
    have : 0 < B + 1 := Nat.succ_pos B
    exact_mod_cast this
  unfold Lambda_gap1
  have h4 : (4 : ℝ) * log (A : ℝ) = log ((A : ℝ) ^ 4) :=
    (Real.log_pow (A : ℝ) 4).symm
  have h13 : (13 : ℝ) * log ((B + 1 : ℕ) : ℝ) =
      log (((B + 1 : ℕ) : ℝ) ^ 13) :=
    (Real.log_pow ((B + 1 : ℕ) : ℝ) 13).symm
  rw [h4, h13, Real.log_div (pow_pos hApos 4).ne' (pow_pos hCpos 13).ne']

theorem abs_Lambda_gap1_eq_log_one_plus {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 0 < B) :
    |Lambda_gap1 A B| = log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hu : (0 : ℝ) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    div_pos (pow_pos hBpos 4) hA4pos
  have hsum := A_pow_real_add h
  have hratio :
      (A : ℝ) ^ 4 / ((B + 1 : ℕ) : ℝ) ^ 13 =
        1 / (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    have hne : (A : ℝ) ^ 4 ≠ 0 := hA4pos.ne'
    have hden :
        (1 : ℝ) + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 =
          ((A : ℝ) ^ 4 + (B : ℝ) ^ 4) / (A : ℝ) ^ 4 := by
      field_simp [hne]
    rw [hden, one_div_div, hsum]
  have hΛ := Lambda_gap1_eq_log_div h
  have h1u : (0 : ℝ) < 1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    add_pos_of_nonneg_of_pos zero_le_one hu
  have hlog :
      Lambda_gap1 A B = -log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    rw [hΛ, hratio, Real.log_div one_ne_zero h1u.ne', log_one, zero_sub]
  rw [hlog, abs_neg, abs_of_nonneg (log_nonneg (le_of_lt (lt_add_of_pos_right 1 hu)))]

theorem abs_Lambda_gap1_le_ratio {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 0 < B) :
    |Lambda_gap1 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hu : (0 : ℝ) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    div_pos (pow_pos hBpos 4) hA4pos
  have hx : (0 : ℝ) < 1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    add_pos_of_nonneg_of_pos zero_le_one hu
  have hlog := Real.log_le_sub_one_of_pos hx
  have : log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ≤
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
    simpa using hlog
  rwa [abs_Lambda_gap1_eq_log_one_plus h hB]

theorem B_pow_five_add_B_pow_four_lt_succ_pow {B : ℕ} (_hB : 0 < B) :
    (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 1 : ℕ) : ℝ) ^ 13 := by
  have hx : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : ((B + 1 : ℕ) : ℝ) = (B : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have h5 : (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 1 : ℕ) : ℝ) ^ 5 := by
    rw [hC]
    have hexp : ((B : ℝ) + 1) ^ 5 =
        (B : ℝ) ^ 5 + 5 * (B : ℝ) ^ 4 + 10 * (B : ℝ) ^ 3 +
          10 * (B : ℝ) ^ 2 + 5 * (B : ℝ) + 1 := by
      ring
    have h3 : (0 : ℝ) ≤ (B : ℝ) ^ 3 := pow_nonneg hx 3
    have h2 : (0 : ℝ) ≤ (B : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hexp, h3, h2, hx]
  have hC1 : (1 : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by
    have : 1 ≤ B + 1 := Nat.succ_le_succ (Nat.zero_le B)
    exact_mod_cast this
  have h513 : ((B + 1 : ℕ) : ℝ) ^ 5 ≤ ((B + 1 : ℕ) : ℝ) ^ 13 :=
    pow_le_pow_right hC1 (by decide : (5 : ℕ) ≤ 13)
  exact lt_of_lt_of_le h5 h513

theorem A_pow_gt_B_pow_five {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 5 < (A : ℝ) ^ 4 := by
  have hA4 : (A : ℝ) ^ 4 =
      ((B + 1 : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 := by
    linarith [A_pow_real_add h]
  have hsum := B_pow_five_add_B_pow_four_lt_succ_pow hB
  linarith [hA4, hsum]

theorem ratio_lt_inv_B {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 4 / (A : ℝ) ^ 4 < 1 / (B : ℝ) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hgt := A_pow_gt_B_pow_five h hB
  have : (B : ℝ) ^ 4 * (B : ℝ) < (A : ℝ) ^ 4 := by
    have : (B : ℝ) ^ 5 = (B : ℝ) ^ 4 * (B : ℝ) := by ring
    rwa [this] at hgt
  rw [div_lt_div_iff hA4pos hBpos, one_mul]
  exact this

theorem abs_Lambda_gap1_lt_inv_B {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 0 < B) :
    |Lambda_gap1 A B| < 1 / (B : ℝ) :=
  lt_of_le_of_lt (abs_Lambda_gap1_le_ratio h hB) (ratio_lt_inv_B h hB)

theorem A_pow_lt_C_pow {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 0 < B) :
    (A : ℝ) ^ 4 < ((B + 1 : ℕ) : ℝ) ^ 13 := by
  have hB4 : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hB
  have hlt : A ^ 4 < (B + 1) ^ 13 :=
    calc
      A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
      _ = (B + 1) ^ 13 := h
  exact_mod_cast hlt

/-! ## Log-method no-go (`C1 ≥ 1` loses to `B⁴/A⁴`) -/

theorem logA_gt_thirteen_of_B_ge_B0 {A B : ℕ}
    (h : is_gap1_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (13 : ℝ) < log (A : ℝ) := by
  have hAgt := A_gt_B_of_sol h hB
  have hA : (B0_nat : ℝ) < (A : ℝ) := by
    have : B0_nat < A := Nat.lt_of_le_of_lt hB0 hAgt
    exact_mod_cast this
  have hB0pos : (1 : ℝ) < (B0_nat : ℝ) := by
    rw [B0_nat_eq]
    norm_num
  have hlog := Real.log_lt_log (lt_trans (by norm_num) hB0pos) hA
  have hlogB0 : (13 : ℝ) < log (B0_nat : ℝ) := by
    simpa [B0_nat_eq_logs] using
      BealMatveevBeal.MatveevThreeLogs.log_B0_gt_thirteen
  exact lt_trans hlogB0 hlog

/-- `exp(−C1 log A log(B+1)) < B⁴/A⁴` for every `C1 ≥ 1` on
    a gap-1 solution with `B ≥ B0`. Same cutoff as `62383af`:
    `C1 < 1` would be needed. -/
theorem hGen_exp_lt_ratio_gap1
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {A B : ℕ} (hsol : is_gap1_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + 1 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  set a : ℝ := log (A : ℝ)
  set c : ℝ := log ((B + 1 : ℕ) : ℝ)
  set C : ℝ := ((B + 1 : ℕ) : ℝ)
  have hAgt1 : 1 < A := A_gt_one_of_sol_pos hsol hB
  have hCgt1 : 1 < B + 1 := Nat.succ_lt_succ hB
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (0 : ℕ) < A := lt_trans Nat.zero_lt_one hAgt1
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C := by
    have : 0 < B + 1 := Nat.succ_pos B
    have : (0 : ℝ) < ((B + 1 : ℕ) : ℝ) := by exact_mod_cast this
    simpa [C] using this
  have hCgt : (1 : ℝ) < C := by
    have : (1 : ℝ) < ((B + 1 : ℕ) : ℝ) := by exact_mod_cast hCgt1
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
        have h16n : (16 : ℕ) ≤ B ^ 4 := by simpa using h16
        exact_mod_cast h16n
      linarith
    exact (div_lt_div_right hC13).mpr hB4
  have hratio : (B : ℝ) ^ 4 / C ^ 13 < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
    have hA4pos : (0 : ℝ) < (A : ℝ) ^ 4 := pow_pos hApos 4
    have hB4pos : (0 : ℝ) < (B : ℝ) ^ 4 := by
      have : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
      exact pow_pos this 4
    have hlt := A_pow_lt_C_pow hsol hB
    exact div_lt_div_of_pos_left hB4pos hA4pos hlt
  have hchain : exp (-C1 * a * c) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    lt_trans (hexp.trans_eq h13) (lt_trans hinv hratio)
  simpa [a, c] using hchain

theorem C1_floor_hGen_loses_gap1 {A B : ℕ}
    (hsol : is_gap1_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + 1 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio_gap1
    (le_of_lt (by
      simpa [C1_floor_eq_logs] using
        BealMatveevBeal.MatveevThreeLogs.C1_floor_gt_one))
    hsol hB hB0

/-! ## Floor form / LLL no-go (`B+1`, not `B+3`) -/

noncomputable def floorFormThird_gap1 (C : ℝ) (A B : ℕ) : ℝ :=
  (4 : ℝ) * ⌊C * log (A : ℝ)⌋ - 13 * ⌊C * log ((B + 1 : ℕ) : ℝ)⌋

/-- `|4⌊C log A⌋ − 13⌊C log(B+1)⌋ − C Λ| < 17` for every real `C`. -/
theorem floor_form_approx_of_C_gap1 (C : ℝ) (A B : ℕ) :
    |floorFormThird_gap1 C A B - C * Lambda_gap1 A B| < 17 := by
  set a : ℝ := C * log (A : ℝ)
  set cval : ℝ := C * log ((B + 1 : ℕ) : ℝ)
  have hΛ : C * Lambda_gap1 A B = 4 * a - 13 * cval := by
    simp only [Lambda_gap1, a, cval]
    ring
  have hft : floorFormThird_gap1 C A B = (4 : ℝ) * ⌊a⌋ - 13 * ⌊cval⌋ := rfl
  have hform :
      floorFormThird_gap1 C A B - C * Lambda_gap1 A B =
        4 * (⌊a⌋ - a) - 13 * (⌊cval⌋ - cval) := by
    rw [hft, hΛ]
    ring
  have ha : |a - ⌊a⌋| < 1 := BealMatveevBeal.MatveevLLL.abs_sub_int_floor a
  have hc : |cval - ⌊cval⌋| < 1 :=
    BealMatveevBeal.MatveevLLL.abs_sub_int_floor cval
  have hbound :
      |4 * (⌊a⌋ - a) - 13 * (⌊cval⌋ - cval)| < 17 := by
    have h4 : |(4 : ℝ) * (⌊a⌋ - a)| < 4 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 4)]
      have : |⌊a⌋ - a| = |a - ⌊a⌋| := abs_sub_comm _ _
      rw [this]
      nlinarith [ha]
    have h13 : |(13 : ℝ) * (⌊cval⌋ - cval)| < 13 := by
      rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 13)]
      have : |⌊cval⌋ - cval| = |cval - ⌊cval⌋| := abs_sub_comm _ _
      rw [this]
      nlinarith [hc]
    have htri : |4 * (⌊a⌋ - a) - 13 * (⌊cval⌋ - cval)| ≤
        |4 * (⌊a⌋ - a)| + |13 * (⌊cval⌋ - cval)| := by
      simpa [sub_eq_add_neg, abs_neg] using
        abs_add ((4 : ℝ) * (⌊a⌋ - a)) (-((13 : ℝ) * (⌊cval⌋ - cval)))
    linarith [htri, h4, h13]
  rwa [hform]

theorem floor_form_third_abs_lt_gap1 {C : ℝ} (hC : 0 < C) (A B : ℕ) :
    |floorFormThird_gap1 C A B| < 17 + C * |Lambda_gap1 A B| := by
  have happ := floor_form_approx_of_C_gap1 C A B
  have hmul : |C * Lambda_gap1 A B| = C * |Lambda_gap1 A B| := by
    rw [abs_mul, abs_of_pos hC]
  have := abs_sub_abs_le_abs_sub
    (floorFormThird_gap1 C A B) (C * Lambda_gap1 A B)
  linarith [happ, this, hmul]

/-- No scaling `C > 0` yields a Baker–Davenport witness
    `r > 17 + C/B0` on a gap-1 solution with `B ≥ B0`. -/
theorem hLLL_method_fails_gap1 :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        is_gap1_sol A B →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |floorFormThird_gap1 C A B| := by
  intro C hC A B hsol hB hB0
  rintro ⟨r, hgt, hle⟩
  have htri := floor_form_third_abs_lt_gap1 hC A B
  have hLam := abs_Lambda_gap1_lt_inv_B hsol hB
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hBle : (B0_nat : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hB0
  have hCΛ : C * |Lambda_gap1 A B| < C / (B0_nat : ℝ) := by
    have hmid : C * |Lambda_gap1 A B| < C * (1 / (B : ℝ)) :=
      mul_lt_mul_of_pos_left hLam hC
    have hrew : C * (1 / (B : ℝ)) = C / (B : ℝ) := mul_one_div _ _
    have hCB : C / (B : ℝ) ≤ C / (B0_nat : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hC) hB0pos hBle
    linarith [hmid, hrew, hCB]
  have hthird : |floorFormThird_gap1 C A B| < 17 + C / (B0_nat : ℝ) := by
    linarith [htri, hCΛ]
  linarith [hgt, hle, hthird]

theorem no_uniform_c_cubic_in_N_gap1 :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (BealMatveevBeal.MatveevThreeLogs.coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) :=
  BealMatveevBeal.MatveevThreeLogs.no_uniform_c_cubic_in_N

theorem coeffCount3_zero_ten_ten_ten_gap1 :
    BealMatveevBeal.MatveevThreeLogs.coeffCount3 0 10 10 10 = 1331 :=
  BealMatveevBeal.MatveevThreeLogs.coeffCount3_zero_ten_ten_ten

theorem no_uniform_c_easy_half_gap1 :
    (1 / 2 : ℝ) * 1 * 1 < 242 := by
  norm_num

/-! ## `hGen_gap1` / `hLLL_gap1` stay `def Prop` -/

/-- Matveev 2000 Theorem 1.4, n=2, displayed `C1_floor` exponential
    on a gap-1 solution. Not in Mathlib 4.12. Instantiating it at
    `B ≥ B0` does not beat `B⁴/A⁴`. -/
def hGen_gap1 : Prop :=
  ∀ A B : ℕ,
    is_gap1_sol A B →
      0 < B →
        |Lambda_gap1 A B| >
          exp (-(C1_floor : ℝ) * log (A : ℝ) *
            log ((B + 1 : ℕ) : ℝ))

/-- Bugeaud / LLL close for gap-1: ratio upper bound ⇒ `B ≤ B0`.
    The displayed lattice does not inhabit it. -/
def hLLL_gap1 : Prop :=
  (∀ A B : ℕ, is_gap1_sol A B → 0 < B →
      |Lambda_gap1 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4) →
    baker_bound_gap1

def baker_bound_gap1_of_hGen_hLLL : Prop :=
  hGen_gap1 → hLLL_gap1 → baker_bound_gap1

/-! ## Combined unconditional no-go (no Darmon–Merel axiom) -/

/-- Log and LLL methods lose on `B ≥ B0`. Remaining solutions are
    coprime with `A > B0`, `B` even, `A` odd. `3 ∣ B` is compatible
    and forces `3 ∤ A`. Darmon–Merel `(4,4,13)` would be refuted by
    any such solution. `baker_bound_gap1` stays uninhabited as a
    named theorem. -/
theorem baker_bound_gap1_unconditional_nogo {A B : ℕ}
    (hsol : is_gap1_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + 1 : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (∀ C : ℝ, 0 < C →
      ¬ ∃ r : ℝ,
        17 + C / (B0_nat : ℝ) < r ∧
          r ≤ |floorFormThird_gap1 C A B|) ∧
    Nat.Coprime A B ∧
    B0_nat < A ∧
    Even B ∧
    Odd A ∧
    (3 ∣ B → ¬ 3 ∣ A) ∧
    (darmon_merel_44_13_no_coprime → False) := by
  refine ⟨?_, ?_, coprime_of_sol_gap1 hsol, ?_,
    B_even_of_sol_gap1 hsol, A_odd_of_sol_gap1 hsol, ?_, ?_⟩
  · intro C1 hC1
    exact hGen_exp_lt_ratio_gap1 hC1 hsol hB hB0
  · intro C hC
    exact hLLL_method_fails_gap1 C hC A B hsol hB hB0
  · exact Nat.lt_of_le_of_lt hB0 (A_gt_B_of_sol hsol hB)
  · intro h3
    exact not_three_dvd_A_of_three_dvd_B hsol h3
  · intro hDM
    have hA0 : A = 0 ∨ B = 0 :=
      hDM A B (B + 1) (coprime_of_sol_gap1 hsol) hsol
    cases hA0 with
    | inl hA => exact A_ne_zero_of_sol hsol hA
    | inr hB0' => exact (ne_of_gt hB) hB0'

/-! ## Axiom-relative close (reuses `BealTrueV25`, no new axiom) -/

/-- Positive-`B` gap-1 solutions are impossible relative to
    `darmon_merel_4413_axiom`. `(1,0)` remains a solution. -/
theorem no_pos_gap1_of_axiom {A B : ℕ}
    (hsol : is_gap1_sol A B) (hB : 0 < B) : False := by
  have hDM := BealMatveevBeal.BealTrueV25.darmon_merel_4413_axiom
  have hA0 : A = 0 ∨ B = 0 :=
    hDM A B (B + 1) (coprime_of_sol_gap1 hsol) hsol
  cases hA0 with
  | inl hA => exact A_ne_zero_of_sol hsol hA
  | inr hB0 => exact (ne_of_gt hB) hB0

/-- Vacuous `B ≤ B0` for every gap-1 solution, relative to the
    existing Darmon–Merel axiom. Not named `baker_bound_gap1`. -/
theorem baker_bound_gap1_true {A B : ℕ}
    (hsol : is_gap1_sol A B) : B ≤ B0_nat := by
  by_cases hB : B = 0
  · simp [hB]
  · exact (no_pos_gap1_of_axiom hsol (Nat.pos_of_ne_zero hB)).elim

#check C1_floor_eq
#check B0_nat_eq
#check gap1_one_zero
#check gcd_B_C_eq_one
#check gcd_A_B_eq_one_of_sol
#check coprime_of_sol_gap1
#check B_even_of_sol_gap1
#check A_odd_of_sol_gap1
#check A_gt_B_of_sol
#check not_three_dvd_A_of_three_dvd_B
#check A_pow_four_mod3_eq_one_of_three_dvd_B
#check A_pow_four_mod5_eq_one_of_five_dvd_B
#check hGen_exp_lt_ratio_gap1
#check C1_floor_hGen_loses_gap1
#check floor_form_approx_of_C_gap1
#check hLLL_method_fails_gap1
#check no_uniform_c_cubic_in_N_gap1
#check no_uniform_c_easy_half_gap1
#check hGen_gap1
#check hLLL_gap1
#check baker_bound_gap1_of_hGen_hLLL
#check baker_bound_gap1_unconditional_nogo
#check baker_bound_gap1
#check no_pos_gap1_of_axiom
#check baker_bound_gap1_true
#print axioms gcd_A_B_eq_one_of_sol
#print axioms B_even_of_sol_gap1
#print axioms not_three_dvd_A_of_three_dvd_B
#print axioms hGen_exp_lt_ratio_gap1
#print axioms C1_floor_hGen_loses_gap1
#print axioms hLLL_method_fails_gap1
#print axioms baker_bound_gap1_unconditional_nogo
#print axioms no_pos_gap1_of_axiom
#print axioms baker_bound_gap1_true

end BealMatveevBeal.BealGap1
