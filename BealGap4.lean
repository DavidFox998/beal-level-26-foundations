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
import BealGap2

/-!
# Gap-4 `A⁴ + B⁴ = (B+4)¹³` (not a `B ≤ 10⁶` close)

Successor of `7a1c53b` (`v24-v24x-final-gap2-nogo`).
`C = B+4` so `gcd(B,C) ∣ 4`. Like gap-2, `B` even is impossible:
six divisions by `2` leave `A₆⁴ + B₆⁴ = 4 (16 B₆ + 1)¹³`, and
`4 · odd ≡ 4` or `12` mod 16, never a sum of fourth powers
`{0,1,2}`. So `B` is odd and `A` is even. `(1,0)` is **not**
a solution (`1 ≠ 4¹³`). Unlike gap-2 / gap-3, `3 ∣ B` does
**not** kill: `C ≡ 1 mod 3`, `A⁴ ≡ 1` is possible (same as
gap-1 `271f03e`). New for gap-4: `5 ∣ B` **does** kill,
`C ≡ 4 mod 5`, `C¹³ ≡ 4`, while `A⁴ ∈ {0,1}`. Remaining
solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 4`, but `B` is odd)
and pure Darmon–Merel signature `(4,4,13)`.

`hGen_gap4` / `hLLL_gap4` stay `def Prop`. Every `C1 ≥ 1` loses
to `B⁴/A⁴` on `B ≥ B0`; no scaling yields a Baker–Davenport
witness above `17 + C/B0`. Named theorem `baker_bound_gap4`
stays a `def Prop`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

set_option maxHeartbeats 800000

open Real

namespace BealMatveevBeal.BealGap4

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_logs :
    C1_floor = BealMatveevBeal.MatveevThreeLogs.C1_floor := rfl

theorem B0_nat_eq_logs :
    B0_nat = BealMatveevBeal.MatveevThreeLogs.B0_nat := rfl

/-! ## Gap-4 equation -/

def is_gap4_sol (A B : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = (B + 4) ^ 13

/-- Kernel Baker bound for gap-4. Stays a `def Prop`. -/
def baker_bound_gap4 : Prop :=
  ∀ A B : ℕ, is_gap4_sol A B → B ≤ B0_nat

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealTrueV25.darmon_merel_44_13_no_coprime

/-! ## `(1,0)` is not a solution -/

theorem not_gap4_one_zero : ¬ is_gap4_sol 1 0 := by
  unfold is_gap4_sol
  decide

/-! ## `gcd(B, B+4) = gcd(B, 4)` divides `4` -/

theorem gcd_B_C_eq_gcd_four (B : ℕ) : Nat.gcd B (B + 4) = Nat.gcd B 4 := by
  rw [Nat.gcd_comm B (B + 4), Nat.add_comm B 4]
  exact (Nat.gcd_add_self_left (4 : ℕ) B).trans (Nat.gcd_comm 4 B)

theorem gcd_B_C_dvd_four (B : ℕ) : Nat.gcd B (B + 4) ∣ 4 := by
  rw [gcd_B_C_eq_gcd_four]
  exact Nat.gcd_dvd_right B 4

theorem gcd_B_C_dvd_four_gap4 (B : ℕ) : Nat.gcd B (B + 4) ∣ 4 :=
  gcd_B_C_dvd_four B

/-! ## `4 · odd ≡ 4` or `12` mod 16 -/

theorem four_mul_odd_mod16 {n : ℕ} (h : Odd n) :
    (4 * n) % 16 = 4 ∨ (4 * n) % 16 = 12 := by
  have hodd : n % 2 = 1 := Nat.odd_iff.1 h
  have h2 : (n % 16) % 2 = 1 := by
    rwa [Nat.mod_mod_of_dvd n (by decide : 2 ∣ 16)]
  have hn : n % 16 = 1 ∨ n % 16 = 3 ∨ n % 16 = 5 ∨ n % 16 = 7 ∨
      n % 16 = 9 ∨ n % 16 = 11 ∨ n % 16 = 13 ∨ n % 16 = 15 := by
    have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
    interval_cases n % 16 <;> simp at h2 ⊢
  have hmul : (4 * n) % 16 = (4 * (n % 16)) % 16 := by
    rw [Nat.mul_mod, Nat.mod_eq_of_lt (by decide : 4 < 16)]
  rcases hn with h1 | h3 | h5 | h7 | h9 | h11 | h13n | h15
  · rw [hmul, h1]; exact Or.inl (by norm_num)
  · rw [hmul, h3]; exact Or.inr (by norm_num)
  · rw [hmul, h5]; exact Or.inl (by norm_num)
  · rw [hmul, h7]; exact Or.inr (by norm_num)
  · rw [hmul, h9]; exact Or.inl (by norm_num)
  · rw [hmul, h11]; exact Or.inr (by norm_num)
  · rw [hmul, h13n]; exact Or.inl (by norm_num)
  · rw [hmul, h15]; exact Or.inr (by norm_num)

theorem odd_of_sixteen_mul_add_one (n : ℕ) : Odd (16 * n + 1) := by
  rw [Nat.odd_iff, Nat.add_mod, Nat.mul_mod]
  norm_num

theorem not_sum_fourth_eq_four_mul_odd {X Y n : ℕ} (hn : Odd n)
    (h : X ^ 4 + Y ^ 4 = 4 * n) : False := by
  have hmod : (X ^ 4 + Y ^ 4) % 16 = (4 * n) % 16 := by rw [h]
  obtain h0 | h1 | h2 := BealGap2.sum_fourth_mod16 X Y
  · obtain hr | hr := four_mul_odd_mod16 hn
    · rw [h0, hr] at hmod; exact (by decide : (0 : ℕ) ≠ 4) hmod
    · rw [h0, hr] at hmod; exact (by decide : (0 : ℕ) ≠ 12) hmod
  · obtain hr | hr := four_mul_odd_mod16 hn
    · rw [h1, hr] at hmod; exact (by decide : (1 : ℕ) ≠ 4) hmod
    · rw [h1, hr] at hmod; exact (by decide : (1 : ℕ) ≠ 12) hmod
  · obtain hr | hr := four_mul_odd_mod16 hn
    · rw [h2, hr] at hmod; exact (by decide : (2 : ℕ) ≠ 4) hmod
    · rw [h2, hr] at hmod; exact (by decide : (2 : ℕ) ≠ 12) hmod

/-! ## Parity: `A` is even. `B` even is impossible, so `B` is odd. -/

theorem A_even_of_sol_gap4 {A B : ℕ} (h : is_gap4_sol A B) : Even A := by
  by_contra hne
  have hAodd : Odd A := Nat.not_even_iff_odd.1 hne
  have hA4 : A ^ 4 % 16 = 1 :=
    BealCatalanZsig.odd_pow_four_mod_sixteen hAodd
  by_cases hBeven : Even B
  · have hCeven : Even (B + 4) := hBeven.add (⟨2, rfl⟩ : Even 4)
    have h16C : 16 ∣ (B + 4) ^ 4 :=
      BealCatalanZsig.even_pow_four_dvd_sixteen hCeven
    have h16R : 16 ∣ (B + 4) ^ 13 :=
      dvd_trans h16C (pow_dvd_pow (B + 4) (by decide : 4 ≤ 13))
    have hR : (B + 4) ^ 13 % 16 = 0 := Nat.mod_eq_zero_of_dvd h16R
    have hB4 : B ^ 4 % 16 = 0 :=
      Nat.mod_eq_zero_of_dvd (BealCatalanZsig.even_pow_four_dvd_sixteen hBeven)
    have hL : (A ^ 4 + B ^ 4) % 16 = 1 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + 4) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (1 : ℕ) ≠ 0) this
  · have hBodd : Odd B := Nat.not_even_iff_odd.1 hBeven
    have hCodd : Odd (B + 4) := hBodd.add_even (⟨2, rfl⟩ : Even 4)
    have hB4 : B ^ 4 % 16 = 1 :=
      BealCatalanZsig.odd_pow_four_mod_sixteen hBodd
    have hL : (A ^ 4 + B ^ 4) % 16 = 2 := by
      rw [Nat.add_mod, hA4, hB4]
    have hR : (B + 4) ^ 13 % 16 = (B + 4) % 16 :=
      BealGap2.odd_pow_thirteen_mod_sixteen hCodd
    have : (A ^ 4 + B ^ 4) % 16 = (B + 4) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    have hC2 : (B + 4) % 2 = 0 := by
      have h16 : (B + 4) % 16 = 2 := this.symm
      have : ((B + 4) % 16) % 2 = 0 := by rw [h16]
      rwa [Nat.mod_mod_of_dvd (B + 4) (by decide : 2 ∣ 16)] at this
    exact Nat.not_even_iff_odd.2 hCodd (Nat.even_iff.2 hC2)

/-- Even `B` is impossible: six divisions by `2` leave
    `A₆⁴ + B₆⁴ = 4 (16 B₆ + 1)¹³`, whose residue is `4` or `12`
    mod 16 and cannot match a sum of fourth powers. Do **not**
    prove `B_even_of_sol_gap4`. -/
theorem no_sol_when_even_B {A B : ℕ}
    (h : is_gap4_sol A B) (hBeven : Even B) : False := by
  have hAeven := A_even_of_sol_gap4 h
  obtain ⟨A1, hA'⟩ := hAeven
  obtain ⟨B1, hB'⟩ := hBeven
  have hA : A = 2 * A1 := by rw [hA', two_mul]
  have hB : B = 2 * B1 := by rw [hB', two_mul]
  have hC : B + 4 = 2 * (B1 + 2) := by
    rw [hB, mul_add]
  have hsol1 : (2 * A1) ^ 4 + (2 * B1) ^ 4 = (2 * (B1 + 2)) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 16 * (A1 ^ 4 + B1 ^ 4) = 2 ^ 13 * (B1 + 2) ^ 13 := by
    rw [← BealGap2.sum_fourth_of_mul_two, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 2 ^ 9 * (B1 + 2) ^ 13 := by
    have hpow : (2 : ℕ) ^ 13 = 16 * 2 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq1, hpow, mul_assoc]
  have h16 : (A1 ^ 4 + B1 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 9 * (B1 + 2) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 9) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1e, hB1e⟩ := BealGap2.both_even_of_sum_fourth_mod16_zero h16
  obtain ⟨A2, hA2'⟩ := hA1e
  obtain ⟨B2, hB2'⟩ := hB1e
  have hA2 : A1 = 2 * A2 := by rw [hA2', two_mul]
  have hB2 : B1 = 2 * B2 := by rw [hB2', two_mul]
  have hB21 : B1 + 2 = 2 * (B2 + 1) := by
    rw [hB2, mul_add, mul_one]
  have heq2src : (2 * A2) ^ 4 + (2 * B2) ^ 4 =
      2 ^ 9 * (2 * (B2 + 1)) ^ 13 := by
    rw [← hA2, ← hB2, ← hB21]; exact h9
  have heq2 : 16 * (A2 ^ 4 + B2 ^ 4) =
      2 ^ 9 * (2 * (B2 + 1)) ^ 13 := by
    rw [← BealGap2.sum_fourth_of_mul_two]; exact heq2src
  have h18 : A2 ^ 4 + B2 ^ 4 = 2 ^ 18 * (B2 + 1) ^ 13 := by
    have hr : (2 * (B2 + 1)) ^ 13 = 2 ^ 13 * (B2 + 1) ^ 13 :=
      mul_pow _ _ 13
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq2, hr]
    have hpow : (2 : ℕ) ^ 9 * 2 ^ 13 = 16 * 2 ^ 18 := by norm_num
    rw [← mul_assoc, hpow, mul_assoc]
  have h16₂ : (A2 ^ 4 + B2 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 18 * (B2 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 18) _
    exact Nat.mod_eq_zero_of_dvd (h18 ▸ this)
  obtain ⟨hA2e, hB2e⟩ := BealGap2.both_even_of_sum_fourth_mod16_zero h16₂
  obtain ⟨A3, hA3'⟩ := hA2e
  obtain ⟨B3, hB3'⟩ := hB2e
  have hA3 : A2 = 2 * A3 := by rw [hA3', two_mul]
  have hB3 : B2 = 2 * B3 := by rw [hB3', two_mul]
  have heq3src : (2 * A3) ^ 4 + (2 * B3) ^ 4 =
      2 ^ 18 * (2 * B3 + 1) ^ 13 := by
    rw [← hA3, ← hB3]
    exact h18
  have heq3 : 16 * (A3 ^ 4 + B3 ^ 4) = 2 ^ 18 * (2 * B3 + 1) ^ 13 := by
    rw [← BealGap2.sum_fourth_of_mul_two]; exact heq3src
  have h14 : A3 ^ 4 + B3 ^ 4 = 2 ^ 14 * (2 * B3 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 18 = 16 * 2 ^ 14 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq3, hpow, mul_assoc]
  have h16₃ : (A3 ^ 4 + B3 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 14 * (2 * B3 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 14) _
    exact Nat.mod_eq_zero_of_dvd (h14 ▸ this)
  obtain ⟨hA3e, hB3e⟩ := BealGap2.both_even_of_sum_fourth_mod16_zero h16₃
  obtain ⟨A4, hA4'⟩ := hA3e
  obtain ⟨B4, hB4'⟩ := hB3e
  have hA4 : A3 = 2 * A4 := by rw [hA4', two_mul]
  have hB4 : B3 = 2 * B4 := by rw [hB4', two_mul]
  have heq4src : (2 * A4) ^ 4 + (2 * B4) ^ 4 =
      2 ^ 14 * (4 * B4 + 1) ^ 13 := by
    have hB21' : 2 * B3 + 1 = 4 * B4 + 1 := by
      rw [hB4]
      have hmul : 2 * (2 * B4) = 4 * B4 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA4, ← hB4, ← hB21']; exact h14
  have heq4 : 16 * (A4 ^ 4 + B4 ^ 4) = 2 ^ 14 * (4 * B4 + 1) ^ 13 := by
    rw [← BealGap2.sum_fourth_of_mul_two]; exact heq4src
  have h10 : A4 ^ 4 + B4 ^ 4 = 2 ^ 10 * (4 * B4 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 14 = 16 * 2 ^ 10 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq4, hpow, mul_assoc]
  have h16₄ : (A4 ^ 4 + B4 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 10 * (4 * B4 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 10) _
    exact Nat.mod_eq_zero_of_dvd (h10 ▸ this)
  obtain ⟨hA4e, hB4e⟩ := BealGap2.both_even_of_sum_fourth_mod16_zero h16₄
  obtain ⟨A5, hA5'⟩ := hA4e
  obtain ⟨B5, hB5'⟩ := hB4e
  have hA5 : A4 = 2 * A5 := by rw [hA5', two_mul]
  have hB5 : B4 = 2 * B5 := by rw [hB5', two_mul]
  have heq5src : (2 * A5) ^ 4 + (2 * B5) ^ 4 =
      2 ^ 10 * (8 * B5 + 1) ^ 13 := by
    have hB21' : 4 * B4 + 1 = 8 * B5 + 1 := by
      rw [hB5]
      have hmul : 4 * (2 * B5) = 8 * B5 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA5, ← hB5, ← hB21']; exact h10
  have heq5 : 16 * (A5 ^ 4 + B5 ^ 4) = 2 ^ 10 * (8 * B5 + 1) ^ 13 := by
    rw [← BealGap2.sum_fourth_of_mul_two]; exact heq5src
  have h6 : A5 ^ 4 + B5 ^ 4 = 2 ^ 6 * (8 * B5 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 10 = 16 * 2 ^ 6 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq5, hpow, mul_assoc]
  have h16₅ : (A5 ^ 4 + B5 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 6 * (8 * B5 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 6) _
    exact Nat.mod_eq_zero_of_dvd (h6 ▸ this)
  obtain ⟨hA5e, hB5e⟩ := BealGap2.both_even_of_sum_fourth_mod16_zero h16₅
  obtain ⟨A6, hA6'⟩ := hA5e
  obtain ⟨B6, hB6'⟩ := hB5e
  have hA6 : A5 = 2 * A6 := by rw [hA6', two_mul]
  have hB6 : B5 = 2 * B6 := by rw [hB6', two_mul]
  have heq6src : (2 * A6) ^ 4 + (2 * B6) ^ 4 =
      2 ^ 6 * (16 * B6 + 1) ^ 13 := by
    have hB21' : 8 * B5 + 1 = 16 * B6 + 1 := by
      rw [hB6]
      have hmul : 8 * (2 * B6) = 16 * B6 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA6, ← hB6, ← hB21']; exact h6
  have heq6 : 16 * (A6 ^ 4 + B6 ^ 4) = 2 ^ 6 * (16 * B6 + 1) ^ 13 := by
    rw [← BealGap2.sum_fourth_of_mul_two]; exact heq6src
  have hlast : A6 ^ 4 + B6 ^ 4 = 4 * (16 * B6 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 6 = 16 * 4 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq6, hpow, mul_assoc]
  have hodd : Odd ((16 * B6 + 1) ^ 13) :=
    Odd.pow (odd_of_sixteen_mul_add_one B6)
  exact not_sum_fourth_eq_four_mul_odd hodd hlast

theorem B_odd_of_sol_gap4 {A B : ℕ} (h : is_gap4_sol A B) : Odd B := by
  rw [← Nat.not_even_iff_odd]
  intro hBeven
  exact no_sol_when_even_B h hBeven

/-! ## Coprimeness: `gcd(A,B) = 1` on every solution -/

theorem gcd_A_B_eq_one_of_sol {A B : ℕ}
    (h : is_gap4_sol A B) : Nat.gcd A B = 1 := by
  have hBodd := B_odd_of_sol_gap4 h
  set d := Nat.gcd A B
  have hdA : d ∣ A := Nat.gcd_dvd_left A B
  have hdB : d ∣ B := Nat.gcd_dvd_right A B
  have hdC13 : d ∣ (B + 4) ^ 13 := by
    have hA4 : d ∣ A ^ 4 := dvd_pow hdA (by decide)
    have hB4 : d ∣ B ^ 4 := dvd_pow hdB (by decide)
    have hsum : d ∣ A ^ 4 + B ^ 4 := Nat.dvd_add hA4 hB4
    simpa [is_gap4_sol] using (h ▸ hsum)
  have hgcd4 : Nat.gcd d (B + 4) ∣ 4 := by
    have h1 : Nat.gcd d (B + 4) ∣ B :=
      dvd_trans (Nat.gcd_dvd_left d (B + 4)) hdB
    have h2 : Nat.gcd d (B + 4) ∣ (B + 4) := Nat.gcd_dvd_right d (B + 4)
    exact dvd_trans (Nat.dvd_gcd h1 h2) (gcd_B_C_dvd_four B)
  have hgcd1 : Nat.gcd d (B + 4) = 1 := by
    have hdvd : Nat.gcd d (B + 4) ∣ 2 ^ 2 := by
      simpa using hgcd4
    obtain ⟨m, hm, heq⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hm0 : m = 0 := by
      by_contra hmnz
      have hmpos : 0 < m := Nat.pos_of_ne_zero hmnz
      have h2g : 2 ∣ Nat.gcd d (B + 4) := by
        rw [heq]
        exact pow_dvd_pow (2 : ℕ) (Nat.succ_le_of_lt hmpos)
      have hd2 : 2 ∣ d := dvd_trans h2g (Nat.gcd_dvd_left d (B + 4))
      have h2B : 2 ∣ B := dvd_trans hd2 hdB
      exact absurd (even_iff_two_dvd.2 h2B) (Nat.not_even_iff_odd.2 hBodd)
    subst hm0
    simpa using heq
  have hcop : Nat.Coprime d (B + 4) := hgcd1
  have hcop13 : Nat.Coprime d ((B + 4) ^ 13) := hcop.pow_right 13
  have hd1 : d ∣ 1 := by
    have := Nat.dvd_gcd (dvd_refl d) hdC13
    rwa [show Nat.gcd d ((B + 4) ^ 13) = 1 from hcop13] at this
  exact Nat.eq_one_of_dvd_one hd1

theorem gcd_A_B_eq_one_of_sol_gap4 {A B : ℕ}
    (h : is_gap4_sol A B) : Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_sol h

theorem coprime_of_sol_gap4 {A B : ℕ}
    (h : is_gap4_sol A B) : Nat.Coprime A B :=
  gcd_A_B_eq_one_of_sol h

/-! ## Size: `A > B` for `B > 0`; `A ≠ 0` on every solution -/

theorem two_mul_B_pow_four_lt_add_four_pow (B : ℕ) :
    2 * B ^ 4 < (B + 4) ^ 13 := by
  have h4 : 4 ≤ B + 4 := Nat.le_add_left 4 B
  have h2 : 2 ≤ B + 4 := le_trans (by decide : 2 ≤ 4) h4
  have h2pow : 2 ≤ 2 ^ 9 := by decide
  have h29 : 2 ^ 9 ≤ (B + 4) ^ 9 := Nat.pow_le_pow_left h2 9
  have h2le : 2 ≤ (B + 4) ^ 9 := le_trans h2pow h29
  have hBlt : B < B + 4 := Nat.lt_add_of_pos_right (by decide : 0 < (4 : ℕ))
  have hB4 : B ^ 4 < (B + 4) ^ 4 :=
    Nat.pow_lt_pow_left hBlt (by decide : 4 ≠ 0)
  have hle : 2 * B ^ 4 ≤ (B + 4) ^ 9 * B ^ 4 :=
    Nat.mul_le_mul_right (B ^ 4) h2le
  have hposC : 0 < B + 4 := Nat.add_pos_right B (by decide : 0 < 4)
  have hpos9 : 0 < (B + 4) ^ 9 := Nat.pos_pow_of_pos 9 hposC
  have hlt : (B + 4) ^ 9 * B ^ 4 < (B + 4) ^ 9 * (B + 4) ^ 4 :=
    Nat.mul_lt_mul_of_pos_left hB4 hpos9
  have hsum : (B + 4) ^ 9 * (B + 4) ^ 4 = (B + 4) ^ 13 := by
    rw [← pow_add]
  rw [← hsum]
  exact lt_of_le_of_lt hle hlt

theorem A_gt_B_of_sol {A B : ℕ}
    (h : is_gap4_sol A B) (_hB : 0 < B) : B < A := by
  by_contra hle
  have hAB : A ≤ B := Nat.not_lt.mp hle
  have hA4 : A ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hAB 4
  have hsum : A ^ 4 + B ^ 4 ≤ 2 * B ^ 4 := by
    have := Nat.add_le_add hA4 (le_refl (B ^ 4))
    simpa [two_mul] using this
  have hlt := two_mul_B_pow_four_lt_add_four_pow B
  have : A ^ 4 + B ^ 4 < (B + 4) ^ 13 := lt_of_le_of_lt hsum hlt
  exact (ne_of_lt this) h

theorem A_ne_zero_of_sol {A B : ℕ} (h : is_gap4_sol A B) : A ≠ 0 := by
  intro hA
  subst hA
  have heq : B ^ 4 = (B + 4) ^ 13 := by
    simpa [is_gap4_sol] using h
  by_cases hB : B = 0
  · subst hB
    exact (by decide : (0 : ℕ) ≠ 67108864) heq
  · have hpos : 0 < B := Nat.pos_of_ne_zero hB
    have hB4pos : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hpos
    have hlt1 : B ^ 4 < 2 * B ^ 4 := by
      have : 1 * B ^ 4 < 2 * B ^ 4 :=
        Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hB4pos
      simpa using this
    have hlt2 := two_mul_B_pow_four_lt_add_four_pow B
    exact (ne_of_lt (lt_trans hlt1 hlt2)) heq

theorem A_gt_one_of_sol_pos {A B : ℕ}
    (h : is_gap4_sol A B) (hB : 0 < B) : 1 < A :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) (A_gt_B_of_sol h hB)

/-! ## `mod 3`: `3 ∣ B` is compatible (like gap-1), and forces `3 ∤ A` -/

theorem fourth_pow_mod3 (a : ℕ) : a ^ 4 % 3 = 0 ∨ a ^ 4 % 3 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod3 a

theorem pow13_mod3 (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  BealMatveevBeal.BealGap1.pow13_mod3_eq_self c

theorem pow13_mod3_eq_self (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  pow13_mod3 c

/-- `C = B+4 ≡ 1 mod 3`, so `C¹³ ≡ 1` and `A⁴ ≡ 1`. No contradiction.
    Do **not** prove `no_sol_when_three_dvd_B` here. -/
theorem A_pow_four_mod3_eq_one_of_three_dvd_B {A B : ℕ}
    (h : is_gap4_sol A B) (h3 : 3 ∣ B) : A ^ 4 % 3 = 1 := by
  have hB4 : B ^ 4 % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h3 (by decide))
  have hC : (B + 4) % 3 = 1 := by
    have : B % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    rw [Nat.add_mod, this]
  have hC13 : (B + 4) ^ 13 % 3 = 1 := by
    rw [pow13_mod3, hC]
  have hsum : (A ^ 4 + B ^ 4) % 3 = (B + 4) ^ 13 % 3 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod3 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · exact h1

theorem not_three_dvd_A_of_three_dvd_B {A B : ℕ}
    (h : is_gap4_sol A B) (hB : 3 ∣ B) : ¬ 3 ∣ A := by
  intro hA
  have : 3 ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
  rw [gcd_A_B_eq_one_of_sol h] at this
  exact (by decide : ¬ (3 ∣ 1)) this

/-! ## `mod 5`: `5 ∣ B` is a contradiction (new for gap-4) -/

theorem fourth_pow_mod5 (a : ℕ) : a ^ 4 % 5 = 0 ∨ a ^ 4 % 5 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod5 a

theorem pow13_mod5 (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  BealMatveevBeal.BealGap1.pow13_mod5_eq_self c

theorem pow13_mod5_eq_self (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  pow13_mod5 c

/-- `C = B+4 ≡ 4 mod 5`, so `C¹³ ≡ 4`, while `A⁴ + B⁴ ≡ A⁴ ∈ {0,1}`. -/
theorem no_sol_when_five_dvd_B_gap4 {A B : ℕ}
    (h : is_gap4_sol A B) (h5 : 5 ∣ B) : False := by
  have hB4 : B ^ 4 % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h5 (by decide))
  have hC : (B + 4) % 5 = 4 := by
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [Nat.add_mod, this]
  have hC13 : (B + 4) ^ 13 % 5 = 4 := by
    rw [pow13_mod5, hC]
  have hsum : (A ^ 4 + B ^ 4) % 5 = (B + 4) ^ 13 % 5 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod5 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · rw [h1] at hsum
    exact absurd hsum (by decide)

theorem five_not_dvd_B_of_sol {A B : ℕ}
    (h : is_gap4_sol A B) : ¬ 5 ∣ B :=
  fun h5 => no_sol_when_five_dvd_B_gap4 h h5

/-- Remaining coprime branch after `5 ∤ B`. Coprimeness already holds
    for every gap-4 solution (`B` odd). -/
theorem coprime_of_remaining_gap4 {A B : ℕ}
    (h : is_gap4_sol A B) (_h5 : ¬ 5 ∣ B) : Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_sol h

/-! ## Linear form `Λ = 4 log A − 13 log(B+4)` -/

noncomputable def Lambda_gap4 (A B : ℕ) : ℝ :=
  4 * log (A : ℝ) - 13 * log ((B + 4 : ℕ) : ℝ)

theorem A_pow_four_eq_sub {A B : ℕ} (h : is_gap4_sol A B) :
    A ^ 4 = (B + 4) ^ 13 - B ^ 4 := by
  rw [← h, add_comm, Nat.add_sub_cancel_left]

theorem A_pow_real_add {A B : ℕ} (h : is_gap4_sol A B) :
    (A : ℝ) ^ 4 + (B : ℝ) ^ 4 = ((B + 4 : ℕ) : ℝ) ^ 13 := by
  have h' : ((A ^ 4 + B ^ 4 : ℕ) : ℝ) = (((B + 4) ^ 13 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [Nat.cast_add, Nat.cast_pow] using h'

theorem A_pow_pos_of_sol {A B : ℕ} (h : is_gap4_sol A B) :
    (0 : ℝ) < (A : ℝ) ^ 4 := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  exact pow_pos hApos 4

theorem Lambda_gap4_eq_log_div {A B : ℕ}
    (h : is_gap4_sol A B) :
    Lambda_gap4 A B =
      log ((A : ℝ) ^ 4 / ((B + 4 : ℕ) : ℝ) ^ 13) := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hCpos : (0 : ℝ) < ((B + 4 : ℕ) : ℝ) := by
    have : 0 < B + 4 := Nat.add_pos_right B (by decide : 0 < 4)
    exact_mod_cast this
  unfold Lambda_gap4
  have h4 : (4 : ℝ) * log (A : ℝ) = log ((A : ℝ) ^ 4) :=
    (Real.log_pow (A : ℝ) 4).symm
  have h13 : (13 : ℝ) * log ((B + 4 : ℕ) : ℝ) =
      log (((B + 4 : ℕ) : ℝ) ^ 13) :=
    (Real.log_pow ((B + 4 : ℕ) : ℝ) 13).symm
  rw [h4, h13, Real.log_div (pow_pos hApos 4).ne' (pow_pos hCpos 13).ne']

theorem abs_Lambda_gap4_eq_log_one_plus {A B : ℕ}
    (h : is_gap4_sol A B) (hB : 0 < B) :
    |Lambda_gap4 A B| = log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hu : (0 : ℝ) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    div_pos (pow_pos hBpos 4) hA4pos
  have hsum := A_pow_real_add h
  have hratio :
      (A : ℝ) ^ 4 / ((B + 4 : ℕ) : ℝ) ^ 13 =
        1 / (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    have hne : (A : ℝ) ^ 4 ≠ 0 := hA4pos.ne'
    have hden :
        (1 : ℝ) + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 =
          ((A : ℝ) ^ 4 + (B : ℝ) ^ 4) / (A : ℝ) ^ 4 := by
      field_simp [hne]
    rw [hden, one_div_div, hsum]
  have hΛ := Lambda_gap4_eq_log_div h
  have h1u : (0 : ℝ) < 1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    add_pos_of_nonneg_of_pos zero_le_one hu
  have hlog :
      Lambda_gap4 A B = -log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    rw [hΛ, hratio, Real.log_div one_ne_zero h1u.ne', log_one, zero_sub]
  rw [hlog, abs_neg, abs_of_nonneg (log_nonneg (le_of_lt (lt_add_of_pos_right 1 hu)))]

theorem abs_Lambda_gap4_le_ratio {A B : ℕ}
    (h : is_gap4_sol A B) (hB : 0 < B) :
    |Lambda_gap4 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
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
  rwa [abs_Lambda_gap4_eq_log_one_plus h hB]

theorem B_pow_five_add_B_pow_four_lt_add_four_pow {B : ℕ} (_hB : 0 < B) :
    (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 4 : ℕ) : ℝ) ^ 13 := by
  have hx : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : ((B + 4 : ℕ) : ℝ) = (B : ℝ) + 4 := by
    rw [Nat.cast_add]
    norm_num
  have h5 : (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 4 : ℕ) : ℝ) ^ 5 := by
    rw [hC]
    have hexp : ((B : ℝ) + 4) ^ 5 =
        (B : ℝ) ^ 5 + 20 * (B : ℝ) ^ 4 + 160 * (B : ℝ) ^ 3 +
          640 * (B : ℝ) ^ 2 + 1280 * (B : ℝ) + 1024 := by
      ring
    have h3 : (0 : ℝ) ≤ (B : ℝ) ^ 3 := pow_nonneg hx 3
    have h2 : (0 : ℝ) ≤ (B : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hexp, h3, h2, hx]
  have hC1 : (1 : ℝ) ≤ ((B + 4 : ℕ) : ℝ) := by
    have : 1 ≤ B + 4 := le_trans (by decide : 1 ≤ 4) (Nat.le_add_left 4 B)
    exact_mod_cast this
  have h513 : ((B + 4 : ℕ) : ℝ) ^ 5 ≤ ((B + 4 : ℕ) : ℝ) ^ 13 :=
    pow_le_pow_right hC1 (by decide : (5 : ℕ) ≤ 13)
  exact lt_of_lt_of_le h5 h513

theorem A_pow_gt_B_pow_five {A B : ℕ}
    (h : is_gap4_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 5 < (A : ℝ) ^ 4 := by
  have hA4 : (A : ℝ) ^ 4 =
      ((B + 4 : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 := by
    linarith [A_pow_real_add h]
  have hsum := B_pow_five_add_B_pow_four_lt_add_four_pow hB
  linarith [hA4, hsum]

theorem ratio_lt_inv_B {A B : ℕ}
    (h : is_gap4_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 4 / (A : ℝ) ^ 4 < 1 / (B : ℝ) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hgt := A_pow_gt_B_pow_five h hB
  have : (B : ℝ) ^ 4 * (B : ℝ) < (A : ℝ) ^ 4 := by
    have : (B : ℝ) ^ 5 = (B : ℝ) ^ 4 * (B : ℝ) := by ring
    rwa [this] at hgt
  rw [div_lt_div_iff hA4pos hBpos, one_mul]
  exact this

theorem abs_Lambda_gap4_lt_inv_B {A B : ℕ}
    (h : is_gap4_sol A B) (hB : 0 < B) :
    |Lambda_gap4 A B| < 1 / (B : ℝ) :=
  lt_of_le_of_lt (abs_Lambda_gap4_le_ratio h hB) (ratio_lt_inv_B h hB)

theorem A_pow_lt_C_pow {A B : ℕ}
    (h : is_gap4_sol A B) (hB : 0 < B) :
    (A : ℝ) ^ 4 < ((B + 4 : ℕ) : ℝ) ^ 13 := by
  have hB4 : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hB
  have hlt : A ^ 4 < (B + 4) ^ 13 :=
    calc
      A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
      _ = (B + 4) ^ 13 := h
  exact_mod_cast hlt

/-! ## Log-method no-go (`C1 ≥ 1` loses to `B⁴/A⁴`) -/

theorem logA_gt_thirteen_of_B_ge_B0 {A B : ℕ}
    (h : is_gap4_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
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

/-- `exp(−C1 log A log(B+4)) < B⁴/A⁴` for every `C1 ≥ 1` on
    a gap-4 solution with `B ≥ B0`. Same cutoff as `62383af`:
    `C1 < 1` would be needed. -/
theorem hGen_exp_lt_ratio_gap4
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {A B : ℕ} (hsol : is_gap4_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + 4 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  set a : ℝ := log (A : ℝ)
  set c : ℝ := log ((B + 4 : ℕ) : ℝ)
  set C : ℝ := ((B + 4 : ℕ) : ℝ)
  have hAgt1 : 1 < A := A_gt_one_of_sol_pos hsol hB
  have hCgt1 : 1 < B + 4 :=
    lt_of_lt_of_le (by decide : 1 < 4) (Nat.le_add_left 4 B)
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (0 : ℕ) < A := lt_trans Nat.zero_lt_one hAgt1
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C := by
    have : 0 < B + 4 := Nat.add_pos_right B (by decide : 0 < 4)
    have : (0 : ℝ) < ((B + 4 : ℕ) : ℝ) := by exact_mod_cast this
    simpa [C] using this
  have hCgt : (1 : ℝ) < C := by
    have : (1 : ℝ) < ((B + 4 : ℕ) : ℝ) := by exact_mod_cast hCgt1
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

theorem C1_floor_hGen_loses_gap4 {A B : ℕ}
    (hsol : is_gap4_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + 4 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio_gap4
    (le_of_lt (by
      simpa [C1_floor_eq_logs] using
        BealMatveevBeal.MatveevThreeLogs.C1_floor_gt_one))
    hsol hB hB0

/-! ## Floor form / LLL no-go (`B+4`, not `B+3` / `B+2` / `B+1`) -/

noncomputable def floorFormThird_gap4 (C : ℝ) (A B : ℕ) : ℝ :=
  (4 : ℝ) * ⌊C * log (A : ℝ)⌋ - 13 * ⌊C * log ((B + 4 : ℕ) : ℝ)⌋

/-- `|4⌊C log A⌋ − 13⌊C log(B+4)⌋ − C Λ| < 17` for every real `C`. -/
theorem floor_form_approx_of_C_gap4 (C : ℝ) (A B : ℕ) :
    |floorFormThird_gap4 C A B - C * Lambda_gap4 A B| < 17 := by
  set a : ℝ := C * log (A : ℝ)
  set cval : ℝ := C * log ((B + 4 : ℕ) : ℝ)
  have hΛ : C * Lambda_gap4 A B = 4 * a - 13 * cval := by
    simp only [Lambda_gap4, a, cval]
    ring
  have hft : floorFormThird_gap4 C A B = (4 : ℝ) * ⌊a⌋ - 13 * ⌊cval⌋ := rfl
  have hform :
      floorFormThird_gap4 C A B - C * Lambda_gap4 A B =
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

theorem floor_form_third_abs_lt_gap4 {C : ℝ} (hC : 0 < C) (A B : ℕ) :
    |floorFormThird_gap4 C A B| < 17 + C * |Lambda_gap4 A B| := by
  have happ := floor_form_approx_of_C_gap4 C A B
  have hmul : |C * Lambda_gap4 A B| = C * |Lambda_gap4 A B| := by
    rw [abs_mul, abs_of_pos hC]
  have := abs_sub_abs_le_abs_sub
    (floorFormThird_gap4 C A B) (C * Lambda_gap4 A B)
  linarith [happ, this, hmul]

/-- No scaling `C > 0` yields a Baker–Davenport witness
    `r > 17 + C/B0` on a gap-4 solution with `B ≥ B0`. -/
theorem hLLL_method_fails_gap4 :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        is_gap4_sol A B →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |floorFormThird_gap4 C A B| := by
  intro C hC A B hsol hB hB0
  rintro ⟨r, hgt, hle⟩
  have htri := floor_form_third_abs_lt_gap4 hC A B
  have hLam := abs_Lambda_gap4_lt_inv_B hsol hB
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hBle : (B0_nat : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hB0
  have hCΛ : C * |Lambda_gap4 A B| < C / (B0_nat : ℝ) := by
    have hmid : C * |Lambda_gap4 A B| < C * (1 / (B : ℝ)) :=
      mul_lt_mul_of_pos_left hLam hC
    have hrew : C * (1 / (B : ℝ)) = C / (B : ℝ) := mul_one_div _ _
    have hCB : C / (B : ℝ) ≤ C / (B0_nat : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hC) hB0pos hBle
    linarith [hmid, hrew, hCB]
  have hthird : |floorFormThird_gap4 C A B| < 17 + C / (B0_nat : ℝ) := by
    linarith [htri, hCΛ]
  linarith [hgt, hle, hthird]

theorem no_uniform_c_cubic_in_N_gap4 :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (BealMatveevBeal.MatveevThreeLogs.coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) :=
  BealMatveevBeal.MatveevThreeLogs.no_uniform_c_cubic_in_N

theorem coeffCount3_zero_ten_ten_ten_gap4 :
    BealMatveevBeal.MatveevThreeLogs.coeffCount3 0 10 10 10 = 1331 :=
  BealMatveevBeal.MatveevThreeLogs.coeffCount3_zero_ten_ten_ten

theorem no_uniform_c_easy_half_gap4 :
    (1 / 2 : ℝ) * 1 * 1 < 242 := by
  norm_num

/-! ## `hGen_gap4` / `hLLL_gap4` stay `def Prop` -/

/-- Matveev 2000 Theorem 1.4, n=2, displayed `C1_floor` exponential
    on a gap-4 solution. Not in Mathlib 4.12. Instantiating it at
    `B ≥ B0` does not beat `B⁴/A⁴`. -/
def hGen_gap4 : Prop :=
  ∀ A B : ℕ,
    is_gap4_sol A B →
      0 < B →
        |Lambda_gap4 A B| >
          exp (-(C1_floor : ℝ) * log (A : ℝ) *
            log ((B + 4 : ℕ) : ℝ))

/-- Bugeaud / LLL close for gap-4: ratio upper bound ⇒ `B ≤ B0`.
    The displayed lattice does not inhabit it. -/
def hLLL_gap4 : Prop :=
  (∀ A B : ℕ, is_gap4_sol A B → 0 < B →
      |Lambda_gap4 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4) →
    baker_bound_gap4

def baker_bound_gap4_of_hGen_hLLL : Prop :=
  hGen_gap4 → hLLL_gap4 → baker_bound_gap4

def baker_bound_gap4_of_hGen_hLLL_gap4 : Prop :=
  baker_bound_gap4_of_hGen_hLLL

/-! ## Combined unconditional no-go (no Darmon–Merel axiom) -/

/-- Log and LLL methods lose on `B ≥ B0`. Remaining solutions are
    coprime with `A > B0`, `B` odd, `A` even. `5 ∣ B` is impossible
    (`C ≡ 4 mod 5`). `3 ∣ B` is compatible and forces `3 ∤ A`.
    Darmon–Merel `(4,4,13)` would be refuted by any such solution.
    `baker_bound_gap4` stays uninhabited as a named theorem. -/
theorem baker_bound_gap4_unconditional_nogo {A B : ℕ}
    (hsol : is_gap4_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + 4 : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (∀ C : ℝ, 0 < C →
      ¬ ∃ r : ℝ,
        17 + C / (B0_nat : ℝ) < r ∧
          r ≤ |floorFormThird_gap4 C A B|) ∧
    Nat.Coprime A B ∧
    B0_nat < A ∧
    Odd B ∧
    Even A ∧
    ¬ 5 ∣ B ∧
    (3 ∣ B → ¬ 3 ∣ A) ∧
    (darmon_merel_44_13_no_coprime → False) := by
  refine ⟨?_, ?_, coprime_of_sol_gap4 hsol, ?_,
    B_odd_of_sol_gap4 hsol, A_even_of_sol_gap4 hsol,
    five_not_dvd_B_of_sol hsol, ?_, ?_⟩
  · intro C1 hC1
    exact hGen_exp_lt_ratio_gap4 hC1 hsol hB hB0
  · intro C hC
    exact hLLL_method_fails_gap4 C hC A B hsol hB hB0
  · exact Nat.lt_of_le_of_lt hB0 (A_gt_B_of_sol hsol hB)
  · intro h3
    exact not_three_dvd_A_of_three_dvd_B hsol h3
  · intro hDM
    have hA0 : A = 0 ∨ B = 0 :=
      hDM A B (B + 4) (coprime_of_sol_gap4 hsol) hsol
    cases hA0 with
    | inl hA => exact A_ne_zero_of_sol hsol hA
    | inr hB0' => exact (ne_of_gt hB) hB0'

/-! ## Axiom-relative close (reuses `BealTrueV25`, no new axiom) -/

/-- Every gap-4 solution is impossible relative to
    `darmon_merel_4413_axiom`. Unlike gap-1 there is no `(1,0)`. -/
theorem no_gap4_of_axiom {A B : ℕ}
    (hsol : is_gap4_sol A B) : False := by
  have hDM := BealMatveevBeal.BealTrueV25.darmon_merel_4413_axiom
  have hA0 : A = 0 ∨ B = 0 :=
    hDM A B (B + 4) (coprime_of_sol_gap4 hsol) hsol
  cases hA0 with
  | inl hA => exact A_ne_zero_of_sol hsol hA
  | inr hB0 =>
      have hodd := B_odd_of_sol_gap4 hsol
      subst hB0
      exact Nat.not_even_iff_odd.2 hodd even_zero

/-- Vacuous `B ≤ B0` for every gap-4 solution, relative to the
    existing Darmon–Merel axiom. Not named `baker_bound_gap4`. -/
theorem baker_bound_gap4_true {A B : ℕ}
    (hsol : is_gap4_sol A B) : B ≤ B0_nat :=
  (no_gap4_of_axiom hsol).elim

theorem baker_bound_gap4_true_of_axiom {A B : ℕ}
    (hsol : is_gap4_sol A B) : B ≤ B0_nat :=
  baker_bound_gap4_true hsol

#check C1_floor_eq
#check B0_nat_eq
#check not_gap4_one_zero
#check gcd_B_C_eq_gcd_four
#check gcd_B_C_dvd_four
#check gcd_A_B_eq_one_of_sol
#check coprime_of_sol_gap4
#check A_even_of_sol_gap4
#check B_odd_of_sol_gap4
#check no_sol_when_even_B
#check A_gt_B_of_sol
#check no_sol_when_five_dvd_B_gap4
#check not_three_dvd_A_of_three_dvd_B
#check A_pow_four_mod3_eq_one_of_three_dvd_B
#check coprime_of_remaining_gap4
#check hGen_exp_lt_ratio_gap4
#check C1_floor_hGen_loses_gap4
#check floor_form_approx_of_C_gap4
#check hLLL_method_fails_gap4
#check no_uniform_c_cubic_in_N_gap4
#check no_uniform_c_easy_half_gap4
#check hGen_gap4
#check hLLL_gap4
#check baker_bound_gap4_of_hGen_hLLL
#check baker_bound_gap4_unconditional_nogo
#check baker_bound_gap4
#check no_gap4_of_axiom
#check baker_bound_gap4_true
#check baker_bound_gap4_true_of_axiom
#print axioms gcd_A_B_eq_one_of_sol
#print axioms B_odd_of_sol_gap4
#print axioms no_sol_when_five_dvd_B_gap4
#print axioms not_three_dvd_A_of_three_dvd_B
#print axioms hGen_exp_lt_ratio_gap4
#print axioms C1_floor_hGen_loses_gap4
#print axioms hLLL_method_fails_gap4
#print axioms baker_bound_gap4_unconditional_nogo
#print axioms no_gap4_of_axiom
#print axioms baker_bound_gap4_true

end BealMatveevBeal.BealGap4
