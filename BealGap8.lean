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
import BealGap7

/-!
# Gap-8 `A⁴ + B⁴ = (B+8)¹³` (not a `B ≤ 10⁶` close)

Successor of `4e30497` (`v24-v24x-final-gap7-nogo`).
`C = B+8` so `gcd(B,C) ∣ 8`. Parity is gap-2/4/6, not gap-1/5/7:
`A` is even (odd `A` makes the left side `1` or `2` mod 16 while
even `C` is `0` and odd `C` is odd, never `2`). Even `B` dies
after nine divisions by `2`, leaving
`A₉⁴ + B₉⁴ = 8 (64 B₉ + 1)¹³` with residue `8` mod 16
(not gap-2's `2`/`10`, gap-4's `4`/`12`, or gap-6's `6`/`14`).
So `B` is odd and `A` is even.
`(1,0)` is **not** a solution (`1 ≠ 8¹³`). Like gap-2 `7a1c53b`
and gap-5 `59d8a4a`, `3 ∣ B` kills residue: `C ≡ 2 mod 3`,
`C¹³ ≡ 2`, while `A⁴ ∈ {0,1}`. `5 ∣ B` **does** kill
(`C ≡ 3 mod 5`, `C¹³ ≡ 3`, not in `{0,1}`). `7 ∣ B` is
compatible (`C ≡ 1 mod 7`, `A⁴ ≡ 1`). Remaining solutions
are coprime (`p ∣ A,B` ⇒ `p ∣ 8`, but `B` is odd) and
pure Darmon–Merel signature `(4,4,13)`.

`hGen_gap8` / `hLLL_gap8` stay `def Prop`. Every `C1 ≥ 1` loses
to `B⁴/A⁴` on `B ≥ B0`; no scaling yields a Baker–Davenport
witness above `17 + C/B0`. Named theorem `baker_bound_gap8`
stays a `def Prop`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

set_option maxHeartbeats 800000

open Real

namespace BealMatveevBeal.BealGap8

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_logs :
    C1_floor = BealMatveevBeal.MatveevThreeLogs.C1_floor := rfl

theorem B0_nat_eq_logs :
    B0_nat = BealMatveevBeal.MatveevThreeLogs.B0_nat := rfl

/-! ## Gap-8 equation -/

def is_gap8_sol (A B : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = (B + 8) ^ 13

/-- Kernel Baker bound for gap-8. Stays a `def Prop`. -/
def baker_bound_gap8 : Prop :=
  ∀ A B : ℕ, is_gap8_sol A B → B ≤ B0_nat

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealTrueV25.darmon_merel_44_13_no_coprime

/-! ## `(1,0)` is not a solution -/

theorem not_gap8_one_zero : ¬ is_gap8_sol 1 0 := by
  unfold is_gap8_sol
  decide

theorem even_eight : Even (8 : ℕ) := ⟨4, rfl⟩

/-! ## `gcd(B, B+8) = gcd(B, 8)` divides `8` -/

theorem gcd_B_C_eq_gcd_eight (B : ℕ) : Nat.gcd B (B + 8) = Nat.gcd B 8 := by
  rw [Nat.gcd_comm B (B + 8), Nat.add_comm B 8]
  exact (Nat.gcd_add_self_left (8 : ℕ) B).trans (Nat.gcd_comm 8 B)

theorem gcd_B_C_dvd_eight (B : ℕ) : Nat.gcd B (B + 8) ∣ 8 := by
  rw [gcd_B_C_eq_gcd_eight]
  exact Nat.gcd_dvd_right B 8

theorem gcd_B_C_dvd_eight_gap8 (B : ℕ) : Nat.gcd B (B + 8) ∣ 8 :=
  gcd_B_C_dvd_eight B

/-! ## Residue `8` after nine divisions by `2` -/

theorem eight_mul_odd_mod16 {n : ℕ} (h : Odd n) :
    (8 * n) % 16 = 8 := by
  obtain ⟨k, hk⟩ := h
  have : 8 * (k + k + 1) = 16 * k + 8 := by
    rw [← two_mul]
    ring
  rw [hk, this, Nat.add_mod, Nat.mul_mod]
  norm_num

theorem eight_mul_odd_pow13_mod16 {n : ℕ} (h : Odd n) :
    (8 * n ^ 13) % 16 = 8 :=
  eight_mul_odd_mod16 (h.pow)

theorem odd_of_sixtyfour_mul_add_one (k : ℕ) : Odd (64 * k + 1) :=
  ⟨32 * k, by ring⟩

theorem not_sum_fourth_eq_eight_mul_odd {X Y n : ℕ}
    (hn : Odd n) (h : X ^ 4 + Y ^ 4 = 8 * n ^ 13) : False := by
  have hmod : (X ^ 4 + Y ^ 4) % 16 = (8 * n ^ 13) % 16 := by rw [h]
  have hR : (8 * n ^ 13) % 16 = 8 := eight_mul_odd_pow13_mod16 hn
  obtain h0 | h1 | h2 := BealMatveevBeal.BealGap2.sum_fourth_mod16 X Y
  · rw [h0, hR] at hmod
    exact (by decide : (0 : ℕ) ≠ 8) hmod
  · rw [h1, hR] at hmod
    exact (by decide : (1 : ℕ) ≠ 8) hmod
  · rw [h2, hR] at hmod
    exact (by decide : (2 : ℕ) ≠ 8) hmod

/-! ## Parity: `A` is even. Even `B` is impossible, so `B` is odd. -/

theorem A_even_of_sol_gap8 {A B : ℕ} (h : is_gap8_sol A B) : Even A := by
  by_contra hne
  have hAodd : Odd A := Nat.not_even_iff_odd.1 hne
  have hA4 : A ^ 4 % 16 = 1 :=
    BealCatalanZsig.odd_pow_four_mod_sixteen hAodd
  by_cases hBeven : Even B
  · have hCeven : Even (B + 8) := hBeven.add even_eight
    have h16C : 16 ∣ (B + 8) ^ 4 :=
      BealCatalanZsig.even_pow_four_dvd_sixteen hCeven
    have h16R : 16 ∣ (B + 8) ^ 13 :=
      dvd_trans h16C (pow_dvd_pow (B + 8) (by decide : 4 ≤ 13))
    have hR : (B + 8) ^ 13 % 16 = 0 := Nat.mod_eq_zero_of_dvd h16R
    have hB4 : B ^ 4 % 16 = 0 :=
      Nat.mod_eq_zero_of_dvd (BealCatalanZsig.even_pow_four_dvd_sixteen hBeven)
    have hL : (A ^ 4 + B ^ 4) % 16 = 1 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + 8) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (1 : ℕ) ≠ 0) this
  · have hBodd : Odd B := Nat.not_even_iff_odd.1 hBeven
    have hCodd : Odd (B + 8) := hBodd.add_even even_eight
    have hB4 : B ^ 4 % 16 = 1 :=
      BealCatalanZsig.odd_pow_four_mod_sixteen hBodd
    have hL : (A ^ 4 + B ^ 4) % 16 = 2 := by
      rw [Nat.add_mod, hA4, hB4]
    have hR : (B + 8) ^ 13 % 16 = (B + 8) % 16 :=
      BealMatveevBeal.BealGap2.odd_pow_thirteen_mod_sixteen hCodd
    have : (A ^ 4 + B ^ 4) % 16 = (B + 8) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    have hC2 : (B + 8) % 2 = 0 := by
      have h16 : (B + 8) % 16 = 2 := this.symm
      have : ((B + 8) % 16) % 2 = 0 := by rw [h16]
      rwa [Nat.mod_mod_of_dvd (B + 8) (by decide : 2 ∣ 16)] at this
    exact Nat.not_even_iff_odd.2 hCodd (Nat.even_iff.2 hC2)

/-- Even `B` is impossible: nine divisions by `2` leave
    `A₉⁴ + B₉⁴ = 8 (64 B₉ + 1)¹³`, whose residue is `8`
    mod 16, never a sum of fourth powers `{0,1,2}`. Do **not**
    prove `B_even_of_sol_gap8`. -/
theorem no_sol_when_even_B {A B : ℕ}
    (h : is_gap8_sol A B) (hBeven : Even B) : False := by
  have hAeven := A_even_of_sol_gap8 h
  obtain ⟨A1, hA'⟩ := hAeven
  obtain ⟨B1, hB'⟩ := hBeven
  have hA : A = 2 * A1 := by rw [hA', two_mul]
  have hB : B = 2 * B1 := by rw [hB', two_mul]
  have hC : B + 8 = 2 * (B1 + 4) := by
    rw [hB, mul_add]
  have hsol1 : (2 * A1) ^ 4 + (2 * B1) ^ 4 = (2 * (B1 + 4)) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 16 * (A1 ^ 4 + B1 ^ 4) = 2 ^ 13 * (B1 + 4) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 2 ^ 9 * (B1 + 4) ^ 13 := by
    have hpow : (2 : ℕ) ^ 13 = 16 * 2 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq1, hpow, mul_assoc]
  have h16 : (A1 ^ 4 + B1 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 9 * (B1 + 4) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 9) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1e, hB1e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16
  obtain ⟨A2, hA2'⟩ := hA1e
  obtain ⟨B2, hB2'⟩ := hB1e
  have hA2 : A1 = 2 * A2 := by rw [hA2', two_mul]
  have hB2 : B1 = 2 * B2 := by rw [hB2', two_mul]
  have hB21 : B1 + 4 = 2 * (B2 + 2) := by
    rw [hB2, mul_add]
  have heq2src : (2 * A2) ^ 4 + (2 * B2) ^ 4 =
      2 ^ 9 * (2 * (B2 + 2)) ^ 13 := by
    rw [← hA2, ← hB2, ← hB21]; exact h9
  have heq2 : 16 * (A2 ^ 4 + B2 ^ 4) =
      2 ^ 9 * (2 * (B2 + 2)) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq2src
  have h18 : A2 ^ 4 + B2 ^ 4 = 2 ^ 18 * (B2 + 2) ^ 13 := by
    have hr : (2 * (B2 + 2)) ^ 13 = 2 ^ 13 * (B2 + 2) ^ 13 :=
      mul_pow _ _ 13
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq2, hr]
    have hpow : (2 : ℕ) ^ 9 * 2 ^ 13 = 16 * 2 ^ 18 := by norm_num
    rw [← mul_assoc, hpow, mul_assoc]
  have h16_2 : (A2 ^ 4 + B2 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 18 * (B2 + 2) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 18) _
    exact Nat.mod_eq_zero_of_dvd (h18 ▸ this)
  obtain ⟨hA2e, hB2e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16_2
  obtain ⟨A3, hA3'⟩ := hA2e
  obtain ⟨B3, hB3'⟩ := hB2e
  have hA3 : A2 = 2 * A3 := by rw [hA3', two_mul]
  have hB3 : B2 = 2 * B3 := by rw [hB3', two_mul]
  have hB32 : B2 + 2 = 2 * (B3 + 1) := by
    rw [hB3, mul_add, mul_one]
  have heq3src : (2 * A3) ^ 4 + (2 * B3) ^ 4 =
      2 ^ 18 * (2 * (B3 + 1)) ^ 13 := by
    rw [← hA3, ← hB3, ← hB32]; exact h18
  have heq3 : 16 * (A3 ^ 4 + B3 ^ 4) =
      2 ^ 18 * (2 * (B3 + 1)) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq3src
  have h27 : A3 ^ 4 + B3 ^ 4 = 2 ^ 27 * (B3 + 1) ^ 13 := by
    have hr : (2 * (B3 + 1)) ^ 13 = 2 ^ 13 * (B3 + 1) ^ 13 :=
      mul_pow _ _ 13
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq3, hr]
    have hpow : (2 : ℕ) ^ 18 * 2 ^ 13 = 16 * 2 ^ 27 := by norm_num
    rw [← mul_assoc, hpow, mul_assoc]
  have h16_3 : (A3 ^ 4 + B3 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 27 * (B3 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 27) _
    exact Nat.mod_eq_zero_of_dvd (h27 ▸ this)
  obtain ⟨hA3e, hB3e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16_3
  obtain ⟨A4, hA4'⟩ := hA3e
  obtain ⟨B4, hB4'⟩ := hB3e
  have hA4 : A3 = 2 * A4 := by rw [hA4', two_mul]
  have hB4 : B3 = 2 * B4 := by rw [hB4', two_mul]
  have heq4src : (2 * A4) ^ 4 + (2 * B4) ^ 4 =
      2 ^ 27 * (2 * B4 + 1) ^ 13 := by
    rw [← hA4, ← hB4]
    exact h27
  have heq4 : 16 * (A4 ^ 4 + B4 ^ 4) = 2 ^ 27 * (2 * B4 + 1) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq4src
  have h23 : A4 ^ 4 + B4 ^ 4 = 2 ^ 23 * (2 * B4 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 27 = 16 * 2 ^ 23 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq4, hpow, mul_assoc]
  have h16_4 : (A4 ^ 4 + B4 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 23 * (2 * B4 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 23) _
    exact Nat.mod_eq_zero_of_dvd (h23 ▸ this)
  obtain ⟨hA4e, hB4e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16_4
  obtain ⟨A5, hA5'⟩ := hA4e
  obtain ⟨B5, hB5'⟩ := hB4e
  have hA5 : A4 = 2 * A5 := by rw [hA5', two_mul]
  have hB5 : B4 = 2 * B5 := by rw [hB5', two_mul]
  have heq5src : (2 * A5) ^ 4 + (2 * B5) ^ 4 =
      2 ^ 23 * (4 * B5 + 1) ^ 13 := by
    have hC : 2 * B4 + 1 = 4 * B5 + 1 := by
      rw [hB5]
      have hmul : 2 * (2 * B5) = 4 * B5 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA5, ← hB5, ← hC]; exact h23
  have heq5 : 16 * (A5 ^ 4 + B5 ^ 4) = 2 ^ 23 * (4 * B5 + 1) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq5src
  have h19 : A5 ^ 4 + B5 ^ 4 = 2 ^ 19 * (4 * B5 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 23 = 16 * 2 ^ 19 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq5, hpow, mul_assoc]
  have h16_5 : (A5 ^ 4 + B5 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 19 * (4 * B5 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 19) _
    exact Nat.mod_eq_zero_of_dvd (h19 ▸ this)
  obtain ⟨hA5e, hB5e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16_5
  obtain ⟨A6, hA6'⟩ := hA5e
  obtain ⟨B6, hB6'⟩ := hB5e
  have hA6 : A5 = 2 * A6 := by rw [hA6', two_mul]
  have hB6 : B5 = 2 * B6 := by rw [hB6', two_mul]
  have heq6src : (2 * A6) ^ 4 + (2 * B6) ^ 4 =
      2 ^ 19 * (8 * B6 + 1) ^ 13 := by
    have hC : 4 * B5 + 1 = 8 * B6 + 1 := by
      rw [hB6]
      have hmul : 4 * (2 * B6) = 8 * B6 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA6, ← hB6, ← hC]; exact h19
  have heq6 : 16 * (A6 ^ 4 + B6 ^ 4) = 2 ^ 19 * (8 * B6 + 1) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq6src
  have h15 : A6 ^ 4 + B6 ^ 4 = 2 ^ 15 * (8 * B6 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 19 = 16 * 2 ^ 15 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq6, hpow, mul_assoc]
  have h16_6 : (A6 ^ 4 + B6 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 15 * (8 * B6 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 15) _
    exact Nat.mod_eq_zero_of_dvd (h15 ▸ this)
  obtain ⟨hA6e, hB6e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16_6
  obtain ⟨A7, hA7'⟩ := hA6e
  obtain ⟨B7, hB7'⟩ := hB6e
  have hA7 : A6 = 2 * A7 := by rw [hA7', two_mul]
  have hB7 : B6 = 2 * B7 := by rw [hB7', two_mul]
  have heq7src : (2 * A7) ^ 4 + (2 * B7) ^ 4 =
      2 ^ 15 * (16 * B7 + 1) ^ 13 := by
    have hC : 8 * B6 + 1 = 16 * B7 + 1 := by
      rw [hB7]
      have hmul : 8 * (2 * B7) = 16 * B7 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA7, ← hB7, ← hC]; exact h15
  have heq7 : 16 * (A7 ^ 4 + B7 ^ 4) = 2 ^ 15 * (16 * B7 + 1) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq7src
  have h11 : A7 ^ 4 + B7 ^ 4 = 2 ^ 11 * (16 * B7 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 15 = 16 * 2 ^ 11 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq7, hpow, mul_assoc]
  have h16_7 : (A7 ^ 4 + B7 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 11 * (16 * B7 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 11) _
    exact Nat.mod_eq_zero_of_dvd (h11 ▸ this)
  obtain ⟨hA7e, hB7e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16_7
  obtain ⟨A8, hA8'⟩ := hA7e
  obtain ⟨B8, hB8'⟩ := hB7e
  have hA8 : A7 = 2 * A8 := by rw [hA8', two_mul]
  have hB8 : B7 = 2 * B8 := by rw [hB8', two_mul]
  have heq8src : (2 * A8) ^ 4 + (2 * B8) ^ 4 =
      2 ^ 11 * (32 * B8 + 1) ^ 13 := by
    have hC : 16 * B7 + 1 = 32 * B8 + 1 := by
      rw [hB8]
      have hmul : 16 * (2 * B8) = 32 * B8 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA8, ← hB8, ← hC]; exact h11
  have heq8 : 16 * (A8 ^ 4 + B8 ^ 4) = 2 ^ 11 * (32 * B8 + 1) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq8src
  have h7 : A8 ^ 4 + B8 ^ 4 = 2 ^ 7 * (32 * B8 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 11 = 16 * 2 ^ 7 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq8, hpow, mul_assoc]
  have h16_8 : (A8 ^ 4 + B8 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 7 * (32 * B8 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 7) _
    exact Nat.mod_eq_zero_of_dvd (h7 ▸ this)
  obtain ⟨hA8e, hB8e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16_8
  obtain ⟨A9, hA9'⟩ := hA8e
  obtain ⟨B9, hB9'⟩ := hB8e
  have hA9 : A8 = 2 * A9 := by rw [hA9', two_mul]
  have hB9 : B8 = 2 * B9 := by rw [hB9', two_mul]
  have heq9src : (2 * A9) ^ 4 + (2 * B9) ^ 4 =
      2 ^ 7 * (64 * B9 + 1) ^ 13 := by
    have hC : 32 * B8 + 1 = 64 * B9 + 1 := by
      rw [hB9]
      have hmul : 32 * (2 * B9) = 64 * B9 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA9, ← hB9, ← hC]; exact h7
  have heq9 : 16 * (A9 ^ 4 + B9 ^ 4) = 2 ^ 7 * (64 * B9 + 1) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq9src
  have hlast : A9 ^ 4 + B9 ^ 4 = 8 * (64 * B9 + 1) ^ 13 := by
    have hpow : (2 : ℕ) ^ 7 = 16 * 8 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq9, hpow, mul_assoc]
  exact not_sum_fourth_eq_eight_mul_odd
    (odd_of_sixtyfour_mul_add_one B9) hlast

theorem B_odd_of_sol_gap8 {A B : ℕ} (h : is_gap8_sol A B) : Odd B := by
  rw [← Nat.not_even_iff_odd]
  intro hBeven
  exact no_sol_when_even_B h hBeven

/-! ## Size: `A > B` for `B > 0`; `A ≠ 0` on every solution -/

theorem two_mul_B_pow_four_lt_add_eight_pow (B : ℕ) :
    2 * B ^ 4 < (B + 8) ^ 13 := by
  have h6 : 6 ≤ B + 8 := Nat.le_add_left 6 B
  have h2 : 2 ≤ B + 8 := le_trans (by decide : 2 ≤ 8) h6
  have h2pow : 2 ≤ 2 ^ 9 := by decide
  have h29 : 2 ^ 9 ≤ (B + 8) ^ 9 := Nat.pow_le_pow_left h2 9
  have h2le : 2 ≤ (B + 8) ^ 9 := le_trans h2pow h29
  have hBlt : B < B + 8 := Nat.lt_add_of_pos_right (by decide : 0 < (8 : ℕ))
  have hB4 : B ^ 4 < (B + 8) ^ 4 :=
    Nat.pow_lt_pow_left hBlt (by decide : 4 ≠ 0)
  have hle : 2 * B ^ 4 ≤ (B + 8) ^ 9 * B ^ 4 :=
    Nat.mul_le_mul_right (B ^ 4) h2le
  have hposC : 0 < B + 8 := Nat.add_pos_right B (by decide : 0 < 8)
  have hpos9 : 0 < (B + 8) ^ 9 := Nat.pos_pow_of_pos 9 hposC
  have hlt : (B + 8) ^ 9 * B ^ 4 < (B + 8) ^ 9 * (B + 8) ^ 4 :=
    Nat.mul_lt_mul_of_pos_left hB4 hpos9
  have hsum : (B + 8) ^ 9 * (B + 8) ^ 4 = (B + 8) ^ 13 := by
    rw [← pow_add]
  rw [← hsum]
  exact lt_of_le_of_lt hle hlt

theorem A_gt_B_of_sol {A B : ℕ}
    (h : is_gap8_sol A B) (_hB : 0 < B) : B < A := by
  by_contra hle
  have hAB : A ≤ B := Nat.not_lt.mp hle
  have hA4 : A ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hAB 4
  have hsum : A ^ 4 + B ^ 4 ≤ 2 * B ^ 4 := by
    have := Nat.add_le_add hA4 (le_refl (B ^ 4))
    simpa [two_mul] using this
  have hlt := two_mul_B_pow_four_lt_add_eight_pow B
  have : A ^ 4 + B ^ 4 < (B + 8) ^ 13 := lt_of_le_of_lt hsum hlt
  exact (ne_of_lt this) h

theorem A_ne_zero_of_sol {A B : ℕ} (h : is_gap8_sol A B) : A ≠ 0 := by
  intro hA
  subst hA
  have heq : B ^ 4 = (B + 8) ^ 13 := by
    simpa [is_gap8_sol] using h
  by_cases hB : B = 0
  · subst hB
    exact (by decide : (0 : ℕ) ≠ 549755813888) heq
  · have hpos : 0 < B := Nat.pos_of_ne_zero hB
    have hB4pos : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hpos
    have hlt1 : B ^ 4 < 2 * B ^ 4 := by
      have : 1 * B ^ 4 < 2 * B ^ 4 :=
        Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hB4pos
      simpa using this
    have hlt2 := two_mul_B_pow_four_lt_add_eight_pow B
    exact (ne_of_lt (lt_trans hlt1 hlt2)) heq

theorem A_gt_one_of_sol_pos {A B : ℕ}
    (h : is_gap8_sol A B) (hB : 0 < B) : 1 < A :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) (A_gt_B_of_sol h hB)

/-! ## `mod 3`: `3 ∣ B` is a contradiction (`C ≡ 2`) -/

theorem fourth_pow_mod3 (a : ℕ) : a ^ 4 % 3 = 0 ∨ a ^ 4 % 3 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod3 a

theorem pow13_mod3 (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  BealMatveevBeal.BealGap1.pow13_mod3_eq_self c

theorem pow13_mod3_eq_self (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  pow13_mod3 c

/-- `C = B+8 ≡ 2 mod 3`, so `C¹³ ≡ 2`, while `A⁴ + B⁴ ≡ A⁴ ∈ {0,1}`. -/
theorem no_sol_when_three_dvd_B_gap8 {A B : ℕ}
    (h : is_gap8_sol A B) (h3 : 3 ∣ B) : False := by
  have hB4 : B ^ 4 % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h3 (by decide))
  have hC : (B + 8) % 3 = 2 := by
    have : B % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    rw [Nat.add_mod, this]
  have hC13 : (B + 8) ^ 13 % 3 = 2 := by
    rw [pow13_mod3, hC]
  have hsum : (A ^ 4 + B ^ 4) % 3 = (B + 8) ^ 13 % 3 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod3 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · rw [h1] at hsum
    exact absurd hsum (by decide)

theorem three_not_dvd_B_of_sol {A B : ℕ}
    (h : is_gap8_sol A B) : ¬ 3 ∣ B :=
  fun h3 => no_sol_when_three_dvd_B_gap8 h h3

/-! ## Coprimeness: `gcd(A,B) = 1` on every solution -/

theorem gcd_A_B_eq_one_of_sol {A B : ℕ}
    (h : is_gap8_sol A B) : Nat.gcd A B = 1 := by
  have hBodd := B_odd_of_sol_gap8 h
  set d := Nat.gcd A B
  have hdA : d ∣ A := Nat.gcd_dvd_left A B
  have hdB : d ∣ B := Nat.gcd_dvd_right A B
  have hdC13 : d ∣ (B + 8) ^ 13 := by
    have hA4 : d ∣ A ^ 4 := dvd_pow hdA (by decide)
    have hB4 : d ∣ B ^ 4 := dvd_pow hdB (by decide)
    have hsum : d ∣ A ^ 4 + B ^ 4 := Nat.dvd_add hA4 hB4
    simpa [is_gap8_sol] using (h ▸ hsum)
  have hgcd8 : Nat.gcd d (B + 8) ∣ 8 := by
    have h1 : Nat.gcd d (B + 8) ∣ B :=
      dvd_trans (Nat.gcd_dvd_left d (B + 8)) hdB
    have h2 : Nat.gcd d (B + 8) ∣ (B + 8) := Nat.gcd_dvd_right d (B + 8)
    exact dvd_trans (Nat.dvd_gcd h1 h2) (gcd_B_C_dvd_eight B)
  have hgcd1 : Nat.gcd d (B + 8) = 1 := by
    by_contra hne
    have hpos : 1 < Nat.gcd d (B + 8) :=
      Nat.lt_of_le_of_ne (Nat.succ_le_of_lt
        (Nat.gcd_pos_of_pos_right d (Nat.add_pos_right B (by decide : 0 < 8))))
        (Ne.symm hne)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hpos)
    have hp8 : p ∣ 8 := dvd_trans hpd hgcd8
    have hp2 : p = 2 := by
      have : p ∣ 2 ^ 3 := by simpa using hp8
      have h2 : p ∣ 2 := Nat.Prime.dvd_of_dvd_pow hp this
      exact ((Nat.dvd_prime Nat.prime_two).1 h2).resolve_left hp.ne_one
    have hd2 : 2 ∣ d := by
      have := Nat.gcd_dvd_left d (B + 8)
      rw [hp2] at hpd
      exact dvd_trans hpd this
    have h2B : 2 ∣ B := dvd_trans hd2 hdB
    exact absurd (even_iff_two_dvd.2 h2B) (Nat.not_even_iff_odd.2 hBodd)
  have hcop : Nat.Coprime d (B + 8) := hgcd1
  have hcop13 : Nat.Coprime d ((B + 8) ^ 13) := hcop.pow_right 13
  have hd1 : d ∣ 1 := by
    have := Nat.dvd_gcd (dvd_refl d) hdC13
    rwa [show Nat.gcd d ((B + 8) ^ 13) = 1 from hcop13] at this
  exact Nat.eq_one_of_dvd_one hd1

theorem gcd_A_B_eq_one_of_sol_gap8 {A B : ℕ}
    (h : is_gap8_sol A B) : Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_sol h

theorem coprime_of_sol_gap8 {A B : ℕ}
    (h : is_gap8_sol A B) : Nat.Coprime A B :=
  gcd_A_B_eq_one_of_sol h

theorem gcd_A_B_eq_one_of_remaining_gap8 {A B : ℕ}
    (h : is_gap8_sol A B) (_h3 : ¬ 3 ∣ B) (_h5 : ¬ 5 ∣ B) :
    Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_sol h

theorem coprime_of_remaining_gap8 {A B : ℕ}
    (h : is_gap8_sol A B) (h3 : ¬ 3 ∣ B) (h5 : ¬ 5 ∣ B) :
    Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_remaining_gap8 h h3 h5

/-! ## `mod 5`: `5 ∣ B` is a contradiction (`C ≡ 3`) -/

theorem fourth_pow_mod5 (a : ℕ) : a ^ 4 % 5 = 0 ∨ a ^ 4 % 5 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod5 a

theorem pow13_mod5 (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  BealMatveevBeal.BealGap1.pow13_mod5_eq_self c

theorem pow13_mod5_eq_self (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  pow13_mod5 c

/-- `C = B+8 ≡ 3 mod 5`, so `C¹³ ≡ 3`, while `A⁴ + B⁴ ≡ A⁴ ∈ {0,1}`. -/
theorem no_sol_when_five_dvd_B_gap8 {A B : ℕ}
    (h : is_gap8_sol A B) (h5 : 5 ∣ B) : False := by
  have hB4 : B ^ 4 % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h5 (by decide))
  have hC : (B + 8) % 5 = 3 := by
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [Nat.add_mod, this]
  have hC13 : (B + 8) ^ 13 % 5 = 3 := by
    rw [pow13_mod5, hC]
  have hsum : (A ^ 4 + B ^ 4) % 5 = (B + 8) ^ 13 % 5 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod5 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · rw [h1] at hsum
    exact absurd hsum (by decide)

theorem five_not_dvd_B_of_sol {A B : ℕ}
    (h : is_gap8_sol A B) : ¬ 5 ∣ B :=
  fun h5 => no_sol_when_five_dvd_B_gap8 h h5

/-! ## `mod 7`: `7 ∣ B` is compatible (`C ≡ 1`), forces `7 ∤ A` -/

theorem fourth_pow_mod7 (a : ℕ) :
    a ^ 4 % 7 = 0 ∨ a ^ 4 % 7 = 1 ∨ a ^ 4 % 7 = 2 ∨ a ^ 4 % 7 = 4 :=
  BealMatveevBeal.BealGap7.fourth_pow_mod7 a

theorem pow13_mod7 (c : ℕ) : c ^ 13 % 7 = c % 7 :=
  BealMatveevBeal.BealGap7.pow13_mod7 c

theorem pow13_mod7_eq_self (c : ℕ) : c ^ 13 % 7 = c % 7 :=
  pow13_mod7 c

/-- `C = B+8 ≡ 1 mod 7`, so `C¹³ ≡ 1` and `A⁴ ≡ 1`. No contradiction.
    Do **not** prove `no_sol_when_seven_dvd_B` here. -/
theorem A_pow_four_mod7_eq_one_of_seven_dvd_B {A B : ℕ}
    (h : is_gap8_sol A B) (h7 : 7 ∣ B) : A ^ 4 % 7 = 1 := by
  have hB4 : B ^ 4 % 7 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h7 (by decide))
  have hC : (B + 8) % 7 = 1 := by
    have : B % 7 = 0 := Nat.mod_eq_zero_of_dvd h7
    rw [Nat.add_mod, this]
  have hC13 : (B + 8) ^ 13 % 7 = 1 := by
    rw [pow13_mod7, hC]
  have hsum : (A ^ 4 + B ^ 4) % 7 = (B + 8) ^ 13 % 7 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 | h2 | h4 := fourth_pow_mod7 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · exact h1
  · rw [h2] at hsum
    exact absurd hsum (by decide)
  · rw [h4] at hsum
    exact absurd hsum (by decide)

theorem not_seven_dvd_A_of_seven_dvd_B {A B : ℕ}
    (h : is_gap8_sol A B) (hB : 7 ∣ B) : ¬ 7 ∣ A := by
  intro hA
  have : 7 ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
  rw [gcd_A_B_eq_one_of_sol h] at this
  exact (by decide : ¬ (7 ∣ 1)) this

/-! ## Linear form `Λ = 4 log A − 13 log(B+8)` -/

noncomputable def Lambda_gap8 (A B : ℕ) : ℝ :=
  4 * log (A : ℝ) - 13 * log ((B + 8 : ℕ) : ℝ)

theorem A_pow_four_eq_sub {A B : ℕ} (h : is_gap8_sol A B) :
    A ^ 4 = (B + 8) ^ 13 - B ^ 4 := by
  rw [← h, add_comm, Nat.add_sub_cancel_left]

theorem A_pow_real_add {A B : ℕ} (h : is_gap8_sol A B) :
    (A : ℝ) ^ 4 + (B : ℝ) ^ 4 = ((B + 8 : ℕ) : ℝ) ^ 13 := by
  have h' : ((A ^ 4 + B ^ 4 : ℕ) : ℝ) = (((B + 8) ^ 13 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [Nat.cast_add, Nat.cast_pow] using h'

theorem A_pow_pos_of_sol {A B : ℕ} (h : is_gap8_sol A B) :
    (0 : ℝ) < (A : ℝ) ^ 4 := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  exact pow_pos hApos 4

theorem Lambda_gap8_eq_log_div {A B : ℕ}
    (h : is_gap8_sol A B) :
    Lambda_gap8 A B =
      log ((A : ℝ) ^ 4 / ((B + 8 : ℕ) : ℝ) ^ 13) := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hCpos : (0 : ℝ) < ((B + 8 : ℕ) : ℝ) := by
    have : 0 < B + 8 := Nat.add_pos_right B (by decide : 0 < 8)
    exact_mod_cast this
  unfold Lambda_gap8
  have h4 : (4 : ℝ) * log (A : ℝ) = log ((A : ℝ) ^ 4) :=
    (Real.log_pow (A : ℝ) 4).symm
  have h13 : (13 : ℝ) * log ((B + 8 : ℕ) : ℝ) =
      log (((B + 8 : ℕ) : ℝ) ^ 13) :=
    (Real.log_pow ((B + 8 : ℕ) : ℝ) 13).symm
  rw [h4, h13, Real.log_div (pow_pos hApos 4).ne' (pow_pos hCpos 13).ne']

theorem abs_Lambda_gap8_eq_log_one_plus {A B : ℕ}
    (h : is_gap8_sol A B) (hB : 0 < B) :
    |Lambda_gap8 A B| = log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hu : (0 : ℝ) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    div_pos (pow_pos hBpos 4) hA4pos
  have hsum := A_pow_real_add h
  have hratio :
      (A : ℝ) ^ 4 / ((B + 8 : ℕ) : ℝ) ^ 13 =
        1 / (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    have hne : (A : ℝ) ^ 4 ≠ 0 := hA4pos.ne'
    have hden :
        (1 : ℝ) + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 =
          ((A : ℝ) ^ 4 + (B : ℝ) ^ 4) / (A : ℝ) ^ 4 := by
      field_simp [hne]
    rw [hden, one_div_div, hsum]
  have hΛ := Lambda_gap8_eq_log_div h
  have h1u : (0 : ℝ) < 1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    add_pos_of_nonneg_of_pos zero_le_one hu
  have hlog :
      Lambda_gap8 A B = -log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    rw [hΛ, hratio, Real.log_div one_ne_zero h1u.ne', log_one, zero_sub]
  rw [hlog, abs_neg, abs_of_nonneg (log_nonneg (le_of_lt (lt_add_of_pos_right 1 hu)))]

theorem abs_Lambda_gap8_le_ratio {A B : ℕ}
    (h : is_gap8_sol A B) (hB : 0 < B) :
    |Lambda_gap8 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
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
  rwa [abs_Lambda_gap8_eq_log_one_plus h hB]

theorem B_pow_five_add_B_pow_four_lt_add_eight_pow {B : ℕ} (_hB : 0 < B) :
    (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 8 : ℕ) : ℝ) ^ 13 := by
  have hx : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : ((B + 8 : ℕ) : ℝ) = (B : ℝ) + 6 := by
    rw [Nat.cast_add]
    norm_num
  have h5 : (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 8 : ℕ) : ℝ) ^ 5 := by
    rw [hC]
    have hexp : ((B : ℝ) + 6) ^ 5 =
        (B : ℝ) ^ 5 + 40 * (B : ℝ) ^ 4 + 640 * (B : ℝ) ^ 3 +
          5120 * (B : ℝ) ^ 2 + 20480 * (B : ℝ) + 32768 := by
      ring
    have h3 : (0 : ℝ) ≤ (B : ℝ) ^ 3 := pow_nonneg hx 3
    have h2 : (0 : ℝ) ≤ (B : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hexp, h3, h2, hx]
  have hC1 : (1 : ℝ) ≤ ((B + 8 : ℕ) : ℝ) := by
    have : 1 ≤ B + 8 := le_trans (by decide : 1 ≤ 8) (Nat.le_add_left 6 B)
    exact_mod_cast this
  have h513 : ((B + 8 : ℕ) : ℝ) ^ 5 ≤ ((B + 8 : ℕ) : ℝ) ^ 13 :=
    pow_le_pow_right hC1 (by decide : (5 : ℕ) ≤ 13)
  exact lt_of_lt_of_le h5 h513

theorem A_pow_gt_B_pow_five {A B : ℕ}
    (h : is_gap8_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 5 < (A : ℝ) ^ 4 := by
  have hA4 : (A : ℝ) ^ 4 =
      ((B + 8 : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 := by
    linarith [A_pow_real_add h]
  have hsum := B_pow_five_add_B_pow_four_lt_add_eight_pow hB
  linarith [hA4, hsum]

theorem ratio_lt_inv_B {A B : ℕ}
    (h : is_gap8_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 4 / (A : ℝ) ^ 4 < 1 / (B : ℝ) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hgt := A_pow_gt_B_pow_five h hB
  have : (B : ℝ) ^ 4 * (B : ℝ) < (A : ℝ) ^ 4 := by
    have : (B : ℝ) ^ 5 = (B : ℝ) ^ 4 * (B : ℝ) := by ring
    rwa [this] at hgt
  rw [div_lt_div_iff hA4pos hBpos, one_mul]
  exact this

theorem abs_Lambda_gap8_lt_inv_B {A B : ℕ}
    (h : is_gap8_sol A B) (hB : 0 < B) :
    |Lambda_gap8 A B| < 1 / (B : ℝ) :=
  lt_of_le_of_lt (abs_Lambda_gap8_le_ratio h hB) (ratio_lt_inv_B h hB)

theorem A_pow_lt_C_pow {A B : ℕ}
    (h : is_gap8_sol A B) (hB : 0 < B) :
    (A : ℝ) ^ 4 < ((B + 8 : ℕ) : ℝ) ^ 13 := by
  have hB4 : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hB
  have hlt : A ^ 4 < (B + 8) ^ 13 :=
    calc
      A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
      _ = (B + 8) ^ 13 := h
  exact_mod_cast hlt

/-! ## Log-method no-go (`C1 ≥ 1` loses to `B⁴/A⁴`) -/

theorem logA_gt_thirteen_of_B_ge_B0 {A B : ℕ}
    (h : is_gap8_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
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

/-- `exp(−C1 log A log(B+8)) < B⁴/A⁴` for every `C1 ≥ 1` on
    a gap-8 solution with `B ≥ B0`. Same cutoff as `62383af`:
    `C1 < 1` would be needed. -/
theorem hGen_exp_lt_ratio_gap8
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {A B : ℕ} (hsol : is_gap8_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + 8 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  set a : ℝ := log (A : ℝ)
  set c : ℝ := log ((B + 8 : ℕ) : ℝ)
  set C : ℝ := ((B + 8 : ℕ) : ℝ)
  have hAgt1 : 1 < A := A_gt_one_of_sol_pos hsol hB
  have hCgt1 : 1 < B + 8 :=
    lt_of_lt_of_le (by decide : 1 < 8) (Nat.le_add_left 6 B)
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (0 : ℕ) < A := lt_trans Nat.zero_lt_one hAgt1
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C := by
    have : 0 < B + 8 := Nat.add_pos_right B (by decide : 0 < 8)
    have : (0 : ℝ) < ((B + 8 : ℕ) : ℝ) := by exact_mod_cast this
    simpa [C] using this
  have hCgt : (1 : ℝ) < C := by
    have : (1 : ℝ) < ((B + 8 : ℕ) : ℝ) := by exact_mod_cast hCgt1
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

theorem C1_floor_hGen_loses_gap8 {A B : ℕ}
    (hsol : is_gap8_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + 8 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio_gap8
    (le_of_lt (by
      simpa [C1_floor_eq_logs] using
        BealMatveevBeal.MatveevThreeLogs.C1_floor_gt_one))
    hsol hB hB0

/-! ## Floor form / LLL no-go (`B+8`) -/

noncomputable def floorFormThird_gap8 (C : ℝ) (A B : ℕ) : ℝ :=
  (4 : ℝ) * ⌊C * log (A : ℝ)⌋ - 13 * ⌊C * log ((B + 8 : ℕ) : ℝ)⌋

/-- `|4⌊C log A⌋ − 13⌊C log(B+8)⌋ − C Λ| < 17` for every real `C`. -/
theorem floor_form_approx_of_C_gap8 (C : ℝ) (A B : ℕ) :
    |floorFormThird_gap8 C A B - C * Lambda_gap8 A B| < 17 := by
  set a : ℝ := C * log (A : ℝ)
  set cval : ℝ := C * log ((B + 8 : ℕ) : ℝ)
  have hΛ : C * Lambda_gap8 A B = 4 * a - 13 * cval := by
    simp only [Lambda_gap8, a, cval]
    ring
  have hft : floorFormThird_gap8 C A B = (4 : ℝ) * ⌊a⌋ - 13 * ⌊cval⌋ := rfl
  have hform :
      floorFormThird_gap8 C A B - C * Lambda_gap8 A B =
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

theorem floor_form_third_abs_lt_gap8 {C : ℝ} (hC : 0 < C) (A B : ℕ) :
    |floorFormThird_gap8 C A B| < 17 + C * |Lambda_gap8 A B| := by
  have happ := floor_form_approx_of_C_gap8 C A B
  have hmul : |C * Lambda_gap8 A B| = C * |Lambda_gap8 A B| := by
    rw [abs_mul, abs_of_pos hC]
  have := abs_sub_abs_le_abs_sub
    (floorFormThird_gap8 C A B) (C * Lambda_gap8 A B)
  linarith [happ, this, hmul]

/-- No scaling `C > 0` yields a Baker–Davenport witness
    `r > 17 + C/B0` on a gap-8 solution with `B ≥ B0`. -/
theorem hLLL_method_fails_gap8 :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        is_gap8_sol A B →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |floorFormThird_gap8 C A B| := by
  intro C hC A B hsol hB hB0
  rintro ⟨r, hgt, hle⟩
  have htri := floor_form_third_abs_lt_gap8 hC A B
  have hLam := abs_Lambda_gap8_lt_inv_B hsol hB
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hBle : (B0_nat : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hB0
  have hCΛ : C * |Lambda_gap8 A B| < C / (B0_nat : ℝ) := by
    have hmid : C * |Lambda_gap8 A B| < C * (1 / (B : ℝ)) :=
      mul_lt_mul_of_pos_left hLam hC
    have hrew : C * (1 / (B : ℝ)) = C / (B : ℝ) := mul_one_div _ _
    have hCB : C / (B : ℝ) ≤ C / (B0_nat : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hC) hB0pos hBle
    linarith [hmid, hrew, hCB]
  have hthird : |floorFormThird_gap8 C A B| < 17 + C / (B0_nat : ℝ) := by
    linarith [htri, hCΛ]
  linarith [hgt, hle, hthird]

theorem no_uniform_c_cubic_in_N_gap8 :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (BealMatveevBeal.MatveevThreeLogs.coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) :=
  BealMatveevBeal.MatveevThreeLogs.no_uniform_c_cubic_in_N

theorem coeffCount3_zero_ten_ten_ten_gap8 :
    BealMatveevBeal.MatveevThreeLogs.coeffCount3 0 10 10 10 = 1331 :=
  BealMatveevBeal.MatveevThreeLogs.coeffCount3_zero_ten_ten_ten

theorem no_uniform_c_easy_half_gap8 :
    (1 / 2 : ℝ) * 1 * 1 < 242 := by
  norm_num

/-! ## `hGen_gap8` / `hLLL_gap8` stay `def Prop` -/

/-- Matveev 2000 Theorem 1.4, n=2, displayed `C1_floor` exponential
    on a gap-8 solution. Not in Mathlib 4.12. Instantiating it at
    `B ≥ B0` does not beat `B⁴/A⁴`. -/
def hGen_gap8 : Prop :=
  ∀ A B : ℕ,
    is_gap8_sol A B →
      0 < B →
        |Lambda_gap8 A B| >
          exp (-(C1_floor : ℝ) * log (A : ℝ) *
            log ((B + 8 : ℕ) : ℝ))

/-- Bugeaud / LLL close for gap-8: ratio upper bound ⇒ `B ≤ B0`.
    The displayed lattice does not inhabit it. -/
def hLLL_gap8 : Prop :=
  (∀ A B : ℕ, is_gap8_sol A B → 0 < B →
      |Lambda_gap8 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4) →
    baker_bound_gap8

def baker_bound_gap8_of_hGen_hLLL : Prop :=
  hGen_gap8 → hLLL_gap8 → baker_bound_gap8

def baker_bound_gap8_of_hGen_hLLL_gap8 : Prop :=
  baker_bound_gap8_of_hGen_hLLL

/-! ## Combined unconditional no-go (no Darmon–Merel axiom) -/

/-- Log and LLL methods lose on `B ≥ B0`. Remaining solutions are
    coprime with `A > B0`, `B` odd, `A` even. `3 ∣ B` and
    `5 ∣ B` are impossible. `7 ∣ B` is compatible and forces
    `7 ∤ A`. Darmon–Merel `(4,4,13)` would be refuted by any
    such solution. `baker_bound_gap8` stays uninhabited as a
    named theorem. -/
theorem baker_bound_gap8_unconditional_nogo {A B : ℕ}
    (hsol : is_gap8_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + 8 : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (∀ C : ℝ, 0 < C →
      ¬ ∃ r : ℝ,
        17 + C / (B0_nat : ℝ) < r ∧
          r ≤ |floorFormThird_gap8 C A B|) ∧
    Nat.Coprime A B ∧
    B0_nat < A ∧
    Odd B ∧
    Even A ∧
    ¬ 3 ∣ B ∧
    ¬ 5 ∣ B ∧
    (7 ∣ B → ¬ 7 ∣ A) ∧
    (darmon_merel_44_13_no_coprime → False) := by
  refine ⟨?_, ?_, coprime_of_sol_gap8 hsol, ?_,
    B_odd_of_sol_gap8 hsol, A_even_of_sol_gap8 hsol,
    three_not_dvd_B_of_sol hsol, five_not_dvd_B_of_sol hsol, ?_, ?_⟩
  · intro C1 hC1
    exact hGen_exp_lt_ratio_gap8 hC1 hsol hB hB0
  · intro C hC
    exact hLLL_method_fails_gap8 C hC A B hsol hB hB0
  · exact Nat.lt_of_le_of_lt hB0 (A_gt_B_of_sol hsol hB)
  · intro h7
    exact not_seven_dvd_A_of_seven_dvd_B hsol h7
  · intro hDM
    have hA0 : A = 0 ∨ B = 0 :=
      hDM A B (B + 8) (coprime_of_sol_gap8 hsol) hsol
    cases hA0 with
    | inl hA => exact A_ne_zero_of_sol hsol hA
    | inr hB0' => exact (ne_of_gt hB) hB0'

/-! ## Axiom-relative close (reuses `BealTrueV25`, no new axiom) -/

/-- Every gap-8 solution is impossible relative to
    `darmon_merel_4413_axiom`. Unlike gap-1 there is no `(1,0)`. -/
theorem no_gap8_of_axiom {A B : ℕ}
    (hsol : is_gap8_sol A B) : False := by
  have hDM := BealMatveevBeal.BealTrueV25.darmon_merel_4413_axiom
  have hA0 : A = 0 ∨ B = 0 :=
    hDM A B (B + 8) (coprime_of_sol_gap8 hsol) hsol
  cases hA0 with
  | inl hA => exact A_ne_zero_of_sol hsol hA
  | inr hB0 =>
      subst hB0
      exact no_sol_when_even_B hsol (by decide : Even 0)

/-- Vacuous `B ≤ B0` for every gap-8 solution, relative to the
    existing Darmon–Merel axiom. Not named `baker_bound_gap8`. -/
theorem baker_bound_gap8_true {A B : ℕ}
    (hsol : is_gap8_sol A B) : B ≤ B0_nat :=
  (no_gap8_of_axiom hsol).elim

theorem baker_bound_gap8_true_of_axiom {A B : ℕ}
    (hsol : is_gap8_sol A B) : B ≤ B0_nat :=
  baker_bound_gap8_true hsol

#check C1_floor_eq
#check B0_nat_eq
#check not_gap8_one_zero
#check gcd_B_C_eq_gcd_eight
#check gcd_B_C_dvd_eight
#check gcd_A_B_eq_one_of_sol
#check coprime_of_sol_gap8
#check B_odd_of_sol_gap8
#check A_even_of_sol_gap8
#check no_sol_when_even_B
#check A_gt_B_of_sol
#check no_sol_when_three_dvd_B_gap8
#check no_sol_when_five_dvd_B_gap8
#check A_pow_four_mod7_eq_one_of_seven_dvd_B
#check not_seven_dvd_A_of_seven_dvd_B
#check coprime_of_remaining_gap8
#check hGen_exp_lt_ratio_gap8
#check C1_floor_hGen_loses_gap8
#check floor_form_approx_of_C_gap8
#check hLLL_method_fails_gap8
#check no_uniform_c_cubic_in_N_gap8
#check no_uniform_c_easy_half_gap8
#check hGen_gap8
#check hLLL_gap8
#check baker_bound_gap8_of_hGen_hLLL
#check baker_bound_gap8_unconditional_nogo
#check baker_bound_gap8
#check no_gap8_of_axiom
#check baker_bound_gap8_true
#check baker_bound_gap8_true_of_axiom
#print axioms gcd_A_B_eq_one_of_sol
#print axioms B_odd_of_sol_gap8
#print axioms no_sol_when_even_B
#print axioms no_sol_when_three_dvd_B_gap8
#print axioms no_sol_when_five_dvd_B_gap8
#print axioms A_pow_four_mod7_eq_one_of_seven_dvd_B
#print axioms hGen_exp_lt_ratio_gap8
#print axioms C1_floor_hGen_loses_gap8
#print axioms hLLL_method_fails_gap8
#print axioms baker_bound_gap8_unconditional_nogo
#print axioms no_gap8_of_axiom
#print axioms baker_bound_gap8_true

end BealMatveevBeal.BealGap8
