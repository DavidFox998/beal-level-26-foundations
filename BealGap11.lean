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
import BealGap10

/-!
# Gap-11 `A⁴ + B⁴ = (B+11)¹³` (not a `B ≤ 10⁶` close)

Successor of `d72316b` (`v24-v24x-final-gap10-nogo`).
`C = B+11` so `gcd(B,C) ∣ 11`. Parity is gap-1/5/7/9, not
gap-2/4/6/8/10: odd `B` makes `C` even, so `C¹³ ≡ 0` mod 16
while `A⁴ + B⁴ ≡ 1` or `2`. Thus `B` is even and `A` is odd.
`(1,0)` is **not** a solution (`1 ≠ 11¹³`). Unlike gap-9,
`3 ∣ B` is a residue kill, not a 3-descent: `11 ≡ 2 mod 3`
so `C ≡ 2`, `C¹³ ≡ 2`, while `A⁴ ∈ {0,1}` (same as gap-2
`7a1c53b` / gap-5 `59d8a4a` / gap-8 `bf43afc`). `11 ∣ B`
forces `11 ∣ A` and then an 11-descent dies: `A=11A₁ B=11B₁
C=11(B₁+1)` gives `A₁⁴+B₁⁴=11⁹ C₁¹³` (`11⁹ = 2357947691`),
fourth powers mod 11 are `{0,1,3,4,5,9}` and sum `0` only
`0+0`, so three further `/11` leave `1331 X = (B₁+1)¹³`
while `B₁+1 ≡ 1 mod 11`. `5 ∣ B` is compatible (`C ≡ 1
mod 5`, `A⁴ ≡ 1`). `7 ∣ B` is compatible (`C ≡ 4 mod 7`,
`A⁴ ≡ 4`; `3⁴ = 81 ≡ 4`). Remaining solutions are coprime
(`p ∣ A,B` ⇒ `p ∣ 11`, but `11 ∤ B`) and pure Darmon–Merel
signature `(4,4,13)`.

`hGen_gap11` / `hLLL_gap11` stay `def Prop`. Every `C1 ≥ 1`
loses to `B⁴/A⁴` on `B ≥ B0`; no scaling yields a
Baker–Davenport witness above `17 + C/B0`. Named theorem
`baker_bound_gap11` stays a `def Prop`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

set_option maxHeartbeats 800000

open Real

namespace BealMatveevBeal.BealGap11

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_logs :
    C1_floor = BealMatveevBeal.MatveevThreeLogs.C1_floor := rfl

theorem B0_nat_eq_logs :
    B0_nat = BealMatveevBeal.MatveevThreeLogs.B0_nat := rfl

/-! ## Gap-11 equation -/

def is_gap11_sol (A B : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = (B + 11) ^ 13

/-- Kernel Baker bound for gap-11. Stays a `def Prop`. -/
def baker_bound_gap11 : Prop :=
  ∀ A B : ℕ, is_gap11_sol A B → B ≤ B0_nat

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealTrueV25.darmon_merel_44_13_no_coprime

/-! ## `(1,0)` is not a solution -/

theorem not_gap11_one_zero : ¬ is_gap11_sol 1 0 := by
  unfold is_gap11_sol
  decide

theorem odd_eleven : Odd (11 : ℕ) := ⟨5, rfl⟩

theorem prime_eleven : Nat.Prime 11 := by decide

/-! ## `gcd(B, B+11) = gcd(B, 11)` divides `11` -/

theorem gcd_B_C_eq_gcd_eleven (B : ℕ) :
    Nat.gcd B (B + 11) = Nat.gcd B 11 := by
  rw [Nat.gcd_comm B (B + 11), Nat.add_comm B 11]
  exact (Nat.gcd_add_self_left (11 : ℕ) B).trans (Nat.gcd_comm 11 B)

theorem gcd_B_C_dvd_eleven (B : ℕ) : Nat.gcd B (B + 11) ∣ 11 := by
  rw [gcd_B_C_eq_gcd_eleven]
  exact Nat.gcd_dvd_right B 11

theorem gcd_B_C_dvd_eleven_gap11 (B : ℕ) : Nat.gcd B (B + 11) ∣ 11 :=
  gcd_B_C_dvd_eleven B

/-! ## Parity: `B` is even, `A` is odd (gap-1/5/7/9, opposite gap-2/4/6/8/10) -/

theorem B_even_of_sol_gap11 {A B : ℕ} (h : is_gap11_sol A B) : Even B := by
  by_contra hne
  have hBodd : Odd B := Nat.not_even_iff_odd.1 hne
  have hCeven : Even (B + 11) := hBodd.add_odd odd_eleven
  have h16C : 16 ∣ (B + 11) ^ 4 :=
    BealCatalanZsig.even_pow_four_dvd_sixteen hCeven
  have h16R : 16 ∣ (B + 11) ^ 13 :=
    dvd_trans h16C (pow_dvd_pow (B + 11) (by decide : 4 ≤ 13))
  have hR : (B + 11) ^ 13 % 16 = 0 := Nat.mod_eq_zero_of_dvd h16R
  have hB4 : B ^ 4 % 16 = 1 :=
    BealCatalanZsig.odd_pow_four_mod_sixteen hBodd
  by_cases hA : Even A
  · have hA4 : A ^ 4 % 16 = 0 :=
      Nat.mod_eq_zero_of_dvd
        (BealCatalanZsig.even_pow_four_dvd_sixteen hA)
    have hL : (A ^ 4 + B ^ 4) % 16 = 1 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + 11) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (1 : ℕ) ≠ 0) this
  · have hAodd : Odd A := Nat.not_even_iff_odd.1 hA
    have hA4 : A ^ 4 % 16 = 1 :=
      BealCatalanZsig.odd_pow_four_mod_sixteen hAodd
    have hL : (A ^ 4 + B ^ 4) % 16 = 2 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + 11) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (2 : ℕ) ≠ 0) this

theorem A_odd_of_sol_gap11 {A B : ℕ} (h : is_gap11_sol A B) : Odd A := by
  have hBeven := B_even_of_sol_gap11 h
  have hCodd : Odd (B + 11) := hBeven.add_odd odd_eleven
  have hC13 : Odd ((B + 11) ^ 13) := hCodd.pow
  have hB4 : Even (B ^ 4) := (Nat.even_pow' (by decide : 4 ≠ 0)).2 hBeven
  rw [← Nat.not_even_iff_odd]
  intro hAeven
  have hA4 : Even (A ^ 4) := (Nat.even_pow' (by decide : 4 ≠ 0)).2 hAeven
  have hL : Even (A ^ 4 + B ^ 4) := hA4.add hB4
  exact (Nat.not_even_iff_odd.2 (h ▸ hC13)) hL

/-! ## Size: `A > B` for `B > 0`; `A ≠ 0` on every solution -/

theorem two_mul_B_pow_four_lt_add_eleven_pow (B : ℕ) :
    2 * B ^ 4 < (B + 11) ^ 13 := by
  have h11le : 11 ≤ B + 11 := Nat.le_add_left 11 B
  have h2 : 2 ≤ B + 11 := le_trans (by decide : 2 ≤ 11) h11le
  have h2pow : 2 ≤ 2 ^ 9 := by decide
  have h29 : 2 ^ 9 ≤ (B + 11) ^ 9 := Nat.pow_le_pow_left h2 9
  have h2le : 2 ≤ (B + 11) ^ 9 := le_trans h2pow h29
  have hBlt : B < B + 11 := Nat.lt_add_of_pos_right (by decide : 0 < (11 : ℕ))
  have hB4 : B ^ 4 < (B + 11) ^ 4 :=
    Nat.pow_lt_pow_left hBlt (by decide : 4 ≠ 0)
  have hle : 2 * B ^ 4 ≤ (B + 11) ^ 9 * B ^ 4 :=
    Nat.mul_le_mul_right (B ^ 4) h2le
  have hposC : 0 < B + 11 := Nat.add_pos_right B (by decide : 0 < 11)
  have hpos9 : 0 < (B + 11) ^ 9 := Nat.pos_pow_of_pos 9 hposC
  have hlt : (B + 11) ^ 9 * B ^ 4 < (B + 11) ^ 9 * (B + 11) ^ 4 :=
    Nat.mul_lt_mul_of_pos_left hB4 hpos9
  have hsum : (B + 11) ^ 9 * (B + 11) ^ 4 = (B + 11) ^ 13 := by
    rw [← pow_add]
  rw [← hsum]
  exact lt_of_le_of_lt hle hlt

theorem A_gt_B_of_sol {A B : ℕ}
    (h : is_gap11_sol A B) (_hB : 0 < B) : B < A := by
  by_contra hle
  have hAB : A ≤ B := Nat.not_lt.mp hle
  have hA4 : A ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hAB 4
  have hsum : A ^ 4 + B ^ 4 ≤ 2 * B ^ 4 := by
    have := Nat.add_le_add hA4 (le_refl (B ^ 4))
    simpa [two_mul] using this
  have hlt := two_mul_B_pow_four_lt_add_eleven_pow B
  have : A ^ 4 + B ^ 4 < (B + 11) ^ 13 := lt_of_le_of_lt hsum hlt
  exact (ne_of_lt this) h

theorem A_ne_zero_of_sol {A B : ℕ} (h : is_gap11_sol A B) : A ≠ 0 := by
  intro hA
  subst hA
  have heq : B ^ 4 = (B + 11) ^ 13 := by
    simpa [is_gap11_sol] using h
  by_cases hB : B = 0
  · subst hB
    exact (by decide : (0 : ℕ) ≠ 34522712143931) heq
  · have hpos : 0 < B := Nat.pos_of_ne_zero hB
    have hB4pos : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hpos
    have hlt1 : B ^ 4 < 2 * B ^ 4 := by
      have : 1 * B ^ 4 < 2 * B ^ 4 :=
        Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hB4pos
      simpa using this
    have hlt2 := two_mul_B_pow_four_lt_add_eleven_pow B
    exact (ne_of_lt (lt_trans hlt1 hlt2)) heq

theorem A_gt_one_of_sol_pos {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 0 < B) : 1 < A :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) (A_gt_B_of_sol h hB)

/-! ## `mod 3`: `3 ∣ B` is a residue contradiction (`C ≡ 2`) -/

theorem fourth_pow_mod3 (a : ℕ) : a ^ 4 % 3 = 0 ∨ a ^ 4 % 3 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod3 a

theorem pow13_mod3 (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  BealMatveevBeal.BealGap1.pow13_mod3_eq_self c

theorem pow13_mod3_eq_self (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  pow13_mod3 c

/-- `C = B+11 ≡ 2 mod 3`, so `C¹³ ≡ 2`, while `A⁴ + B⁴ ≡ A⁴ ∈ {0,1}`. -/
theorem no_sol_when_three_dvd_B_gap11 {A B : ℕ}
    (h : is_gap11_sol A B) (h3 : 3 ∣ B) : False := by
  have hB4 : B ^ 4 % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h3 (by decide))
  have hC : (B + 11) % 3 = 2 := by
    have : B % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    rw [Nat.add_mod, this]
  have hC13 : (B + 11) ^ 13 % 3 = 2 := by
    rw [pow13_mod3, hC]
  have hsum : (A ^ 4 + B ^ 4) % 3 = (B + 11) ^ 13 % 3 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod3 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · rw [h1] at hsum
    exact absurd hsum (by decide)

theorem three_not_dvd_B_of_sol {A B : ℕ}
    (h : is_gap11_sol A B) : ¬ 3 ∣ B :=
  fun h3 => no_sol_when_three_dvd_B_gap11 h h3

/-! ## `mod 11`: fourth powers are `0,1,3,4,5,9`; sum `0` only `0+0` -/

theorem fourth_pow_mod11 (a : ℕ) :
    a ^ 4 % 11 = 0 ∨ a ^ 4 % 11 = 1 ∨ a ^ 4 % 11 = 3 ∨
      a ^ 4 % 11 = 4 ∨ a ^ 4 % 11 = 5 ∨ a ^ 4 % 11 = 9 := by
  rw [Nat.pow_mod]
  have hlt : a % 11 < 11 := Nat.mod_lt a (by decide)
  interval_cases a % 11 <;> decide

theorem eleven_dvd_of_fourth_pow_mod_zero {n : ℕ}
    (h : n ^ 4 % 11 = 0) : 11 ∣ n :=
  Nat.Prime.dvd_of_dvd_pow prime_eleven (Nat.dvd_of_mod_eq_zero h)

theorem residues_sum_mod11_zero {x y : ℕ}
    (hx : x = 0 ∨ x = 1 ∨ x = 3 ∨ x = 4 ∨ x = 5 ∨ x = 9)
    (hy : y = 0 ∨ y = 1 ∨ y = 3 ∨ y = 4 ∨ y = 5 ∨ y = 9)
    (h : (x + y) % 11 = 0) : x = 0 ∧ y = 0 := by
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases hy with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact ⟨rfl, rfl⟩ | exact absurd h (by decide)

theorem both_eleven_dvd_of_sum_fourth_mod11_zero {X Y : ℕ}
    (h : (X ^ 4 + Y ^ 4) % 11 = 0) : 11 ∣ X ∧ 11 ∣ Y := by
  have hsum : (X ^ 4 + Y ^ 4) % 11 = (X ^ 4 % 11 + Y ^ 4 % 11) % 11 :=
    Nat.add_mod _ _ _
  rw [hsum] at h
  have hxy := residues_sum_mod11_zero (fourth_pow_mod11 X) (fourth_pow_mod11 Y) h
  exact ⟨eleven_dvd_of_fourth_pow_mod_zero hxy.1,
    eleven_dvd_of_fourth_pow_mod_zero hxy.2⟩

theorem sum_fourth_of_mul_eleven (x y : ℕ) :
    (11 * x) ^ 4 + (11 * y) ^ 4 = 14641 * (x ^ 4 + y ^ 4) := by
  have hx : (11 * x) ^ 4 = 14641 * x ^ 4 := by
    rw [mul_pow]; norm_num
  have hy : (11 * y) ^ 4 = 14641 * y ^ 4 := by
    rw [mul_pow]; norm_num
  rw [hx, hy, mul_add]

/-- `C = B+11 ≡ 0 mod 11`, so `C¹³ ≡ 0` and `A⁴ ≡ 0`, hence `11 ∣ A`. -/
theorem eleven_dvd_B_forces_eleven_dvd_A_gap11 {A B : ℕ}
    (h : is_gap11_sol A B) (h11 : 11 ∣ B) : 11 ∣ A := by
  have hB4 : B ^ 4 % 11 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h11 (by decide))
  have hC : (B + 11) % 11 = 0 := by
    have : B % 11 = 0 := Nat.mod_eq_zero_of_dvd h11
    rw [Nat.add_mod, this]
  have hC13 : (B + 11) ^ 13 % 11 = 0 :=
    Nat.mod_eq_zero_of_dvd
      (dvd_pow (Nat.dvd_of_mod_eq_zero hC) (by decide : 13 ≠ 0))
  have hsum : (A ^ 4 + B ^ 4) % 11 = (B + 11) ^ 13 % 11 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  exact eleven_dvd_of_fourth_pow_mod_zero hsum

theorem eleven_dvd_B_forces_eleven_dvd_A {A B : ℕ}
    (h : is_gap11_sol A B) (h11 : 11 ∣ B) : 11 ∣ A :=
  eleven_dvd_B_forces_eleven_dvd_A_gap11 h h11

/-- `11 ∣ B` is impossible: three extra divisions by `11` leave
    `14641 (A₄⁴ + B₄⁴) = 11 (B₁+1)¹³` with `B₁+1 ≡ 1 mod 11`. -/
theorem no_sol_when_eleven_dvd_B_gap11 {A B : ℕ}
    (h : is_gap11_sol A B) (h11 : 11 ∣ B) : False := by
  have hA11 := eleven_dvd_B_forces_eleven_dvd_A_gap11 h h11
  obtain ⟨A1, hA⟩ := hA11
  obtain ⟨B1, hB⟩ := h11
  have hC : B + 11 = 11 * (B1 + 1) := by
    rw [hB, mul_add, mul_one]
  have hsol1 : (11 * A1) ^ 4 + (11 * B1) ^ 4 = (11 * (B1 + 1)) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 14641 * (A1 ^ 4 + B1 ^ 4) = 11 ^ 13 * (B1 + 1) ^ 13 := by
    rw [← sum_fourth_of_mul_eleven, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 11 ^ 9 * (B1 + 1) ^ 13 := by
    have hpow : (11 : ℕ) ^ 13 = 14641 * 11 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 14641)
    rw [heq1, hpow, mul_assoc]
  have hmod1 : (A1 ^ 4 + B1 ^ 4) % 11 = 0 := by
    have : 11 ∣ 11 ^ 9 * (B1 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 11 (by decide : 9 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1, hB1d⟩ := both_eleven_dvd_of_sum_fourth_mod11_zero hmod1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1d
  have heq2src : (11 * A2) ^ 4 + (11 * B2) ^ 4 =
      11 ^ 9 * (B1 + 1) ^ 13 := by
    rw [← hA2, ← hB2]
    exact h9
  have heq2 : 14641 * (A2 ^ 4 + B2 ^ 4) =
      11 ^ 9 * (B1 + 1) ^ 13 := by
    rw [← sum_fourth_of_mul_eleven]; exact heq2src
  have h5eq : A2 ^ 4 + B2 ^ 4 = 11 ^ 5 * (B1 + 1) ^ 13 := by
    have hpow : (11 : ℕ) ^ 9 = 14641 * 11 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 14641)
    rw [heq2, hpow, mul_assoc]
  have hmod2 : (A2 ^ 4 + B2 ^ 4) % 11 = 0 := by
    have : 11 ∣ 11 ^ 5 * (B1 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 11 (by decide : 5 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h5eq ▸ this)
  obtain ⟨hA2e, hB2e⟩ := both_eleven_dvd_of_sum_fourth_mod11_zero hmod2
  obtain ⟨A3, hA3e⟩ := hA2e
  obtain ⟨B3, hB3⟩ := hB2e
  have heq3src : (11 * A3) ^ 4 + (11 * B3) ^ 4 =
      11 ^ 5 * (B1 + 1) ^ 13 := by
    rw [← hA3e, ← hB3]
    exact h5eq
  have heq3 : 14641 * (A3 ^ 4 + B3 ^ 4) =
      11 ^ 5 * (B1 + 1) ^ 13 := by
    rw [← sum_fourth_of_mul_eleven]; exact heq3src
  have h1eq : A3 ^ 4 + B3 ^ 4 = 11 * (B1 + 1) ^ 13 := by
    have hpow : (11 : ℕ) ^ 5 = 14641 * 11 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 14641)
    rw [heq3, hpow, mul_assoc]
  have hmod3 : (A3 ^ 4 + B3 ^ 4) % 11 = 0 := by
    have : 11 ∣ 11 * (B1 + 1) ^ 13 := dvd_mul_right _ _
    exact Nat.mod_eq_zero_of_dvd (h1eq ▸ this)
  obtain ⟨hA3e', hB3e⟩ := both_eleven_dvd_of_sum_fourth_mod11_zero hmod3
  obtain ⟨A4, hA4⟩ := hA3e'
  obtain ⟨B4, hB4⟩ := hB3e
  have heq4src : (11 * A4) ^ 4 + (11 * B4) ^ 4 =
      11 * (B1 + 1) ^ 13 := by
    rw [← hA4, ← hB4]
    exact h1eq
  have heq4 : 14641 * (A4 ^ 4 + B4 ^ 4) = 11 * (B1 + 1) ^ 13 := by
    rw [← sum_fourth_of_mul_eleven]; exact heq4src
  have h1331 : 1331 * (A4 ^ 4 + B4 ^ 4) = (B1 + 1) ^ 13 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (11 : ℕ))
    have hL : 11 * (1331 * (A4 ^ 4 + B4 ^ 4)) =
        14641 * (A4 ^ 4 + B4 ^ 4) := by
      rw [← mul_assoc]
      rfl
    rw [hL]
    exact heq4
  have hC13 : 11 ∣ (B1 + 1) ^ 13 :=
    ⟨121 * (A4 ^ 4 + B4 ^ 4), by
      rw [← h1331, ← mul_assoc]
      rfl⟩
  have hC1 : 11 ∣ B1 + 1 := Nat.Prime.dvd_of_dvd_pow prime_eleven hC13
  have hB1eleven : 11 ∣ B1 := ⟨B2, hB2⟩
  have hCmod : (B1 + 1) % 11 = 1 := by
    have : B1 % 11 = 0 := Nat.mod_eq_zero_of_dvd hB1eleven
    rw [Nat.add_mod, this]
  have hC0 : (B1 + 1) % 11 = 0 := Nat.mod_eq_zero_of_dvd hC1
  rw [hCmod] at hC0
  exact (by decide : (1 : ℕ) ≠ 0) hC0

theorem eleven_not_dvd_B_of_sol {A B : ℕ}
    (h : is_gap11_sol A B) : ¬ 11 ∣ B :=
  fun h11 => no_sol_when_eleven_dvd_B_gap11 h h11

/-! ## Coprimeness: `gcd(A,B) = 1` on every solution -/

theorem gcd_A_B_eq_one_of_sol {A B : ℕ}
    (h : is_gap11_sol A B) : Nat.gcd A B = 1 := by
  have h11n := eleven_not_dvd_B_of_sol h
  set d := Nat.gcd A B
  have hdA : d ∣ A := Nat.gcd_dvd_left A B
  have hdB : d ∣ B := Nat.gcd_dvd_right A B
  have hdC13 : d ∣ (B + 11) ^ 13 := by
    have hA4 : d ∣ A ^ 4 := dvd_pow hdA (by decide)
    have hB4 : d ∣ B ^ 4 := dvd_pow hdB (by decide)
    have hsum : d ∣ A ^ 4 + B ^ 4 := Nat.dvd_add hA4 hB4
    simpa [is_gap11_sol] using (h ▸ hsum)
  have hgcd11 : Nat.gcd d (B + 11) ∣ 11 := by
    have h1 : Nat.gcd d (B + 11) ∣ B :=
      dvd_trans (Nat.gcd_dvd_left d (B + 11)) hdB
    have h2 : Nat.gcd d (B + 11) ∣ (B + 11) := Nat.gcd_dvd_right d (B + 11)
    exact dvd_trans (Nat.dvd_gcd h1 h2) (gcd_B_C_dvd_eleven B)
  have hgcd1 : Nat.gcd d (B + 11) = 1 := by
    have h117 : Nat.gcd d (B + 11) = 1 ∨ Nat.gcd d (B + 11) = 11 :=
      (Nat.dvd_prime prime_eleven).1 hgcd11
    rcases h117 with h1 | h11eq
    · exact h1
    · have hd11 : 11 ∣ d := by
        have := Nat.gcd_dvd_left d (B + 11)
        rwa [h11eq] at this
      have h11B : 11 ∣ B := dvd_trans hd11 hdB
      exact absurd h11B h11n
  have hcop : Nat.Coprime d (B + 11) := hgcd1
  have hcop13 : Nat.Coprime d ((B + 11) ^ 13) := hcop.pow_right 13
  have hd1 : d ∣ 1 := by
    have := Nat.dvd_gcd (dvd_refl d) hdC13
    rwa [show Nat.gcd d ((B + 11) ^ 13) = 1 from hcop13] at this
  exact Nat.eq_one_of_dvd_one hd1

theorem gcd_A_B_eq_one_of_sol_gap11 {A B : ℕ}
    (h : is_gap11_sol A B) : Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_sol h

theorem coprime_of_sol_gap11 {A B : ℕ}
    (h : is_gap11_sol A B) : Nat.Coprime A B :=
  gcd_A_B_eq_one_of_sol h

theorem gcd_A_B_eq_one_of_remaining_gap11 {A B : ℕ}
    (h : is_gap11_sol A B) (_h3 : ¬ 3 ∣ B) (_h11 : ¬ 11 ∣ B) :
    Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_sol h

theorem coprime_of_remaining_gap11 {A B : ℕ}
    (h : is_gap11_sol A B) (h3 : ¬ 3 ∣ B) (h11 : ¬ 11 ∣ B) :
    Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_remaining_gap11 h h3 h11

/-! ## `mod 5`: `5 ∣ B` is compatible (`C ≡ 1`), forces `A⁴ ≡ 1` -/

theorem fourth_pow_mod5 (a : ℕ) : a ^ 4 % 5 = 0 ∨ a ^ 4 % 5 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod5 a

theorem pow13_mod5 (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  BealMatveevBeal.BealGap1.pow13_mod5_eq_self c

theorem pow13_mod5_eq_self (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  pow13_mod5 c

/-- `C = B+11 ≡ 1 mod 5`, so `C¹³ ≡ 1` and `A⁴ ≡ 1`. No contradiction.
    Do **not** prove `no_sol_when_five_dvd_B` here. -/
theorem A_pow_four_mod5_eq_one_of_five_dvd_B {A B : ℕ}
    (h : is_gap11_sol A B) (h5 : 5 ∣ B) : A ^ 4 % 5 = 1 := by
  have hB4 : B ^ 4 % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h5 (by decide))
  have hC : (B + 11) % 5 = 1 := by
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [Nat.add_mod, this]
  have hC13 : (B + 11) ^ 13 % 5 = 1 := by
    rw [pow13_mod5, hC]
  have hsum : (A ^ 4 + B ^ 4) % 5 = (B + 11) ^ 13 % 5 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod5 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · exact h1

theorem not_five_dvd_A_of_five_dvd_B {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 5 ∣ B) : ¬ 5 ∣ A := by
  intro hA
  have : 5 ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
  rw [gcd_A_B_eq_one_of_sol h] at this
  exact (by decide : ¬ (5 ∣ 1)) this

/-! ## `mod 7`: `7 ∣ B` is compatible (`C ≡ 4`), forces `A⁴ ≡ 4` -/

theorem fourth_pow_mod7 (a : ℕ) :
    a ^ 4 % 7 = 0 ∨ a ^ 4 % 7 = 1 ∨ a ^ 4 % 7 = 2 ∨ a ^ 4 % 7 = 4 :=
  BealMatveevBeal.BealGap7.fourth_pow_mod7 a

theorem pow13_mod7 (c : ℕ) : c ^ 13 % 7 = c % 7 :=
  BealMatveevBeal.BealGap7.pow13_mod7 c

theorem pow13_mod7_eq_self (c : ℕ) : c ^ 13 % 7 = c % 7 :=
  pow13_mod7 c

/-- `C = B+11 ≡ 4 mod 7`, so `C¹³ ≡ 4` and `A⁴ ≡ 4`. No contradiction.
    Do **not** prove `no_sol_when_seven_dvd_B` here. -/
theorem A_pow_four_mod7_eq_four_of_seven_dvd_B {A B : ℕ}
    (h : is_gap11_sol A B) (h7 : 7 ∣ B) : A ^ 4 % 7 = 4 := by
  have hB4 : B ^ 4 % 7 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h7 (by decide))
  have hC : (B + 11) % 7 = 4 := by
    have : B % 7 = 0 := Nat.mod_eq_zero_of_dvd h7
    rw [Nat.add_mod, this]
  have hC13 : (B + 11) ^ 13 % 7 = 4 := by
    rw [pow13_mod7, hC]
  have hsum : (A ^ 4 + B ^ 4) % 7 = (B + 11) ^ 13 % 7 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 | h2 | h4 := fourth_pow_mod7 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · rw [h1] at hsum
    exact absurd hsum (by decide)
  · rw [h2] at hsum
    exact absurd hsum (by decide)
  · exact h4

theorem not_seven_dvd_A_of_seven_dvd_B {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 7 ∣ B) : ¬ 7 ∣ A := by
  intro hA
  have : 7 ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
  rw [gcd_A_B_eq_one_of_sol h] at this
  exact (by decide : ¬ (7 ∣ 1)) this

/-! ## Linear form `Λ = 4 log A − 13 log(B+11)` -/

noncomputable def Lambda_gap11 (A B : ℕ) : ℝ :=
  4 * log (A : ℝ) - 13 * log ((B + 11 : ℕ) : ℝ)

theorem A_pow_four_eq_sub {A B : ℕ} (h : is_gap11_sol A B) :
    A ^ 4 = (B + 11) ^ 13 - B ^ 4 := by
  rw [← h, add_comm, Nat.add_sub_cancel_left]

theorem A_pow_real_add {A B : ℕ} (h : is_gap11_sol A B) :
    (A : ℝ) ^ 4 + (B : ℝ) ^ 4 = ((B + 11 : ℕ) : ℝ) ^ 13 := by
  have h' : ((A ^ 4 + B ^ 4 : ℕ) : ℝ) = (((B + 11) ^ 13 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [Nat.cast_add, Nat.cast_pow] using h'

theorem A_pow_pos_of_sol {A B : ℕ} (h : is_gap11_sol A B) :
    (0 : ℝ) < (A : ℝ) ^ 4 := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  exact pow_pos hApos 4

theorem Lambda_gap11_eq_log_div {A B : ℕ}
    (h : is_gap11_sol A B) :
    Lambda_gap11 A B =
      log ((A : ℝ) ^ 4 / ((B + 11 : ℕ) : ℝ) ^ 13) := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hCpos : (0 : ℝ) < ((B + 11 : ℕ) : ℝ) := by
    have : 0 < B + 11 := Nat.add_pos_right B (by decide : 0 < 11)
    exact_mod_cast this
  unfold Lambda_gap11
  have h4 : (4 : ℝ) * log (A : ℝ) = log ((A : ℝ) ^ 4) :=
    (Real.log_pow (A : ℝ) 4).symm
  have h13 : (13 : ℝ) * log ((B + 11 : ℕ) : ℝ) =
      log (((B + 11 : ℕ) : ℝ) ^ 13) :=
    (Real.log_pow ((B + 11 : ℕ) : ℝ) 13).symm
  rw [h4, h13, Real.log_div (pow_pos hApos 4).ne' (pow_pos hCpos 13).ne']

theorem abs_Lambda_gap11_eq_log_one_plus {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 0 < B) :
    |Lambda_gap11 A B| = log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hu : (0 : ℝ) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    div_pos (pow_pos hBpos 4) hA4pos
  have hsum := A_pow_real_add h
  have hratio :
      (A : ℝ) ^ 4 / ((B + 11 : ℕ) : ℝ) ^ 13 =
        1 / (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    have hne : (A : ℝ) ^ 4 ≠ 0 := hA4pos.ne'
    have hden :
        (1 : ℝ) + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 =
          ((A : ℝ) ^ 4 + (B : ℝ) ^ 4) / (A : ℝ) ^ 4 := by
      field_simp [hne]
    rw [hden, one_div_div, hsum]
  have hΛ := Lambda_gap11_eq_log_div h
  have h1u : (0 : ℝ) < 1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    add_pos_of_nonneg_of_pos zero_le_one hu
  have hlog :
      Lambda_gap11 A B = -log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    rw [hΛ, hratio, Real.log_div one_ne_zero h1u.ne', log_one, zero_sub]
  rw [hlog, abs_neg, abs_of_nonneg (log_nonneg (le_of_lt (lt_add_of_pos_right 1 hu)))]

theorem abs_Lambda_gap11_le_ratio {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 0 < B) :
    |Lambda_gap11 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
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
  rwa [abs_Lambda_gap11_eq_log_one_plus h hB]

theorem B_pow_five_add_B_pow_four_lt_add_eleven_pow {B : ℕ} (_hB : 0 < B) :
    (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 11 : ℕ) : ℝ) ^ 13 := by
  have hx : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : ((B + 11 : ℕ) : ℝ) = (B : ℝ) + 11 := by
    rw [Nat.cast_add]
    norm_num
  have h5 : (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 11 : ℕ) : ℝ) ^ 5 := by
    rw [hC]
    have hexp : ((B : ℝ) + 11) ^ 5 =
        (B : ℝ) ^ 5 + 55 * (B : ℝ) ^ 4 + 1210 * (B : ℝ) ^ 3 +
          13310 * (B : ℝ) ^ 2 + 73205 * (B : ℝ) + 161051 := by
      ring
    have h3 : (0 : ℝ) ≤ (B : ℝ) ^ 3 := pow_nonneg hx 3
    have h2 : (0 : ℝ) ≤ (B : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hexp, h3, h2, hx]
  have hC1 : (1 : ℝ) ≤ ((B + 11 : ℕ) : ℝ) := by
    have : 1 ≤ B + 11 := le_trans (by decide : 1 ≤ 11) (Nat.le_add_left 11 B)
    exact_mod_cast this
  have h513 : ((B + 11 : ℕ) : ℝ) ^ 5 ≤ ((B + 11 : ℕ) : ℝ) ^ 13 :=
    pow_le_pow_right hC1 (by decide : (5 : ℕ) ≤ 13)
  exact lt_of_lt_of_le h5 h513

theorem A_pow_gt_B_pow_five {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 5 < (A : ℝ) ^ 4 := by
  have hA4 : (A : ℝ) ^ 4 =
      ((B + 11 : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 := by
    linarith [A_pow_real_add h]
  have hsum := B_pow_five_add_B_pow_four_lt_add_eleven_pow hB
  linarith [hA4, hsum]

theorem ratio_lt_inv_B {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 4 / (A : ℝ) ^ 4 < 1 / (B : ℝ) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hgt := A_pow_gt_B_pow_five h hB
  have : (B : ℝ) ^ 4 * (B : ℝ) < (A : ℝ) ^ 4 := by
    have : (B : ℝ) ^ 5 = (B : ℝ) ^ 4 * (B : ℝ) := by ring
    rwa [this] at hgt
  rw [div_lt_div_iff hA4pos hBpos, one_mul]
  exact this

theorem abs_Lambda_gap11_lt_inv_B {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 0 < B) :
    |Lambda_gap11 A B| < 1 / (B : ℝ) :=
  lt_of_le_of_lt (abs_Lambda_gap11_le_ratio h hB) (ratio_lt_inv_B h hB)

theorem A_pow_lt_C_pow {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 0 < B) :
    (A : ℝ) ^ 4 < ((B + 11 : ℕ) : ℝ) ^ 13 := by
  have hB4 : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hB
  have hlt : A ^ 4 < (B + 11) ^ 13 :=
    calc
      A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
      _ = (B + 11) ^ 13 := h
  exact_mod_cast hlt

/-! ## Log-method no-go (`C1 ≥ 1` loses to `B⁴/A⁴`) -/

theorem logA_gt_thirteen_of_B_ge_B0 {A B : ℕ}
    (h : is_gap11_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
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

/-- `exp(−C1 log A log(B+11)) < B⁴/A⁴` for every `C1 ≥ 1` on
    a gap-11 solution with `B ≥ B0`. Same cutoff as `62383af`:
    `C1 < 1` would be needed. -/
theorem hGen_exp_lt_ratio_gap11
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {A B : ℕ} (hsol : is_gap11_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + 11 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  set a : ℝ := log (A : ℝ)
  set c : ℝ := log ((B + 11 : ℕ) : ℝ)
  set C : ℝ := ((B + 11 : ℕ) : ℝ)
  have hAgt1 : 1 < A := A_gt_one_of_sol_pos hsol hB
  have hCgt1 : 1 < B + 11 :=
    lt_of_lt_of_le (by decide : 1 < 11) (Nat.le_add_left 11 B)
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (0 : ℕ) < A := lt_trans Nat.zero_lt_one hAgt1
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C := by
    have : 0 < B + 11 := Nat.add_pos_right B (by decide : 0 < 11)
    have : (0 : ℝ) < ((B + 11 : ℕ) : ℝ) := by exact_mod_cast this
    simpa [C] using this
  have hCgt : (1 : ℝ) < C := by
    have : (1 : ℝ) < ((B + 11 : ℕ) : ℝ) := by exact_mod_cast hCgt1
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

theorem C1_floor_hGen_loses_gap11 {A B : ℕ}
    (hsol : is_gap11_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + 11 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio_gap11
    (le_of_lt (by
      simpa [C1_floor_eq_logs] using
        BealMatveevBeal.MatveevThreeLogs.C1_floor_gt_one))
    hsol hB hB0

/-! ## Floor form / LLL no-go (`B+11`) -/

noncomputable def floorFormThird_gap11 (C : ℝ) (A B : ℕ) : ℝ :=
  (4 : ℝ) * ⌊C * log (A : ℝ)⌋ - 13 * ⌊C * log ((B + 11 : ℕ) : ℝ)⌋

/-- `|4⌊C log A⌋ − 13⌊C log(B+11)⌋ − C Λ| < 17` for every real `C`. -/
theorem floor_form_approx_of_C_gap11 (C : ℝ) (A B : ℕ) :
    |floorFormThird_gap11 C A B - C * Lambda_gap11 A B| < 17 := by
  set a : ℝ := C * log (A : ℝ)
  set cval : ℝ := C * log ((B + 11 : ℕ) : ℝ)
  have hΛ : C * Lambda_gap11 A B = 4 * a - 13 * cval := by
    simp only [Lambda_gap11, a, cval]
    ring
  have hft : floorFormThird_gap11 C A B = (4 : ℝ) * ⌊a⌋ - 13 * ⌊cval⌋ := rfl
  have hform :
      floorFormThird_gap11 C A B - C * Lambda_gap11 A B =
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

theorem floor_form_third_abs_lt_gap11 {C : ℝ} (hC : 0 < C) (A B : ℕ) :
    |floorFormThird_gap11 C A B| < 17 + C * |Lambda_gap11 A B| := by
  have happ := floor_form_approx_of_C_gap11 C A B
  have hmul : |C * Lambda_gap11 A B| = C * |Lambda_gap11 A B| := by
    rw [abs_mul, abs_of_pos hC]
  have := abs_sub_abs_le_abs_sub
    (floorFormThird_gap11 C A B) (C * Lambda_gap11 A B)
  linarith [happ, this, hmul]

/-- No scaling `C > 0` yields a Baker–Davenport witness
    `r > 17 + C/B0` on a gap-11 solution with `B ≥ B0`. -/
theorem hLLL_method_fails_gap11 :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        is_gap11_sol A B →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |floorFormThird_gap11 C A B| := by
  intro C hC A B hsol hB hB0
  rintro ⟨r, hgt, hle⟩
  have htri := floor_form_third_abs_lt_gap11 hC A B
  have hLam := abs_Lambda_gap11_lt_inv_B hsol hB
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hBle : (B0_nat : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hB0
  have hCΛ : C * |Lambda_gap11 A B| < C / (B0_nat : ℝ) := by
    have hmid : C * |Lambda_gap11 A B| < C * (1 / (B : ℝ)) :=
      mul_lt_mul_of_pos_left hLam hC
    have hrew : C * (1 / (B : ℝ)) = C / (B : ℝ) := mul_one_div _ _
    have hCB : C / (B : ℝ) ≤ C / (B0_nat : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hC) hB0pos hBle
    linarith [hmid, hrew, hCB]
  have hthird : |floorFormThird_gap11 C A B| < 17 + C / (B0_nat : ℝ) := by
    linarith [htri, hCΛ]
  linarith [hgt, hle, hthird]

theorem no_uniform_c_cubic_in_N_gap11 :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (BealMatveevBeal.MatveevThreeLogs.coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) :=
  BealMatveevBeal.MatveevThreeLogs.no_uniform_c_cubic_in_N

theorem coeffCount3_zero_ten_ten_ten_gap11 :
    BealMatveevBeal.MatveevThreeLogs.coeffCount3 0 10 10 10 = 1331 :=
  BealMatveevBeal.MatveevThreeLogs.coeffCount3_zero_ten_ten_ten

theorem no_uniform_c_easy_half_gap11 :
    (1 / 2 : ℝ) * 1 * 1 < 242 := by
  norm_num

/-! ## `hGen_gap11` / `hLLL_gap11` stay `def Prop` -/

/-- Matveev 2000 Theorem 1.4, n=2, displayed `C1_floor` exponential
    on a gap-11 solution. Not in Mathlib 4.12. Instantiating it at
    `B ≥ B0` does not beat `B⁴/A⁴`. -/
def hGen_gap11 : Prop :=
  ∀ A B : ℕ,
    is_gap11_sol A B →
      0 < B →
        |Lambda_gap11 A B| >
          exp (-(C1_floor : ℝ) * log (A : ℝ) *
            log ((B + 11 : ℕ) : ℝ))

/-- Bugeaud / LLL close for gap-11: ratio upper bound ⇒ `B ≤ B0`.
    The displayed lattice does not inhabit it. -/
def hLLL_gap11 : Prop :=
  (∀ A B : ℕ, is_gap11_sol A B → 0 < B →
      |Lambda_gap11 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4) →
    baker_bound_gap11

def baker_bound_gap11_of_hGen_hLLL : Prop :=
  hGen_gap11 → hLLL_gap11 → baker_bound_gap11

def baker_bound_gap11_of_hGen_hLLL_gap11 : Prop :=
  baker_bound_gap11_of_hGen_hLLL

/-! ## Combined unconditional no-go (no Darmon–Merel axiom) -/

/-- Log and LLL methods lose on `B ≥ B0`. Remaining solutions are
    coprime with `A > B0`, `B` even, `A` odd. `3 ∣ B` and `11 ∣ B`
    are impossible. `5 ∣ B` is compatible and forces `A⁴ ≡ 1`.
    `7 ∣ B` is compatible and forces `A⁴ ≡ 4`.
    Darmon–Merel `(4,4,13)` would be refuted by any such solution.
    `baker_bound_gap11` stays uninhabited as a named theorem. -/
theorem baker_bound_gap11_unconditional_nogo {A B : ℕ}
    (hsol : is_gap11_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + 11 : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (∀ C : ℝ, 0 < C →
      ¬ ∃ r : ℝ,
        17 + C / (B0_nat : ℝ) < r ∧
          r ≤ |floorFormThird_gap11 C A B|) ∧
    Nat.Coprime A B ∧
    B0_nat < A ∧
    Even B ∧
    Odd A ∧
    ¬ 3 ∣ B ∧
    ¬ 11 ∣ B ∧
    (5 ∣ B → A ^ 4 % 5 = 1) ∧
    (7 ∣ B → A ^ 4 % 7 = 4) ∧
    (darmon_merel_44_13_no_coprime → False) := by
  refine ⟨?_, ?_, coprime_of_sol_gap11 hsol, ?_,
    B_even_of_sol_gap11 hsol, A_odd_of_sol_gap11 hsol,
    three_not_dvd_B_of_sol hsol, eleven_not_dvd_B_of_sol hsol, ?_, ?_, ?_⟩
  · intro C1 hC1
    exact hGen_exp_lt_ratio_gap11 hC1 hsol hB hB0
  · intro C hC
    exact hLLL_method_fails_gap11 C hC A B hsol hB hB0
  · exact Nat.lt_of_le_of_lt hB0 (A_gt_B_of_sol hsol hB)
  · intro h5
    exact A_pow_four_mod5_eq_one_of_five_dvd_B hsol h5
  · intro h7
    exact A_pow_four_mod7_eq_four_of_seven_dvd_B hsol h7
  · intro hDM
    have hA0 : A = 0 ∨ B = 0 :=
      hDM A B (B + 11) (coprime_of_sol_gap11 hsol) hsol
    cases hA0 with
    | inl hA => exact A_ne_zero_of_sol hsol hA
    | inr hB0' => exact (ne_of_gt hB) hB0'

/-! ## Axiom-relative close (reuses `BealTrueV25`, no new axiom) -/

/-- Every gap-11 solution is impossible relative to
    `darmon_merel_4413_axiom`. Unlike gap-1 there is no `(1,0)`. -/
theorem no_gap11_of_axiom {A B : ℕ}
    (hsol : is_gap11_sol A B) : False := by
  have hDM := BealMatveevBeal.BealTrueV25.darmon_merel_4413_axiom
  have hA0 : A = 0 ∨ B = 0 :=
    hDM A B (B + 11) (coprime_of_sol_gap11 hsol) hsol
  cases hA0 with
  | inl hA => exact A_ne_zero_of_sol hsol hA
  | inr hB0 =>
      subst hB0
      exact three_not_dvd_B_of_sol hsol (by decide : 3 ∣ 0)

/-- Vacuous `B ≤ B0` for every gap-11 solution, relative to the
    existing Darmon–Merel axiom. Not named `baker_bound_gap11`. -/
theorem baker_bound_gap11_true {A B : ℕ}
    (hsol : is_gap11_sol A B) : B ≤ B0_nat :=
  (no_gap11_of_axiom hsol).elim

theorem baker_bound_gap11_true_of_axiom {A B : ℕ}
    (hsol : is_gap11_sol A B) : B ≤ B0_nat :=
  baker_bound_gap11_true hsol

#check C1_floor_eq
#check B0_nat_eq
#check not_gap11_one_zero
#check gcd_B_C_eq_gcd_eleven
#check gcd_B_C_dvd_eleven
#check gcd_B_C_dvd_eleven_gap11
#check gcd_A_B_eq_one_of_sol
#check coprime_of_sol_gap11
#check B_even_of_sol_gap11
#check A_odd_of_sol_gap11
#check A_gt_B_of_sol
#check no_sol_when_three_dvd_B_gap11
#check eleven_dvd_B_forces_eleven_dvd_A_gap11
#check eleven_dvd_B_forces_eleven_dvd_A
#check no_sol_when_eleven_dvd_B_gap11
#check A_pow_four_mod5_eq_one_of_five_dvd_B
#check A_pow_four_mod7_eq_four_of_seven_dvd_B
#check not_five_dvd_A_of_five_dvd_B
#check not_seven_dvd_A_of_seven_dvd_B
#check coprime_of_remaining_gap11
#check hGen_exp_lt_ratio_gap11
#check C1_floor_hGen_loses_gap11
#check floor_form_approx_of_C_gap11
#check hLLL_method_fails_gap11
#check no_uniform_c_cubic_in_N_gap11
#check no_uniform_c_easy_half_gap11
#check hGen_gap11
#check hLLL_gap11
#check baker_bound_gap11_of_hGen_hLLL
#check baker_bound_gap11_unconditional_nogo
#check baker_bound_gap11
#check no_gap11_of_axiom
#check baker_bound_gap11_true
#check baker_bound_gap11_true_of_axiom
#print axioms gcd_A_B_eq_one_of_sol
#print axioms B_even_of_sol_gap11
#print axioms A_odd_of_sol_gap11
#print axioms no_sol_when_three_dvd_B_gap11
#print axioms eleven_dvd_B_forces_eleven_dvd_A_gap11
#print axioms no_sol_when_eleven_dvd_B_gap11
#print axioms hGen_exp_lt_ratio_gap11
#print axioms C1_floor_hGen_loses_gap11
#print axioms hLLL_method_fails_gap11
#print axioms baker_bound_gap11_unconditional_nogo
#print axioms no_gap11_of_axiom
#print axioms baker_bound_gap11_true

end BealMatveevBeal.BealGap11
