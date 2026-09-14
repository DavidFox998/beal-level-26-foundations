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
import BealGap5

/-!
# Gap-6 `A⁴ + B⁴ = (B+6)¹³` (not a `B ≤ 10⁶` close)

Successor of `59d8a4a` (`v24-v24x-final-gap5-nogo`).
`C = B+6` so `gcd(B,C) ∣ 6`. Parity is gap-2/4, not gap-1/5:
`A` is even (odd `A` makes the left side `1` or `2` mod 16 while
even `C` is `0` and odd `C` is odd, never `2`). Even `B` dies
after three divisions by `2`, leaving
`A₃⁴ + B₃⁴ = 2 (4 B₃ + 3)¹³` with residue `6` or `14` mod 16
(not gap-2's `2` or `10`). So `B` is odd and `A` is even.
`(1,0)` is **not** a solution (`1 ≠ 6¹³`). Like gap-3 `f1cb039`,
`3 ∣ B` is a 3-descent: `A=3A₁ B=3B₁ C=3(B₁+2)` gives
`A₁⁴+B₁⁴=3⁹ C₁¹³`, and after two more steps
`27 X = C₁¹³` while `C₁=B₁+2 ≡ 2 mod 3`. `5 ∣ B` does **not**
kill (`C ≡ 1 mod 5`, `A⁴ ≡ 1` possible). Remaining solutions
are coprime (`p ∣ A,B` ⇒ `p ∣ 6`, but `B` is odd and `3 ∤ B`)
and pure Darmon–Merel signature `(4,4,13)`.

`hGen_gap6` / `hLLL_gap6` stay `def Prop`. Every `C1 ≥ 1` loses
to `B⁴/A⁴` on `B ≥ B0`; no scaling yields a Baker–Davenport
witness above `17 + C/B0`. Named theorem `baker_bound_gap6`
stays a `def Prop`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

set_option maxHeartbeats 800000

open Real

namespace BealMatveevBeal.BealGap6

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_logs :
    C1_floor = BealMatveevBeal.MatveevThreeLogs.C1_floor := rfl

theorem B0_nat_eq_logs :
    B0_nat = BealMatveevBeal.MatveevThreeLogs.B0_nat := rfl

/-! ## Gap-6 equation -/

def is_gap6_sol (A B : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = (B + 6) ^ 13

/-- Kernel Baker bound for gap-6. Stays a `def Prop`. -/
def baker_bound_gap6 : Prop :=
  ∀ A B : ℕ, is_gap6_sol A B → B ≤ B0_nat

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealTrueV25.darmon_merel_44_13_no_coprime

/-! ## `(1,0)` is not a solution -/

theorem not_gap6_one_zero : ¬ is_gap6_sol 1 0 := by
  unfold is_gap6_sol
  decide

theorem even_six : Even (6 : ℕ) := ⟨3, rfl⟩

/-! ## `gcd(B, B+6) = gcd(B, 6)` divides `6` -/

theorem gcd_B_C_eq_gcd_six (B : ℕ) : Nat.gcd B (B + 6) = Nat.gcd B 6 := by
  rw [Nat.gcd_comm B (B + 6), Nat.add_comm B 6]
  exact (Nat.gcd_add_self_left (6 : ℕ) B).trans (Nat.gcd_comm 6 B)

theorem gcd_B_C_dvd_six (B : ℕ) : Nat.gcd B (B + 6) ∣ 6 := by
  rw [gcd_B_C_eq_gcd_six]
  exact Nat.gcd_dvd_right B 6

theorem gcd_B_C_dvd_six_gap6 (B : ℕ) : Nat.gcd B (B + 6) ∣ 6 :=
  gcd_B_C_dvd_six B

/-! ## `2 n¹³` residues when `n ≡ 3` or `7` mod 8 -/

theorem two_mul_mod16_of_mod8_three {n : ℕ} (h : n % 8 = 3) :
    (2 * n) % 16 = 6 := by
  have h8 : (n % 16) % 8 = 3 := by
    rw [Nat.mod_mod_of_dvd n (by decide : 8 ∣ 16), h]
  have hn : n % 16 = 3 ∨ n % 16 = 11 := by
    have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
    interval_cases n % 16 <;> simp at h8 ⊢
  have hmul : (2 * n) % 16 = (2 * (n % 16)) % 16 := by
    rw [Nat.mul_mod, Nat.mod_eq_of_lt (by decide : 2 < 16)]
  rcases hn with h3 | h11
  · rw [hmul, h3]
  · rw [hmul, h11]

theorem two_mul_mod16_of_mod8_seven {n : ℕ} (h : n % 8 = 7) :
    (2 * n) % 16 = 14 := by
  have h8 : (n % 16) % 8 = 7 := by
    rw [Nat.mod_mod_of_dvd n (by decide : 8 ∣ 16), h]
  have hn : n % 16 = 7 ∨ n % 16 = 15 := by
    have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
    interval_cases n % 16 <;> simp at h8 ⊢
  have hmul : (2 * n) % 16 = (2 * (n % 16)) % 16 := by
    rw [Nat.mul_mod, Nat.mod_eq_of_lt (by decide : 2 < 16)]
  rcases hn with h7 | h15
  · rw [hmul, h7]
  · rw [hmul, h15]

theorem two_mul_pow13_mod16_of_mod8_three {n : ℕ} (h : n % 8 = 3) :
    (2 * n ^ 13) % 16 = 6 := by
  have hodd : Odd n := by
    rw [Nat.odd_iff]
    have : n % 2 = (n % 8) % 2 :=
      (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).symm
    rw [this, h]
  have h13 : n ^ 13 % 16 = n % 16 :=
    BealMatveevBeal.BealGap2.odd_pow_thirteen_mod_sixteen hodd
  have h2n : (2 * n) % 16 = 6 := two_mul_mod16_of_mod8_three h
  have hrev : (2 * (n % 16)) % 16 = (2 * n) % 16 := by
    have hm := Nat.mul_mod 2 n 16
    rw [Nat.mod_eq_of_lt (by decide : (2 : ℕ) < 16)] at hm
    exact hm.symm
  calc (2 * n ^ 13) % 16
      = (2 % 16 * (n ^ 13 % 16)) % 16 := Nat.mul_mod 2 (n ^ 13) 16
    _ = (2 * (n % 16)) % 16 := by
        rw [h13, Nat.mod_eq_of_lt (by decide : 2 < 16)]
    _ = (2 * n) % 16 := hrev
    _ = 6 := h2n

theorem two_mul_pow13_mod16_of_mod8_seven {n : ℕ} (h : n % 8 = 7) :
    (2 * n ^ 13) % 16 = 14 := by
  have hodd : Odd n := by
    rw [Nat.odd_iff]
    have : n % 2 = (n % 8) % 2 :=
      (Nat.mod_mod_of_dvd n (by decide : 2 ∣ 8)).symm
    rw [this, h]
  have h13 : n ^ 13 % 16 = n % 16 :=
    BealMatveevBeal.BealGap2.odd_pow_thirteen_mod_sixteen hodd
  have h2n : (2 * n) % 16 = 14 := two_mul_mod16_of_mod8_seven h
  have hrev : (2 * (n % 16)) % 16 = (2 * n) % 16 := by
    have hm := Nat.mul_mod 2 n 16
    rw [Nat.mod_eq_of_lt (by decide : (2 : ℕ) < 16)] at hm
    exact hm.symm
  calc (2 * n ^ 13) % 16
      = (2 % 16 * (n ^ 13 % 16)) % 16 := Nat.mul_mod 2 (n ^ 13) 16
    _ = (2 * (n % 16)) % 16 := by
        rw [h13, Nat.mod_eq_of_lt (by decide : 2 < 16)]
    _ = (2 * n) % 16 := hrev
    _ = 14 := h2n

/-! ## Parity: `A` is even. Even `B` is impossible, so `B` is odd. -/

theorem A_even_of_sol_gap6 {A B : ℕ} (h : is_gap6_sol A B) : Even A := by
  by_contra hne
  have hAodd : Odd A := Nat.not_even_iff_odd.1 hne
  have hA4 : A ^ 4 % 16 = 1 :=
    BealCatalanZsig.odd_pow_four_mod_sixteen hAodd
  by_cases hBeven : Even B
  · have hCeven : Even (B + 6) := hBeven.add even_six
    have h16C : 16 ∣ (B + 6) ^ 4 :=
      BealCatalanZsig.even_pow_four_dvd_sixteen hCeven
    have h16R : 16 ∣ (B + 6) ^ 13 :=
      dvd_trans h16C (pow_dvd_pow (B + 6) (by decide : 4 ≤ 13))
    have hR : (B + 6) ^ 13 % 16 = 0 := Nat.mod_eq_zero_of_dvd h16R
    have hB4 : B ^ 4 % 16 = 0 :=
      Nat.mod_eq_zero_of_dvd (BealCatalanZsig.even_pow_four_dvd_sixteen hBeven)
    have hL : (A ^ 4 + B ^ 4) % 16 = 1 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + 6) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (1 : ℕ) ≠ 0) this
  · have hBodd : Odd B := Nat.not_even_iff_odd.1 hBeven
    have hCodd : Odd (B + 6) := hBodd.add_even even_six
    have hB4 : B ^ 4 % 16 = 1 :=
      BealCatalanZsig.odd_pow_four_mod_sixteen hBodd
    have hL : (A ^ 4 + B ^ 4) % 16 = 2 := by
      rw [Nat.add_mod, hA4, hB4]
    have hR : (B + 6) ^ 13 % 16 = (B + 6) % 16 :=
      BealMatveevBeal.BealGap2.odd_pow_thirteen_mod_sixteen hCodd
    have : (A ^ 4 + B ^ 4) % 16 = (B + 6) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    have hC2 : (B + 6) % 2 = 0 := by
      have h16 : (B + 6) % 16 = 2 := this.symm
      have : ((B + 6) % 16) % 2 = 0 := by rw [h16]
      rwa [Nat.mod_mod_of_dvd (B + 6) (by decide : 2 ∣ 16)] at this
    exact Nat.not_even_iff_odd.2 hCodd (Nat.even_iff.2 hC2)

/-- Even `B` is impossible: three divisions by `2` leave
    `A₃⁴ + B₃⁴ = 2 (4 B₃ + 3)¹³`, whose residue is `6` or `14`
    mod 16, never a sum of fourth powers `{0,1,2}`. Do **not**
    prove `B_even_of_sol_gap6`. -/
theorem no_sol_when_even_B {A B : ℕ}
    (h : is_gap6_sol A B) (hBeven : Even B) : False := by
  have hAeven := A_even_of_sol_gap6 h
  obtain ⟨A1, hA'⟩ := hAeven
  obtain ⟨B1, hB'⟩ := hBeven
  have hA : A = 2 * A1 := by rw [hA', two_mul]
  have hB : B = 2 * B1 := by rw [hB', two_mul]
  have hC : B + 6 = 2 * (B1 + 3) := by
    rw [hB, mul_add]
  have hsol1 : (2 * A1) ^ 4 + (2 * B1) ^ 4 = (2 * (B1 + 3)) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 16 * (A1 ^ 4 + B1 ^ 4) = 2 ^ 13 * (B1 + 3) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 2 ^ 9 * (B1 + 3) ^ 13 := by
    have hpow : (2 : ℕ) ^ 13 = 16 * 2 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq1, hpow, mul_assoc]
  have h16 : (A1 ^ 4 + B1 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 9 * (B1 + 3) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 9) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1e, hB1e⟩ := BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16
  obtain ⟨A2, hA2'⟩ := hA1e
  obtain ⟨B2, hB2'⟩ := hB1e
  have hA2 : A1 = 2 * A2 := by rw [hA2', two_mul]
  have hB2 : B1 = 2 * B2 := by rw [hB2', two_mul]
  have heq2src : (2 * A2) ^ 4 + (2 * B2) ^ 4 =
      2 ^ 9 * (2 * B2 + 3) ^ 13 := by
    rw [← hA2, ← hB2]
    exact h9
  have heq2 : 16 * (A2 ^ 4 + B2 ^ 4) = 2 ^ 9 * (2 * B2 + 3) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq2src
  have h5 : A2 ^ 4 + B2 ^ 4 = 2 ^ 5 * (2 * B2 + 3) ^ 13 := by
    have hpow : (2 : ℕ) ^ 9 = 16 * 2 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq2, hpow, mul_assoc]
  have h16' : (A2 ^ 4 + B2 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 5 * (2 * B2 + 3) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 5) _
    exact Nat.mod_eq_zero_of_dvd (h5 ▸ this)
  obtain ⟨hA2e, hB2e⟩ := BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16'
  obtain ⟨A3, hA3'⟩ := hA2e
  obtain ⟨B3, hB3'⟩ := hB2e
  have hA3 : A2 = 2 * A3 := by rw [hA3', two_mul]
  have hB3 : B2 = 2 * B3 := by rw [hB3', two_mul]
  have heq3src : (2 * A3) ^ 4 + (2 * B3) ^ 4 =
      2 ^ 5 * (4 * B3 + 3) ^ 13 := by
    have hB21 : 2 * B2 + 3 = 4 * B3 + 3 := by
      rw [hB3]
      have hmul : 2 * (2 * B3) = 4 * B3 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA3, ← hB3, ← hB21]
    exact h5
  have heq3 : 16 * (A3 ^ 4 + B3 ^ 4) = 2 ^ 5 * (4 * B3 + 3) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq3src
  have hlast : A3 ^ 4 + B3 ^ 4 = 2 * (4 * B3 + 3) ^ 13 := by
    have hpow : (2 : ℕ) ^ 5 = 16 * 2 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq3, hpow, mul_assoc]
  have hmod : (A3 ^ 4 + B3 ^ 4) % 16 =
      (2 * (4 * B3 + 3) ^ 13) % 16 := by rw [hlast]
  by_cases hB3e : Even B3
  · obtain ⟨k, hk'⟩ := hB3e
    have hk : B3 = 2 * k := by rw [hk', two_mul]
    have hC : 4 * B3 + 3 = 8 * k + 3 := by
      rw [hk]
      have hmul : 4 * (2 * k) = 8 * k := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    have hC8 : (4 * B3 + 3) % 8 = 3 := by
      rw [hC, Nat.add_mod, Nat.mul_mod]
      norm_num
    have hR : (2 * (4 * B3 + 3) ^ 13) % 16 = 6 :=
      two_mul_pow13_mod16_of_mod8_three hC8
    obtain h0 | h1 | h2 := BealMatveevBeal.BealGap2.sum_fourth_mod16 A3 B3
    · rw [h0, hR] at hmod
      exact (by decide : (0 : ℕ) ≠ 6) hmod
    · rw [h1, hR] at hmod
      exact (by decide : (1 : ℕ) ≠ 6) hmod
    · rw [h2, hR] at hmod
      exact (by decide : (2 : ℕ) ≠ 6) hmod
  · have hB3o : Odd B3 := Nat.not_even_iff_odd.1 hB3e
    obtain ⟨k, hk⟩ := hB3o
    have hC : 4 * B3 + 3 = 8 * k + 7 := by
      rw [hk]
      ring
    have hC8 : (4 * B3 + 3) % 8 = 7 := by
      rw [hC, Nat.add_mod, Nat.mul_mod]
      norm_num
    have hR : (2 * (4 * B3 + 3) ^ 13) % 16 = 14 :=
      two_mul_pow13_mod16_of_mod8_seven hC8
    obtain h0 | h1 | h2 := BealMatveevBeal.BealGap2.sum_fourth_mod16 A3 B3
    · rw [h0, hR] at hmod
      exact (by decide : (0 : ℕ) ≠ 14) hmod
    · rw [h1, hR] at hmod
      exact (by decide : (1 : ℕ) ≠ 14) hmod
    · rw [h2, hR] at hmod
      exact (by decide : (2 : ℕ) ≠ 14) hmod

theorem B_odd_of_sol_gap6 {A B : ℕ} (h : is_gap6_sol A B) : Odd B := by
  rw [← Nat.not_even_iff_odd]
  intro hBeven
  exact no_sol_when_even_B h hBeven

/-! ## Size: `A > B` for `B > 0`; `A ≠ 0` on every solution -/

theorem two_mul_B_pow_four_lt_add_six_pow (B : ℕ) :
    2 * B ^ 4 < (B + 6) ^ 13 := by
  have h6 : 6 ≤ B + 6 := Nat.le_add_left 6 B
  have h2 : 2 ≤ B + 6 := le_trans (by decide : 2 ≤ 6) h6
  have h2pow : 2 ≤ 2 ^ 9 := by decide
  have h29 : 2 ^ 9 ≤ (B + 6) ^ 9 := Nat.pow_le_pow_left h2 9
  have h2le : 2 ≤ (B + 6) ^ 9 := le_trans h2pow h29
  have hBlt : B < B + 6 := Nat.lt_add_of_pos_right (by decide : 0 < (6 : ℕ))
  have hB4 : B ^ 4 < (B + 6) ^ 4 :=
    Nat.pow_lt_pow_left hBlt (by decide : 4 ≠ 0)
  have hle : 2 * B ^ 4 ≤ (B + 6) ^ 9 * B ^ 4 :=
    Nat.mul_le_mul_right (B ^ 4) h2le
  have hposC : 0 < B + 6 := Nat.add_pos_right B (by decide : 0 < 6)
  have hpos9 : 0 < (B + 6) ^ 9 := Nat.pos_pow_of_pos 9 hposC
  have hlt : (B + 6) ^ 9 * B ^ 4 < (B + 6) ^ 9 * (B + 6) ^ 4 :=
    Nat.mul_lt_mul_of_pos_left hB4 hpos9
  have hsum : (B + 6) ^ 9 * (B + 6) ^ 4 = (B + 6) ^ 13 := by
    rw [← pow_add]
  rw [← hsum]
  exact lt_of_le_of_lt hle hlt

theorem A_gt_B_of_sol {A B : ℕ}
    (h : is_gap6_sol A B) (_hB : 0 < B) : B < A := by
  by_contra hle
  have hAB : A ≤ B := Nat.not_lt.mp hle
  have hA4 : A ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hAB 4
  have hsum : A ^ 4 + B ^ 4 ≤ 2 * B ^ 4 := by
    have := Nat.add_le_add hA4 (le_refl (B ^ 4))
    simpa [two_mul] using this
  have hlt := two_mul_B_pow_four_lt_add_six_pow B
  have : A ^ 4 + B ^ 4 < (B + 6) ^ 13 := lt_of_le_of_lt hsum hlt
  exact (ne_of_lt this) h

theorem A_ne_zero_of_sol {A B : ℕ} (h : is_gap6_sol A B) : A ≠ 0 := by
  intro hA
  subst hA
  have heq : B ^ 4 = (B + 6) ^ 13 := by
    simpa [is_gap6_sol] using h
  by_cases hB : B = 0
  · subst hB
    exact (by decide : (0 : ℕ) ≠ 13060694016) heq
  · have hpos : 0 < B := Nat.pos_of_ne_zero hB
    have hB4pos : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hpos
    have hlt1 : B ^ 4 < 2 * B ^ 4 := by
      have : 1 * B ^ 4 < 2 * B ^ 4 :=
        Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hB4pos
      simpa using this
    have hlt2 := two_mul_B_pow_four_lt_add_six_pow B
    exact (ne_of_lt (lt_trans hlt1 hlt2)) heq

theorem A_gt_one_of_sol_pos {A B : ℕ}
    (h : is_gap6_sol A B) (hB : 0 < B) : 1 < A :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) (A_gt_B_of_sol h hB)

/-! ## `mod 3`: `3 ∣ B` forces `3 ∣ A`, then 3-descent dies -/

theorem fourth_pow_mod3 (a : ℕ) : a ^ 4 % 3 = 0 ∨ a ^ 4 % 3 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod3 a

theorem pow13_mod3 (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  BealMatveevBeal.BealGap1.pow13_mod3_eq_self c

theorem pow13_mod3_eq_self (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  pow13_mod3 c

theorem three_dvd_of_fourth_pow_mod_zero {n : ℕ}
    (h : n ^ 4 % 3 = 0) : 3 ∣ n :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_three (Nat.dvd_of_mod_eq_zero h)

theorem both_three_dvd_of_sum_fourth_mod3_zero {X Y : ℕ}
    (h : (X ^ 4 + Y ^ 4) % 3 = 0) : 3 ∣ X ∧ 3 ∣ Y := by
  obtain hX0 | hX1 := fourth_pow_mod3 X
  · obtain hY0 | hY1 := fourth_pow_mod3 Y
    · exact ⟨three_dvd_of_fourth_pow_mod_zero hX0,
        three_dvd_of_fourth_pow_mod_zero hY0⟩
    · have hL : (X ^ 4 + Y ^ 4) % 3 = 1 := by
        rw [Nat.add_mod, hX0, hY1]
      rw [hL] at h
      exact False.elim ((by decide : (1 : ℕ) ≠ 0) h)
  · obtain hY0 | hY1 := fourth_pow_mod3 Y
    · have hL : (X ^ 4 + Y ^ 4) % 3 = 1 := by
        rw [Nat.add_mod, hX1, hY0]
      rw [hL] at h
      exact False.elim ((by decide : (1 : ℕ) ≠ 0) h)
    · have hL : (X ^ 4 + Y ^ 4) % 3 = 2 := by
        rw [Nat.add_mod, hX1, hY1]
      rw [hL] at h
      exact False.elim ((by decide : (2 : ℕ) ≠ 0) h)

theorem sum_fourth_of_mul_three (x y : ℕ) :
    (3 * x) ^ 4 + (3 * y) ^ 4 = 81 * (x ^ 4 + y ^ 4) := by
  have hx : (3 * x) ^ 4 = 81 * x ^ 4 := by
    rw [mul_pow]; norm_num
  have hy : (3 * y) ^ 4 = 81 * y ^ 4 := by
    rw [mul_pow]; norm_num
  rw [hx, hy, mul_add]

/-- `C = B+6 ≡ 0 mod 3`, so `C¹³ ≡ 0` and `A⁴ ≡ 0`, hence `3 ∣ A`. -/
theorem three_dvd_B_forces_three_dvd_A_gap6 {A B : ℕ}
    (h : is_gap6_sol A B) (h3 : 3 ∣ B) : 3 ∣ A := by
  have hB4 : B ^ 4 % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h3 (by decide))
  have hC : (B + 6) % 3 = 0 := by
    have : B % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    rw [Nat.add_mod, this]
  have hC13 : (B + 6) ^ 13 % 3 = 0 := by
    rw [pow13_mod3, hC]
  have hsum : (A ^ 4 + B ^ 4) % 3 = (B + 6) ^ 13 % 3 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  exact three_dvd_of_fourth_pow_mod_zero hsum

/-- `3 ∣ B` is impossible: three extra divisions by `3` leave
    `27 (A₄⁴ + B₄⁴) = (B₁+2)¹³` with `B₁+2 ≡ 2 mod 3`. -/
theorem no_sol_when_three_dvd_B_gap6 {A B : ℕ}
    (h : is_gap6_sol A B) (h3 : 3 ∣ B) : False := by
  have hA3 := three_dvd_B_forces_three_dvd_A_gap6 h h3
  obtain ⟨A1, hA⟩ := hA3
  obtain ⟨B1, hB⟩ := h3
  have hC : B + 6 = 3 * (B1 + 2) := by
    rw [hB, mul_add]
  have hsol1 : (3 * A1) ^ 4 + (3 * B1) ^ 4 = (3 * (B1 + 2)) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 81 * (A1 ^ 4 + B1 ^ 4) = 3 ^ 13 * (B1 + 2) ^ 13 := by
    rw [← sum_fourth_of_mul_three, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 3 ^ 9 * (B1 + 2) ^ 13 := by
    have hpow : (3 : ℕ) ^ 13 = 81 * 3 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 81)
    rw [heq1, hpow, mul_assoc]
  have hmod1 : (A1 ^ 4 + B1 ^ 4) % 3 = 0 := by
    have : 3 ∣ 3 ^ 9 * (B1 + 2) ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 3 (by decide : 9 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1, hB1d⟩ := both_three_dvd_of_sum_fourth_mod3_zero hmod1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1d
  have heq2src : (3 * A2) ^ 4 + (3 * B2) ^ 4 =
      3 ^ 9 * (B1 + 2) ^ 13 := by
    rw [← hA2, ← hB2]
    exact h9
  have heq2 : 81 * (A2 ^ 4 + B2 ^ 4) =
      3 ^ 9 * (B1 + 2) ^ 13 := by
    rw [← sum_fourth_of_mul_three]; exact heq2src
  have h5eq : A2 ^ 4 + B2 ^ 4 = 3 ^ 5 * (B1 + 2) ^ 13 := by
    have hpow : (3 : ℕ) ^ 9 = 81 * 3 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 81)
    rw [heq2, hpow, mul_assoc]
  have hmod2 : (A2 ^ 4 + B2 ^ 4) % 3 = 0 := by
    have : 3 ∣ 3 ^ 5 * (B1 + 2) ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 3 (by decide : 5 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h5eq ▸ this)
  obtain ⟨hA2e, hB2e⟩ := both_three_dvd_of_sum_fourth_mod3_zero hmod2
  obtain ⟨A3, hA3e⟩ := hA2e
  obtain ⟨B3, hB3⟩ := hB2e
  have heq3src : (3 * A3) ^ 4 + (3 * B3) ^ 4 =
      3 ^ 5 * (B1 + 2) ^ 13 := by
    rw [← hA3e, ← hB3]
    exact h5eq
  have heq3 : 81 * (A3 ^ 4 + B3 ^ 4) =
      3 ^ 5 * (B1 + 2) ^ 13 := by
    rw [← sum_fourth_of_mul_three]; exact heq3src
  have h1eq : A3 ^ 4 + B3 ^ 4 = 3 * (B1 + 2) ^ 13 := by
    have hpow : (3 : ℕ) ^ 5 = 81 * 3 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 81)
    rw [heq3, hpow, mul_assoc]
  have hmod3 : (A3 ^ 4 + B3 ^ 4) % 3 = 0 := by
    have : 3 ∣ 3 * (B1 + 2) ^ 13 := dvd_mul_right _ _
    exact Nat.mod_eq_zero_of_dvd (h1eq ▸ this)
  obtain ⟨hA3e', hB3e⟩ := both_three_dvd_of_sum_fourth_mod3_zero hmod3
  obtain ⟨A4, hA4⟩ := hA3e'
  obtain ⟨B4, hB4⟩ := hB3e
  have heq4src : (3 * A4) ^ 4 + (3 * B4) ^ 4 =
      3 * (B1 + 2) ^ 13 := by
    rw [← hA4, ← hB4]
    exact h1eq
  have heq4 : 81 * (A4 ^ 4 + B4 ^ 4) = 3 * (B1 + 2) ^ 13 := by
    rw [← sum_fourth_of_mul_three]; exact heq4src
  have h27 : 27 * (A4 ^ 4 + B4 ^ 4) = (B1 + 2) ^ 13 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (3 : ℕ))
    have hL : 3 * (27 * (A4 ^ 4 + B4 ^ 4)) =
        81 * (A4 ^ 4 + B4 ^ 4) := by
      rw [← mul_assoc]
      rfl
    rw [hL]
    exact heq4
  have hC13 : 3 ∣ (B1 + 2) ^ 13 :=
    ⟨9 * (A4 ^ 4 + B4 ^ 4), by
      rw [← h27, ← mul_assoc]
      rfl⟩
  have hC1 : 3 ∣ B1 + 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hC13
  have hB1three : 3 ∣ B1 := ⟨B2, hB2⟩
  have hCmod : (B1 + 2) % 3 = 2 := by
    have : B1 % 3 = 0 := Nat.mod_eq_zero_of_dvd hB1three
    rw [Nat.add_mod, this]
  have hC0 : (B1 + 2) % 3 = 0 := Nat.mod_eq_zero_of_dvd hC1
  rw [hCmod] at hC0
  exact (by decide : (2 : ℕ) ≠ 0) hC0

theorem three_not_dvd_B_of_sol {A B : ℕ}
    (h : is_gap6_sol A B) : ¬ 3 ∣ B :=
  fun h3 => no_sol_when_three_dvd_B_gap6 h h3

/-! ## Coprimeness: `gcd(A,B) = 1` on every solution -/

theorem gcd_A_B_eq_one_of_sol {A B : ℕ}
    (h : is_gap6_sol A B) : Nat.gcd A B = 1 := by
  have hBodd := B_odd_of_sol_gap6 h
  have h3n := three_not_dvd_B_of_sol h
  set d := Nat.gcd A B
  have hdA : d ∣ A := Nat.gcd_dvd_left A B
  have hdB : d ∣ B := Nat.gcd_dvd_right A B
  have hdC13 : d ∣ (B + 6) ^ 13 := by
    have hA4 : d ∣ A ^ 4 := dvd_pow hdA (by decide)
    have hB4 : d ∣ B ^ 4 := dvd_pow hdB (by decide)
    have hsum : d ∣ A ^ 4 + B ^ 4 := Nat.dvd_add hA4 hB4
    simpa [is_gap6_sol] using (h ▸ hsum)
  have hgcd6 : Nat.gcd d (B + 6) ∣ 6 := by
    have h1 : Nat.gcd d (B + 6) ∣ B :=
      dvd_trans (Nat.gcd_dvd_left d (B + 6)) hdB
    have h2 : Nat.gcd d (B + 6) ∣ (B + 6) := Nat.gcd_dvd_right d (B + 6)
    exact dvd_trans (Nat.dvd_gcd h1 h2) (gcd_B_C_dvd_six B)
  have hgcd1 : Nat.gcd d (B + 6) = 1 := by
    by_contra hne
    have hpos : 1 < Nat.gcd d (B + 6) :=
      Nat.lt_of_le_of_ne (Nat.succ_le_of_lt
        (Nat.gcd_pos_of_pos_right d (Nat.add_pos_right B (by decide : 0 < 6))))
        (Ne.symm hne)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hpos)
    have hp6 : p ∣ 6 := dvd_trans hpd hgcd6
    have hp23 : p = 2 ∨ p = 3 := by
      have hmul : p ∣ 2 ∨ p ∣ 3 :=
        (Nat.Prime.dvd_mul hp).mp (by simpa using hp6)
      rcases hmul with h2 | h3
      · exact Or.inl
          (((Nat.dvd_prime Nat.prime_two).1 h2).resolve_left hp.ne_one)
      · exact Or.inr
          (((Nat.dvd_prime Nat.prime_three).1 h3).resolve_left hp.ne_one)
    rcases hp23 with hp2 | hp3
    · have hd2 : 2 ∣ d := by
        have := Nat.gcd_dvd_left d (B + 6)
        rw [hp2] at hpd
        exact dvd_trans hpd this
      have h2B : 2 ∣ B := dvd_trans hd2 hdB
      exact absurd (even_iff_two_dvd.2 h2B) (Nat.not_even_iff_odd.2 hBodd)
    · have hd3 : 3 ∣ d := by
        have := Nat.gcd_dvd_left d (B + 6)
        rw [hp3] at hpd
        exact dvd_trans hpd this
      exact h3n (dvd_trans hd3 hdB)
  have hcop : Nat.Coprime d (B + 6) := hgcd1
  have hcop13 : Nat.Coprime d ((B + 6) ^ 13) := hcop.pow_right 13
  have hd1 : d ∣ 1 := by
    have := Nat.dvd_gcd (dvd_refl d) hdC13
    rwa [show Nat.gcd d ((B + 6) ^ 13) = 1 from hcop13] at this
  exact Nat.eq_one_of_dvd_one hd1

theorem gcd_A_B_eq_one_of_sol_gap6 {A B : ℕ}
    (h : is_gap6_sol A B) : Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_sol h

theorem coprime_of_sol_gap6 {A B : ℕ}
    (h : is_gap6_sol A B) : Nat.Coprime A B :=
  gcd_A_B_eq_one_of_sol h

theorem gcd_A_B_eq_one_of_remaining_gap6 {A B : ℕ}
    (h : is_gap6_sol A B) (_h3 : ¬ 3 ∣ B) : Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_sol h

theorem coprime_of_remaining_gap6 {A B : ℕ}
    (h : is_gap6_sol A B) (h3 : ¬ 3 ∣ B) : Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_remaining_gap6 h h3

/-! ## `mod 5`: `5 ∣ B` is compatible (`C ≡ 1`), forces `5 ∤ A` -/

theorem fourth_pow_mod5 (a : ℕ) : a ^ 4 % 5 = 0 ∨ a ^ 4 % 5 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod5 a

theorem pow13_mod5 (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  BealMatveevBeal.BealGap1.pow13_mod5_eq_self c

theorem pow13_mod5_eq_self (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  pow13_mod5 c

/-- `C = B+6 ≡ 1 mod 5`, so `C¹³ ≡ 1` and `A⁴ ≡ 1`. No contradiction.
    Do **not** prove `no_sol_when_five_dvd_B` here. -/
theorem A_pow_four_mod5_eq_one_of_five_dvd_B {A B : ℕ}
    (h : is_gap6_sol A B) (h5 : 5 ∣ B) : A ^ 4 % 5 = 1 := by
  have hB4 : B ^ 4 % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h5 (by decide))
  have hC : (B + 6) % 5 = 1 := by
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [Nat.add_mod, this]
  have hC13 : (B + 6) ^ 13 % 5 = 1 := by
    rw [pow13_mod5, hC]
  have hsum : (A ^ 4 + B ^ 4) % 5 = (B + 6) ^ 13 % 5 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod5 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · exact h1

theorem not_five_dvd_A_of_five_dvd_B {A B : ℕ}
    (h : is_gap6_sol A B) (hB : 5 ∣ B) : ¬ 5 ∣ A := by
  intro hA
  have : 5 ∣ Nat.gcd A B := Nat.dvd_gcd hA hB
  rw [gcd_A_B_eq_one_of_sol h] at this
  exact (by decide : ¬ (5 ∣ 1)) this

/-! ## Linear form `Λ = 4 log A − 13 log(B+6)` -/

noncomputable def Lambda_gap6 (A B : ℕ) : ℝ :=
  4 * log (A : ℝ) - 13 * log ((B + 6 : ℕ) : ℝ)

theorem A_pow_four_eq_sub {A B : ℕ} (h : is_gap6_sol A B) :
    A ^ 4 = (B + 6) ^ 13 - B ^ 4 := by
  rw [← h, add_comm, Nat.add_sub_cancel_left]

theorem A_pow_real_add {A B : ℕ} (h : is_gap6_sol A B) :
    (A : ℝ) ^ 4 + (B : ℝ) ^ 4 = ((B + 6 : ℕ) : ℝ) ^ 13 := by
  have h' : ((A ^ 4 + B ^ 4 : ℕ) : ℝ) = (((B + 6) ^ 13 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [Nat.cast_add, Nat.cast_pow] using h'

theorem A_pow_pos_of_sol {A B : ℕ} (h : is_gap6_sol A B) :
    (0 : ℝ) < (A : ℝ) ^ 4 := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  exact pow_pos hApos 4

theorem Lambda_gap6_eq_log_div {A B : ℕ}
    (h : is_gap6_sol A B) :
    Lambda_gap6 A B =
      log ((A : ℝ) ^ 4 / ((B + 6 : ℕ) : ℝ) ^ 13) := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hCpos : (0 : ℝ) < ((B + 6 : ℕ) : ℝ) := by
    have : 0 < B + 6 := Nat.add_pos_right B (by decide : 0 < 6)
    exact_mod_cast this
  unfold Lambda_gap6
  have h4 : (4 : ℝ) * log (A : ℝ) = log ((A : ℝ) ^ 4) :=
    (Real.log_pow (A : ℝ) 4).symm
  have h13 : (13 : ℝ) * log ((B + 6 : ℕ) : ℝ) =
      log (((B + 6 : ℕ) : ℝ) ^ 13) :=
    (Real.log_pow ((B + 6 : ℕ) : ℝ) 13).symm
  rw [h4, h13, Real.log_div (pow_pos hApos 4).ne' (pow_pos hCpos 13).ne']

theorem abs_Lambda_gap6_eq_log_one_plus {A B : ℕ}
    (h : is_gap6_sol A B) (hB : 0 < B) :
    |Lambda_gap6 A B| = log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hu : (0 : ℝ) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    div_pos (pow_pos hBpos 4) hA4pos
  have hsum := A_pow_real_add h
  have hratio :
      (A : ℝ) ^ 4 / ((B + 6 : ℕ) : ℝ) ^ 13 =
        1 / (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    have hne : (A : ℝ) ^ 4 ≠ 0 := hA4pos.ne'
    have hden :
        (1 : ℝ) + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 =
          ((A : ℝ) ^ 4 + (B : ℝ) ^ 4) / (A : ℝ) ^ 4 := by
      field_simp [hne]
    rw [hden, one_div_div, hsum]
  have hΛ := Lambda_gap6_eq_log_div h
  have h1u : (0 : ℝ) < 1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    add_pos_of_nonneg_of_pos zero_le_one hu
  have hlog :
      Lambda_gap6 A B = -log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    rw [hΛ, hratio, Real.log_div one_ne_zero h1u.ne', log_one, zero_sub]
  rw [hlog, abs_neg, abs_of_nonneg (log_nonneg (le_of_lt (lt_add_of_pos_right 1 hu)))]

theorem abs_Lambda_gap6_le_ratio {A B : ℕ}
    (h : is_gap6_sol A B) (hB : 0 < B) :
    |Lambda_gap6 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
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
  rwa [abs_Lambda_gap6_eq_log_one_plus h hB]

theorem B_pow_five_add_B_pow_four_lt_add_six_pow {B : ℕ} (_hB : 0 < B) :
    (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 6 : ℕ) : ℝ) ^ 13 := by
  have hx : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : ((B + 6 : ℕ) : ℝ) = (B : ℝ) + 6 := by
    rw [Nat.cast_add]
    norm_num
  have h5 : (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 6 : ℕ) : ℝ) ^ 5 := by
    rw [hC]
    have hexp : ((B : ℝ) + 6) ^ 5 =
        (B : ℝ) ^ 5 + 30 * (B : ℝ) ^ 4 + 360 * (B : ℝ) ^ 3 +
          2160 * (B : ℝ) ^ 2 + 6480 * (B : ℝ) + 7776 := by
      ring
    have h3 : (0 : ℝ) ≤ (B : ℝ) ^ 3 := pow_nonneg hx 3
    have h2 : (0 : ℝ) ≤ (B : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hexp, h3, h2, hx]
  have hC1 : (1 : ℝ) ≤ ((B + 6 : ℕ) : ℝ) := by
    have : 1 ≤ B + 6 := le_trans (by decide : 1 ≤ 6) (Nat.le_add_left 6 B)
    exact_mod_cast this
  have h513 : ((B + 6 : ℕ) : ℝ) ^ 5 ≤ ((B + 6 : ℕ) : ℝ) ^ 13 :=
    pow_le_pow_right hC1 (by decide : (5 : ℕ) ≤ 13)
  exact lt_of_lt_of_le h5 h513

theorem A_pow_gt_B_pow_five {A B : ℕ}
    (h : is_gap6_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 5 < (A : ℝ) ^ 4 := by
  have hA4 : (A : ℝ) ^ 4 =
      ((B + 6 : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 := by
    linarith [A_pow_real_add h]
  have hsum := B_pow_five_add_B_pow_four_lt_add_six_pow hB
  linarith [hA4, hsum]

theorem ratio_lt_inv_B {A B : ℕ}
    (h : is_gap6_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 4 / (A : ℝ) ^ 4 < 1 / (B : ℝ) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hgt := A_pow_gt_B_pow_five h hB
  have : (B : ℝ) ^ 4 * (B : ℝ) < (A : ℝ) ^ 4 := by
    have : (B : ℝ) ^ 5 = (B : ℝ) ^ 4 * (B : ℝ) := by ring
    rwa [this] at hgt
  rw [div_lt_div_iff hA4pos hBpos, one_mul]
  exact this

theorem abs_Lambda_gap6_lt_inv_B {A B : ℕ}
    (h : is_gap6_sol A B) (hB : 0 < B) :
    |Lambda_gap6 A B| < 1 / (B : ℝ) :=
  lt_of_le_of_lt (abs_Lambda_gap6_le_ratio h hB) (ratio_lt_inv_B h hB)

theorem A_pow_lt_C_pow {A B : ℕ}
    (h : is_gap6_sol A B) (hB : 0 < B) :
    (A : ℝ) ^ 4 < ((B + 6 : ℕ) : ℝ) ^ 13 := by
  have hB4 : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hB
  have hlt : A ^ 4 < (B + 6) ^ 13 :=
    calc
      A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
      _ = (B + 6) ^ 13 := h
  exact_mod_cast hlt

/-! ## Log-method no-go (`C1 ≥ 1` loses to `B⁴/A⁴`) -/

theorem logA_gt_thirteen_of_B_ge_B0 {A B : ℕ}
    (h : is_gap6_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
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

/-- `exp(−C1 log A log(B+6)) < B⁴/A⁴` for every `C1 ≥ 1` on
    a gap-6 solution with `B ≥ B0`. Same cutoff as `62383af`:
    `C1 < 1` would be needed. -/
theorem hGen_exp_lt_ratio_gap6
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {A B : ℕ} (hsol : is_gap6_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + 6 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  set a : ℝ := log (A : ℝ)
  set c : ℝ := log ((B + 6 : ℕ) : ℝ)
  set C : ℝ := ((B + 6 : ℕ) : ℝ)
  have hAgt1 : 1 < A := A_gt_one_of_sol_pos hsol hB
  have hCgt1 : 1 < B + 6 :=
    lt_of_lt_of_le (by decide : 1 < 6) (Nat.le_add_left 6 B)
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (0 : ℕ) < A := lt_trans Nat.zero_lt_one hAgt1
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C := by
    have : 0 < B + 6 := Nat.add_pos_right B (by decide : 0 < 6)
    have : (0 : ℝ) < ((B + 6 : ℕ) : ℝ) := by exact_mod_cast this
    simpa [C] using this
  have hCgt : (1 : ℝ) < C := by
    have : (1 : ℝ) < ((B + 6 : ℕ) : ℝ) := by exact_mod_cast hCgt1
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

theorem C1_floor_hGen_loses_gap6 {A B : ℕ}
    (hsol : is_gap6_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + 6 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio_gap6
    (le_of_lt (by
      simpa [C1_floor_eq_logs] using
        BealMatveevBeal.MatveevThreeLogs.C1_floor_gt_one))
    hsol hB hB0

/-! ## Floor form / LLL no-go (`B+6`) -/

noncomputable def floorFormThird_gap6 (C : ℝ) (A B : ℕ) : ℝ :=
  (4 : ℝ) * ⌊C * log (A : ℝ)⌋ - 13 * ⌊C * log ((B + 6 : ℕ) : ℝ)⌋

/-- `|4⌊C log A⌋ − 13⌊C log(B+6)⌋ − C Λ| < 17` for every real `C`. -/
theorem floor_form_approx_of_C_gap6 (C : ℝ) (A B : ℕ) :
    |floorFormThird_gap6 C A B - C * Lambda_gap6 A B| < 17 := by
  set a : ℝ := C * log (A : ℝ)
  set cval : ℝ := C * log ((B + 6 : ℕ) : ℝ)
  have hΛ : C * Lambda_gap6 A B = 4 * a - 13 * cval := by
    simp only [Lambda_gap6, a, cval]
    ring
  have hft : floorFormThird_gap6 C A B = (4 : ℝ) * ⌊a⌋ - 13 * ⌊cval⌋ := rfl
  have hform :
      floorFormThird_gap6 C A B - C * Lambda_gap6 A B =
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

theorem floor_form_third_abs_lt_gap6 {C : ℝ} (hC : 0 < C) (A B : ℕ) :
    |floorFormThird_gap6 C A B| < 17 + C * |Lambda_gap6 A B| := by
  have happ := floor_form_approx_of_C_gap6 C A B
  have hmul : |C * Lambda_gap6 A B| = C * |Lambda_gap6 A B| := by
    rw [abs_mul, abs_of_pos hC]
  have := abs_sub_abs_le_abs_sub
    (floorFormThird_gap6 C A B) (C * Lambda_gap6 A B)
  linarith [happ, this, hmul]

/-- No scaling `C > 0` yields a Baker–Davenport witness
    `r > 17 + C/B0` on a gap-6 solution with `B ≥ B0`. -/
theorem hLLL_method_fails_gap6 :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        is_gap6_sol A B →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |floorFormThird_gap6 C A B| := by
  intro C hC A B hsol hB hB0
  rintro ⟨r, hgt, hle⟩
  have htri := floor_form_third_abs_lt_gap6 hC A B
  have hLam := abs_Lambda_gap6_lt_inv_B hsol hB
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hBle : (B0_nat : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hB0
  have hCΛ : C * |Lambda_gap6 A B| < C / (B0_nat : ℝ) := by
    have hmid : C * |Lambda_gap6 A B| < C * (1 / (B : ℝ)) :=
      mul_lt_mul_of_pos_left hLam hC
    have hrew : C * (1 / (B : ℝ)) = C / (B : ℝ) := mul_one_div _ _
    have hCB : C / (B : ℝ) ≤ C / (B0_nat : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hC) hB0pos hBle
    linarith [hmid, hrew, hCB]
  have hthird : |floorFormThird_gap6 C A B| < 17 + C / (B0_nat : ℝ) := by
    linarith [htri, hCΛ]
  linarith [hgt, hle, hthird]

theorem no_uniform_c_cubic_in_N_gap6 :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (BealMatveevBeal.MatveevThreeLogs.coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) :=
  BealMatveevBeal.MatveevThreeLogs.no_uniform_c_cubic_in_N

theorem coeffCount3_zero_ten_ten_ten_gap6 :
    BealMatveevBeal.MatveevThreeLogs.coeffCount3 0 10 10 10 = 1331 :=
  BealMatveevBeal.MatveevThreeLogs.coeffCount3_zero_ten_ten_ten

theorem no_uniform_c_easy_half_gap6 :
    (1 / 2 : ℝ) * 1 * 1 < 242 := by
  norm_num

/-! ## `hGen_gap6` / `hLLL_gap6` stay `def Prop` -/

/-- Matveev 2000 Theorem 1.4, n=2, displayed `C1_floor` exponential
    on a gap-6 solution. Not in Mathlib 4.12. Instantiating it at
    `B ≥ B0` does not beat `B⁴/A⁴`. -/
def hGen_gap6 : Prop :=
  ∀ A B : ℕ,
    is_gap6_sol A B →
      0 < B →
        |Lambda_gap6 A B| >
          exp (-(C1_floor : ℝ) * log (A : ℝ) *
            log ((B + 6 : ℕ) : ℝ))

/-- Bugeaud / LLL close for gap-6: ratio upper bound ⇒ `B ≤ B0`.
    The displayed lattice does not inhabit it. -/
def hLLL_gap6 : Prop :=
  (∀ A B : ℕ, is_gap6_sol A B → 0 < B →
      |Lambda_gap6 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4) →
    baker_bound_gap6

def baker_bound_gap6_of_hGen_hLLL : Prop :=
  hGen_gap6 → hLLL_gap6 → baker_bound_gap6

def baker_bound_gap6_of_hGen_hLLL_gap6 : Prop :=
  baker_bound_gap6_of_hGen_hLLL

/-! ## Combined unconditional no-go (no Darmon–Merel axiom) -/

/-- Log and LLL methods lose on `B ≥ B0`. Remaining solutions are
    coprime with `A > B0`, `B` odd, `A` even. `3 ∣ B` is
    impossible. `5 ∣ B` is compatible. Darmon–Merel `(4,4,13)`
    would be refuted by any such solution. `baker_bound_gap6`
    stays uninhabited as a named theorem. -/
theorem baker_bound_gap6_unconditional_nogo {A B : ℕ}
    (hsol : is_gap6_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + 6 : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (∀ C : ℝ, 0 < C →
      ¬ ∃ r : ℝ,
        17 + C / (B0_nat : ℝ) < r ∧
          r ≤ |floorFormThird_gap6 C A B|) ∧
    Nat.Coprime A B ∧
    B0_nat < A ∧
    Odd B ∧
    Even A ∧
    ¬ 3 ∣ B ∧
    (darmon_merel_44_13_no_coprime → False) := by
  refine ⟨?_, ?_, coprime_of_sol_gap6 hsol, ?_,
    B_odd_of_sol_gap6 hsol, A_even_of_sol_gap6 hsol,
    three_not_dvd_B_of_sol hsol, ?_⟩
  · intro C1 hC1
    exact hGen_exp_lt_ratio_gap6 hC1 hsol hB hB0
  · intro C hC
    exact hLLL_method_fails_gap6 C hC A B hsol hB hB0
  · exact Nat.lt_of_le_of_lt hB0 (A_gt_B_of_sol hsol hB)
  · intro hDM
    have hA0 : A = 0 ∨ B = 0 :=
      hDM A B (B + 6) (coprime_of_sol_gap6 hsol) hsol
    cases hA0 with
    | inl hA => exact A_ne_zero_of_sol hsol hA
    | inr hB0' => exact (ne_of_gt hB) hB0'

/-! ## Axiom-relative close (reuses `BealTrueV25`, no new axiom) -/

/-- Every gap-6 solution is impossible relative to
    `darmon_merel_4413_axiom`. Unlike gap-1 there is no `(1,0)`. -/
theorem no_gap6_of_axiom {A B : ℕ}
    (hsol : is_gap6_sol A B) : False := by
  have hDM := BealMatveevBeal.BealTrueV25.darmon_merel_4413_axiom
  have hA0 : A = 0 ∨ B = 0 :=
    hDM A B (B + 6) (coprime_of_sol_gap6 hsol) hsol
  cases hA0 with
  | inl hA => exact A_ne_zero_of_sol hsol hA
  | inr hB0 =>
      subst hB0
      exact no_sol_when_even_B hsol (by decide : Even 0)

/-- Vacuous `B ≤ B0` for every gap-6 solution, relative to the
    existing Darmon–Merel axiom. Not named `baker_bound_gap6`. -/
theorem baker_bound_gap6_true {A B : ℕ}
    (hsol : is_gap6_sol A B) : B ≤ B0_nat :=
  (no_gap6_of_axiom hsol).elim

theorem baker_bound_gap6_true_of_axiom {A B : ℕ}
    (hsol : is_gap6_sol A B) : B ≤ B0_nat :=
  baker_bound_gap6_true hsol

#check C1_floor_eq
#check B0_nat_eq
#check not_gap6_one_zero
#check gcd_B_C_eq_gcd_six
#check gcd_B_C_dvd_six
#check gcd_A_B_eq_one_of_sol
#check coprime_of_sol_gap6
#check B_odd_of_sol_gap6
#check A_even_of_sol_gap6
#check no_sol_when_even_B
#check A_gt_B_of_sol
#check three_dvd_B_forces_three_dvd_A_gap6
#check no_sol_when_three_dvd_B_gap6
#check A_pow_four_mod5_eq_one_of_five_dvd_B
#check not_five_dvd_A_of_five_dvd_B
#check coprime_of_remaining_gap6
#check hGen_exp_lt_ratio_gap6
#check C1_floor_hGen_loses_gap6
#check floor_form_approx_of_C_gap6
#check hLLL_method_fails_gap6
#check no_uniform_c_cubic_in_N_gap6
#check no_uniform_c_easy_half_gap6
#check hGen_gap6
#check hLLL_gap6
#check baker_bound_gap6_of_hGen_hLLL
#check baker_bound_gap6_unconditional_nogo
#check baker_bound_gap6
#check no_gap6_of_axiom
#check baker_bound_gap6_true
#check baker_bound_gap6_true_of_axiom
#print axioms gcd_A_B_eq_one_of_sol
#print axioms B_odd_of_sol_gap6
#print axioms no_sol_when_even_B
#print axioms no_sol_when_three_dvd_B_gap6
#print axioms three_dvd_B_forces_three_dvd_A_gap6
#print axioms hGen_exp_lt_ratio_gap6
#print axioms C1_floor_hGen_loses_gap6
#print axioms hLLL_method_fails_gap6
#print axioms baker_bound_gap6_unconditional_nogo
#print axioms no_gap6_of_axiom
#print axioms baker_bound_gap6_true

end BealMatveevBeal.BealGap6
