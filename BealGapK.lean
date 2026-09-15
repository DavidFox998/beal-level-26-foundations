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
import BealGap15

/-!
# Gap-K generic `A⁴ + B⁴ = (B+k)¹³` (not a `∀k` close)

Successor of `0af0b77` (`v24-v24x-final-gap15-nogo`).
Generic infrastructure for `C = B+k`. This does **not** inhabit
`∀ k A B, ¬ is_gapK_sol k A B`: gap-1 has `(1,0)`, and every
fourth-power gap `k = m⁴` gives the parametric solution
`A = m¹³`, `B = 0`. Even `k` does **not** force `B` odd
(gap-10 leftover even `B`). Even `B` does **not** always die
as three `/2` residue `6` or `14` (only some `k ≡ 2 mod 4`
branches). `p ∣ k` last-step `p³ X = C₁¹³` contradicts only
when `v_p(k) = 1`. Residue kills need the displayed
congruence. Recover existing axiom closes for
`k ∈ {2,3,4,5,6,7,8,9,11,12,13,14,15}` and odd-`B` gap-10.
Do **not** delete `BealGap1`–`BealGap15`.

`hGen_gapK` / `hLLL_gapK` / `baker_bound_gapK` stay `def Prop`.
Every `C1 ≥ 1` loses to `B⁴/A⁴` on `B ≥ B0` and `k ≥ 1`.
0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

set_option maxHeartbeats 800000

open Real

namespace BealMatveevBeal.BealGapK

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_logs :
    C1_floor = BealMatveevBeal.MatveevThreeLogs.C1_floor := rfl

theorem B0_nat_eq_logs :
    B0_nat = BealMatveevBeal.MatveevThreeLogs.B0_nat := rfl

/-! ## Gap-K equation -/

def is_gapK_sol (k A B : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = (B + k) ^ 13

/-- Kernel Baker bound for a fixed gap `k`. Stays a `def Prop`. -/
def baker_bound_gapK (k : ℕ) : Prop :=
  ∀ A B : ℕ, is_gapK_sol k A B → B ≤ B0_nat

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealTrueV25.darmon_merel_44_13_no_coprime

/-! ## Real solutions that block a uniform `∀k` nogo -/

theorem gap1_one_zero : is_gapK_sol 1 1 0 := by
  unfold is_gapK_sol
  decide

theorem fourth_power_gap_at_zero (m : ℕ) :
    is_gapK_sol (m ^ 4) (m ^ 13) 0 := by
  unfold is_gapK_sol
  have hL : (m ^ 13) ^ 4 + 0 ^ 4 = m ^ 52 := by
    rw [zero_pow (by decide : 4 ≠ 0), add_zero, ← pow_mul]
  have hR : (0 + m ^ 4) ^ 13 = m ^ 52 := by
    rw [zero_add, ← pow_mul]
  rw [hL, hR]

theorem zero_zero_of_zero_gap : is_gapK_sol 0 0 0 := by
  unfold is_gapK_sol
  decide

/-! ## `gcd(B, B+k) = gcd(B, k)` divides `k` -/

theorem gcd_B_C_eq_gcd_k (k B : ℕ) :
    Nat.gcd B (B + k) = Nat.gcd B k := by
  rw [Nat.gcd_comm B (B + k), Nat.add_comm B k]
  exact (Nat.gcd_add_self_left k B).trans (Nat.gcd_comm k B)

theorem gcd_B_C_dvd_k (k B : ℕ) : Nat.gcd B (B + k) ∣ k := by
  rw [gcd_B_C_eq_gcd_k]
  exact Nat.gcd_dvd_right B k

theorem gcd_B_C_dvd_k_gapK (k B : ℕ) : Nat.gcd B (B + k) ∣ k :=
  gcd_B_C_dvd_k k B

/-! ## Parity (honest: even `k` forces `A` even only) -/

theorem A_even_of_sol_of_even_k {k A B : ℕ}
    (hk : Even k) (h : is_gapK_sol k A B) : Even A := by
  by_contra hA
  have hAodd : Odd A := Nat.not_even_iff_odd.1 hA
  have hA4 : Odd (A ^ 4) := hAodd.pow
  by_cases hBeven : Even B
  · have hC : Even (B + k) := hBeven.add hk
    have hC13 : Even ((B + k) ^ 13) :=
      (Nat.even_pow' (by decide : 13 ≠ 0)).2 hC
    have hB4 : Even (B ^ 4) :=
      (Nat.even_pow' (by decide : 4 ≠ 0)).2 hBeven
    have hL : Odd (A ^ 4 + B ^ 4) := hA4.add_even hB4
    exact Nat.not_even_iff_odd.2 (h ▸ hL) hC13
  · have hBodd : Odd B := Nat.not_even_iff_odd.1 hBeven
    have hC : Odd (B + k) := hBodd.add_even hk
    have hC13 : Odd ((B + k) ^ 13) := hC.pow
    have hB4 : Odd (B ^ 4) := hBodd.pow
    have hL : Even (A ^ 4 + B ^ 4) := hA4.add_odd hB4
    exact (Nat.not_even_iff_odd.2 (h ▸ hC13)) hL

theorem B_even_of_sol_of_odd_k {k A B : ℕ}
    (hk : Odd k) (h : is_gapK_sol k A B) : Even B := by
  by_contra hne
  have hBodd : Odd B := Nat.not_even_iff_odd.1 hne
  have hCeven : Even (B + k) := hBodd.add_odd hk
  have h16C : 16 ∣ (B + k) ^ 4 :=
    BealCatalanZsig.even_pow_four_dvd_sixteen hCeven
  have h16R : 16 ∣ (B + k) ^ 13 :=
    dvd_trans h16C (pow_dvd_pow (B + k) (by decide : 4 ≤ 13))
  have hR : (B + k) ^ 13 % 16 = 0 := Nat.mod_eq_zero_of_dvd h16R
  have hB4 : B ^ 4 % 16 = 1 :=
    BealCatalanZsig.odd_pow_four_mod_sixteen hBodd
  by_cases hA : Even A
  · have hA4 : A ^ 4 % 16 = 0 :=
      Nat.mod_eq_zero_of_dvd
        (BealCatalanZsig.even_pow_four_dvd_sixteen hA)
    have hL : (A ^ 4 + B ^ 4) % 16 = 1 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + k) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (1 : ℕ) ≠ 0) this
  · have hAodd : Odd A := Nat.not_even_iff_odd.1 hA
    have hA4 : A ^ 4 % 16 = 1 :=
      BealCatalanZsig.odd_pow_four_mod_sixteen hAodd
    have hL : (A ^ 4 + B ^ 4) % 16 = 2 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + k) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (2 : ℕ) ≠ 0) this

theorem A_odd_of_sol_of_odd_k {k A B : ℕ}
    (hk : Odd k) (h : is_gapK_sol k A B) : Odd A := by
  have hBeven := B_even_of_sol_of_odd_k hk h
  have hCodd : Odd (B + k) := hBeven.add_odd hk
  have hC13 : Odd ((B + k) ^ 13) := hCodd.pow
  have hB4 : Even (B ^ 4) := (Nat.even_pow' (by decide : 4 ≠ 0)).2 hBeven
  rw [← Nat.not_even_iff_odd]
  intro hAeven
  have hA4 : Even (A ^ 4) := (Nat.even_pow' (by decide : 4 ≠ 0)).2 hAeven
  have hL : Even (A ^ 4 + B ^ 4) := hA4.add hB4
  exact (Nat.not_even_iff_odd.2 (h ▸ hC13)) hL

theorem A_parity_of_sol_gapK {k A B : ℕ} (h : is_gapK_sol k A B) :
    (Even k → Even A) ∧ (Odd k → Odd A) :=
  ⟨fun hk => A_even_of_sol_of_even_k hk h,
    fun hk => A_odd_of_sol_of_odd_k hk h⟩

/-! ## Size: `A > B` for `k ≥ 1`, `B > 0`; `A ≠ 0` when `k ≥ 1` -/

theorem two_mul_lt_succ_pow_five (B : ℕ) : 2 * B ^ 4 < (B + 1) ^ 5 := by
  have hexp : (B + 1) ^ 5 =
      B ^ 5 + 5 * B ^ 4 + 10 * B ^ 3 + 10 * B ^ 2 + 5 * B + 1 := by
    ring
  rw [hexp]
  cases B with
  | zero => decide
  | succ n =>
    set B := n + 1
    have hB5 : B ^ 5 = B * B ^ 4 := by rw [pow_succ']
    have h6 : 6 * B ^ 4 ≤ B ^ 5 + 5 * B ^ 4 := by
      rw [hB5, ← add_mul]
      exact Nat.mul_le_mul_right (B ^ 4) (by decide : 6 ≤ B + 5)
    have hpos : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 (Nat.succ_pos n)
    have h2 : 2 * B ^ 4 < 6 * B ^ 4 :=
      Nat.mul_lt_mul_of_pos_right (by decide : 2 < 6) hpos
    have hrest :
        B ^ 5 + 5 * B ^ 4 ≤
          B ^ 5 + 5 * B ^ 4 + 10 * B ^ 3 + 10 * B ^ 2 + 5 * B + 1 :=
      Nat.le_add_right _ _
    exact lt_of_lt_of_le (lt_of_lt_of_le h2 h6) hrest

theorem two_mul_B_pow_four_lt_add_k_pow {k B : ℕ} (hk : 1 ≤ k) :
    2 * B ^ 4 < (B + k) ^ 13 := by
  have h5 : 2 * B ^ 4 < (B + 1) ^ 5 := two_mul_lt_succ_pow_five B
  have hB1 : 1 ≤ B + 1 := Nat.succ_le_succ (Nat.zero_le B)
  have h513 : (B + 1) ^ 5 ≤ (B + 1) ^ 13 :=
    Nat.pow_le_pow_right hB1 (by decide : 5 ≤ 13)
  have hle : B + 1 ≤ B + k := Nat.add_le_add_left hk B
  have h13 : (B + 1) ^ 13 ≤ (B + k) ^ 13 :=
    Nat.pow_le_pow_left hle 13
  exact lt_of_lt_of_le (lt_of_lt_of_le h5 h513) h13

theorem A_gt_B_of_sol {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (_hB : 0 < B) : B < A := by
  by_contra hle
  have hAB : A ≤ B := Nat.not_lt.mp hle
  have hA4 : A ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hAB 4
  have hsum : A ^ 4 + B ^ 4 ≤ 2 * B ^ 4 := by
    have := Nat.add_le_add hA4 (le_refl (B ^ 4))
    simpa [two_mul] using this
  have hlt := two_mul_B_pow_four_lt_add_k_pow (k := k) (B := B) hk
  have : A ^ 4 + B ^ 4 < (B + k) ^ 13 := lt_of_le_of_lt hsum hlt
  exact (ne_of_lt this) h

theorem A_ne_zero_of_sol {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) : A ≠ 0 := by
  intro hA
  subst hA
  have heq : B ^ 4 = (B + k) ^ 13 := by
    simpa [is_gapK_sol] using h
  by_cases hB : B = 0
  · subst hB
    have : (k : ℕ) ^ 13 ≠ 0 :=
      pow_ne_zero 13 (ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hk))
    exact this (by simpa using heq.symm)
  · have hpos : 0 < B := Nat.pos_of_ne_zero hB
    have hB4pos : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hpos
    have hlt1 : B ^ 4 < 2 * B ^ 4 := by
      have : 1 * B ^ 4 < 2 * B ^ 4 :=
        Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hB4pos
      simpa using this
    have hlt2 := two_mul_B_pow_four_lt_add_k_pow (k := k) (B := B) hk
    exact (ne_of_lt (lt_trans hlt1 hlt2)) heq

theorem A_gt_one_of_sol_pos {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 0 < B) : 1 < A :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) (A_gt_B_of_sol hk h hB)

/-! ## Fourth powers and `p ∣ k` forces `p ∣ A` -/

theorem fourth_pow_mod3 (a : ℕ) : a ^ 4 % 3 = 0 ∨ a ^ 4 % 3 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod3 a

theorem fourth_pow_mod5 (a : ℕ) : a ^ 4 % 5 = 0 ∨ a ^ 4 % 5 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod5 a

theorem fourth_pow_mod7 (a : ℕ) :
    a ^ 4 % 7 = 0 ∨ a ^ 4 % 7 = 1 ∨ a ^ 4 % 7 = 2 ∨ a ^ 4 % 7 = 4 :=
  BealMatveevBeal.BealGap7.fourth_pow_mod7 a

theorem fourth_pow_mod11 (a : ℕ) :
    a ^ 4 % 11 = 0 ∨ a ^ 4 % 11 = 1 ∨ a ^ 4 % 11 = 3 ∨
      a ^ 4 % 11 = 4 ∨ a ^ 4 % 11 = 5 ∨ a ^ 4 % 11 = 9 :=
  BealMatveevBeal.BealGap11.fourth_pow_mod11 a

theorem fourth_pow_mod13 (a : ℕ) :
    a ^ 4 % 13 = 0 ∨ a ^ 4 % 13 = 1 ∨ a ^ 4 % 13 = 3 ∨
      a ^ 4 % 13 = 9 :=
  BealMatveevBeal.BealGap13.fourth_pow_mod13 a

theorem pow13_mod3 (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  BealMatveevBeal.BealGap1.pow13_mod3_eq_self c

theorem pow13_mod5 (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  BealMatveevBeal.BealGap1.pow13_mod5_eq_self c

theorem pow13_mod7 (c : ℕ) : c ^ 13 % 7 = c % 7 :=
  BealMatveevBeal.BealGap7.pow13_mod7 c

theorem pow13_mod11 (c : ℕ) : c ^ 13 % 11 = (c % 11) ^ 3 % 11 :=
  BealMatveevBeal.BealGap13.pow13_mod11 c

theorem p_dvd_k_forces_p_dvd_A_gapK {k A B p : ℕ}
    (hp : Nat.Prime p) (hk : p ∣ k) (hB : p ∣ B)
    (h : is_gapK_sol k A B) : p ∣ A := by
  have hB4 : p ∣ B ^ 4 := dvd_pow hB (by decide)
  have hC : p ∣ B + k := Nat.dvd_add hB hk
  have hC13 : p ∣ (B + k) ^ 13 := dvd_pow hC (by decide)
  have hsum : p ∣ A ^ 4 + B ^ 4 := by
    rw [h]
    exact hC13
  have hA4 : p ∣ A ^ 4 := (Nat.dvd_add_left hB4).mp hsum
  exact Nat.Prime.dvd_of_dvd_pow hp hA4

theorem val_one_of_prime_dvd {p k : ℕ}
    (hk : p ∣ k) (hn : ¬ p ^ 2 ∣ k) :
    ∃ k', k = p * k' ∧ ¬ p ∣ k' := by
  obtain ⟨k', hk'⟩ := hk
  refine ⟨k', hk', ?_⟩
  intro h
  obtain ⟨k'', hk''⟩ := h
  exact hn ⟨k'', by rw [hk', hk'', mul_assoc, pow_two]⟩

/-! ## `p ∣ k` and `v_p(k)=1`: 3/5/7/11/13-descent -/

theorem both_three_dvd_of_sum_fourth_mod3_zero {X Y : ℕ}
    (h : (X ^ 4 + Y ^ 4) % 3 = 0) : 3 ∣ X ∧ 3 ∣ Y :=
  BealMatveevBeal.BealGap6.both_three_dvd_of_sum_fourth_mod3_zero h

theorem sum_fourth_of_mul_three (x y : ℕ) :
    (3 * x) ^ 4 + (3 * y) ^ 4 = 81 * (x ^ 4 + y ^ 4) :=
  BealMatveevBeal.BealGap6.sum_fourth_of_mul_three x y

theorem both_five_dvd_of_sum_fourth_mod5_zero {X Y : ℕ}
    (h : (X ^ 4 + Y ^ 4) % 5 = 0) : 5 ∣ X ∧ 5 ∣ Y :=
  BealMatveevBeal.BealGap5.both_five_dvd_of_sum_fourth_mod5_zero h

theorem sum_fourth_of_mul_five (x y : ℕ) :
    (5 * x) ^ 4 + (5 * y) ^ 4 = 625 * (x ^ 4 + y ^ 4) :=
  BealMatveevBeal.BealGap5.sum_fourth_of_mul_five x y

theorem both_seven_dvd_of_sum_fourth_mod7_zero {X Y : ℕ}
    (h : (X ^ 4 + Y ^ 4) % 7 = 0) : 7 ∣ X ∧ 7 ∣ Y :=
  BealMatveevBeal.BealGap7.both_seven_dvd_of_sum_fourth_mod7_zero h

theorem sum_fourth_of_mul_seven (x y : ℕ) :
    (7 * x) ^ 4 + (7 * y) ^ 4 = 2401 * (x ^ 4 + y ^ 4) :=
  BealMatveevBeal.BealGap7.sum_fourth_of_mul_seven x y

theorem both_eleven_dvd_of_sum_fourth_mod11_zero {X Y : ℕ}
    (h : (X ^ 4 + Y ^ 4) % 11 = 0) : 11 ∣ X ∧ 11 ∣ Y :=
  BealMatveevBeal.BealGap11.both_eleven_dvd_of_sum_fourth_mod11_zero h

theorem sum_fourth_of_mul_eleven (x y : ℕ) :
    (11 * x) ^ 4 + (11 * y) ^ 4 = 14641 * (x ^ 4 + y ^ 4) :=
  BealMatveevBeal.BealGap11.sum_fourth_of_mul_eleven x y

theorem both_thirteen_dvd_of_sum_fourth_mod13_zero {X Y : ℕ}
    (h : (X ^ 4 + Y ^ 4) % 13 = 0) : 13 ∣ X ∧ 13 ∣ Y :=
  BealMatveevBeal.BealGap13.both_thirteen_dvd_of_sum_fourth_mod13_zero h

theorem sum_fourth_of_mul_thirteen (x y : ℕ) :
    (13 * x) ^ 4 + (13 * y) ^ 4 = 28561 * (x ^ 4 + y ^ 4) :=
  BealMatveevBeal.BealGap13.sum_fourth_of_mul_thirteen x y

/-- `3 ∣ B` and `v_3(k)=1` die: last `27 X = C₁¹³` with `C₁ ≡ k/3 ≢ 0`. -/
theorem no_sol_when_p_dvd_k_three_gapK {k A B : ℕ}
    (hk : 3 ∣ k) (hn9 : ¬ 9 ∣ k) (h : is_gapK_sol k A B)
    (h3 : 3 ∣ B) : False := by
  have hA3 := p_dvd_k_forces_p_dvd_A_gapK Nat.prime_three hk h3 h
  obtain ⟨A1, hA⟩ := hA3
  obtain ⟨B1, hB⟩ := h3
  obtain ⟨k', hk', hk'n⟩ := val_one_of_prime_dvd hk (by
    simpa [pow_two] using hn9)
  have hC : B + k = 3 * (B1 + k') := by
    rw [hB, hk', mul_add]
  have hsol1 : (3 * A1) ^ 4 + (3 * B1) ^ 4 = (3 * (B1 + k')) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 81 * (A1 ^ 4 + B1 ^ 4) = 3 ^ 13 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_three, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 3 ^ 9 * (B1 + k') ^ 13 := by
    have hpow : (3 : ℕ) ^ 13 = 81 * 3 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 81)
    rw [heq1, hpow, mul_assoc]
  have hmod1 : (A1 ^ 4 + B1 ^ 4) % 3 = 0 := by
    have : 3 ∣ 3 ^ 9 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 3 (by decide : 9 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1, hB1d⟩ := both_three_dvd_of_sum_fourth_mod3_zero hmod1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1d
  have heq2src : (3 * A2) ^ 4 + (3 * B2) ^ 4 =
      3 ^ 9 * (B1 + k') ^ 13 := by
    rw [← hA2, ← hB2]; exact h9
  have heq2 : 81 * (A2 ^ 4 + B2 ^ 4) = 3 ^ 9 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_three]; exact heq2src
  have h5eq : A2 ^ 4 + B2 ^ 4 = 3 ^ 5 * (B1 + k') ^ 13 := by
    have hpow : (3 : ℕ) ^ 9 = 81 * 3 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 81)
    rw [heq2, hpow, mul_assoc]
  have hmod2 : (A2 ^ 4 + B2 ^ 4) % 3 = 0 := by
    have : 3 ∣ 3 ^ 5 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 3 (by decide : 5 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h5eq ▸ this)
  obtain ⟨hA2e, hB2e⟩ := both_three_dvd_of_sum_fourth_mod3_zero hmod2
  obtain ⟨A3, hA3e⟩ := hA2e
  obtain ⟨B3, hB3⟩ := hB2e
  have heq3src : (3 * A3) ^ 4 + (3 * B3) ^ 4 =
      3 ^ 5 * (B1 + k') ^ 13 := by
    rw [← hA3e, ← hB3]; exact h5eq
  have heq3 : 81 * (A3 ^ 4 + B3 ^ 4) = 3 ^ 5 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_three]; exact heq3src
  have h1eq : A3 ^ 4 + B3 ^ 4 = 3 * (B1 + k') ^ 13 := by
    have hpow : (3 : ℕ) ^ 5 = 81 * 3 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 81)
    rw [heq3, hpow, mul_assoc]
  have hmod3 : (A3 ^ 4 + B3 ^ 4) % 3 = 0 := by
    have : 3 ∣ 3 * (B1 + k') ^ 13 := dvd_mul_right _ _
    exact Nat.mod_eq_zero_of_dvd (h1eq ▸ this)
  obtain ⟨hA3e', hB3e⟩ := both_three_dvd_of_sum_fourth_mod3_zero hmod3
  obtain ⟨A4, hA4⟩ := hA3e'
  obtain ⟨B4, hB4⟩ := hB3e
  have heq4src : (3 * A4) ^ 4 + (3 * B4) ^ 4 =
      3 * (B1 + k') ^ 13 := by
    rw [← hA4, ← hB4]; exact h1eq
  have heq4 : 81 * (A4 ^ 4 + B4 ^ 4) = 3 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_three]; exact heq4src
  have h27 : 27 * (A4 ^ 4 + B4 ^ 4) = (B1 + k') ^ 13 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (3 : ℕ))
    have hL : 3 * (27 * (A4 ^ 4 + B4 ^ 4)) =
        81 * (A4 ^ 4 + B4 ^ 4) := by
      rw [← mul_assoc]
      rfl
    rw [hL]
    exact heq4
  have hC13 : 3 ∣ (B1 + k') ^ 13 :=
    ⟨9 * (A4 ^ 4 + B4 ^ 4), by rw [← h27, ← mul_assoc]; rfl⟩
  have hC1 : 3 ∣ B1 + k' := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hC13
  have hB1three : 3 ∣ B1 := ⟨B2, hB2⟩
  have : 3 ∣ k' := (Nat.dvd_add_left hB1three).mp hC1
  exact hk'n this

/-- `5 ∣ B` and `v_5(k)=1` die: last `125 X = C₁¹³` with `C₁ ≡ k/5 ≢ 0`. -/
theorem no_sol_when_p_dvd_k_five_gapK {k A B : ℕ}
    (hk : 5 ∣ k) (hn25 : ¬ 25 ∣ k) (h : is_gapK_sol k A B)
    (h5 : 5 ∣ B) : False := by
  have hA5 := p_dvd_k_forces_p_dvd_A_gapK Nat.prime_five hk h5 h
  obtain ⟨A1, hA⟩ := hA5
  obtain ⟨B1, hB⟩ := h5
  obtain ⟨k', hk', hk'n⟩ := val_one_of_prime_dvd hk (by
    simpa [pow_two] using hn25)
  have hC : B + k = 5 * (B1 + k') := by
    rw [hB, hk', mul_add]
  have hsol1 : (5 * A1) ^ 4 + (5 * B1) ^ 4 = (5 * (B1 + k')) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 625 * (A1 ^ 4 + B1 ^ 4) = 5 ^ 13 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_five, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 5 ^ 9 * (B1 + k') ^ 13 := by
    have hpow : (5 : ℕ) ^ 13 = 625 * 5 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 625)
    rw [heq1, hpow, mul_assoc]
  have hmod1 : (A1 ^ 4 + B1 ^ 4) % 5 = 0 := by
    have : 5 ∣ 5 ^ 9 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 5 (by decide : 9 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1, hB1d⟩ := both_five_dvd_of_sum_fourth_mod5_zero hmod1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1d
  have heq2src : (5 * A2) ^ 4 + (5 * B2) ^ 4 =
      5 ^ 9 * (B1 + k') ^ 13 := by
    rw [← hA2, ← hB2]; exact h9
  have heq2 : 625 * (A2 ^ 4 + B2 ^ 4) = 5 ^ 9 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_five]; exact heq2src
  have h5eq : A2 ^ 4 + B2 ^ 4 = 5 ^ 5 * (B1 + k') ^ 13 := by
    have hpow : (5 : ℕ) ^ 9 = 625 * 5 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 625)
    rw [heq2, hpow, mul_assoc]
  have hmod2 : (A2 ^ 4 + B2 ^ 4) % 5 = 0 := by
    have : 5 ∣ 5 ^ 5 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 5 (by decide : 5 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h5eq ▸ this)
  obtain ⟨hA2e, hB2e⟩ := both_five_dvd_of_sum_fourth_mod5_zero hmod2
  obtain ⟨A3, hA3e⟩ := hA2e
  obtain ⟨B3, hB3⟩ := hB2e
  have heq3src : (5 * A3) ^ 4 + (5 * B3) ^ 4 =
      5 ^ 5 * (B1 + k') ^ 13 := by
    rw [← hA3e, ← hB3]; exact h5eq
  have heq3 : 625 * (A3 ^ 4 + B3 ^ 4) = 5 ^ 5 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_five]; exact heq3src
  have h1eq : A3 ^ 4 + B3 ^ 4 = 5 * (B1 + k') ^ 13 := by
    have hpow : (5 : ℕ) ^ 5 = 625 * 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 625)
    rw [heq3, hpow, mul_assoc]
  have hmod3 : (A3 ^ 4 + B3 ^ 4) % 5 = 0 := by
    have : 5 ∣ 5 * (B1 + k') ^ 13 := dvd_mul_right _ _
    exact Nat.mod_eq_zero_of_dvd (h1eq ▸ this)
  obtain ⟨hA3e', hB3e⟩ := both_five_dvd_of_sum_fourth_mod5_zero hmod3
  obtain ⟨A4, hA4⟩ := hA3e'
  obtain ⟨B4, hB4⟩ := hB3e
  have heq4src : (5 * A4) ^ 4 + (5 * B4) ^ 4 =
      5 * (B1 + k') ^ 13 := by
    rw [← hA4, ← hB4]; exact h1eq
  have heq4 : 625 * (A4 ^ 4 + B4 ^ 4) = 5 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_five]; exact heq4src
  have h125 : 125 * (A4 ^ 4 + B4 ^ 4) = (B1 + k') ^ 13 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (5 : ℕ))
    have hL : 5 * (125 * (A4 ^ 4 + B4 ^ 4)) =
        625 * (A4 ^ 4 + B4 ^ 4) := by
      rw [← mul_assoc]
      rfl
    rw [hL]
    exact heq4
  have hC13 : 5 ∣ (B1 + k') ^ 13 :=
    ⟨25 * (A4 ^ 4 + B4 ^ 4), by rw [← h125, ← mul_assoc]; rfl⟩
  have hC1 : 5 ∣ B1 + k' := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hC13
  have hB1five : 5 ∣ B1 := ⟨B2, hB2⟩
  have : 5 ∣ k' := (Nat.dvd_add_left hB1five).mp hC1
  exact hk'n this

/-- `7 ∣ B` and `v_7(k)=1` die: last `343 X = C₁¹³` with `C₁ ≡ k/7 ≢ 0`. -/
theorem no_sol_when_p_dvd_k_seven_gapK {k A B : ℕ}
    (hk : 7 ∣ k) (hn49 : ¬ 49 ∣ k) (h : is_gapK_sol k A B)
    (h7 : 7 ∣ B) : False := by
  have hA7 :=
    p_dvd_k_forces_p_dvd_A_gapK
      BealMatveevBeal.BealGap7.prime_seven hk h7 h
  obtain ⟨A1, hA⟩ := hA7
  obtain ⟨B1, hB⟩ := h7
  obtain ⟨k', hk', hk'n⟩ := val_one_of_prime_dvd hk (by
    simpa [pow_two] using hn49)
  have hC : B + k = 7 * (B1 + k') := by
    rw [hB, hk', mul_add]
  have hsol1 : (7 * A1) ^ 4 + (7 * B1) ^ 4 = (7 * (B1 + k')) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 2401 * (A1 ^ 4 + B1 ^ 4) = 7 ^ 13 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_seven, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 7 ^ 9 * (B1 + k') ^ 13 := by
    have hpow : (7 : ℕ) ^ 13 = 2401 * 7 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2401)
    rw [heq1, hpow, mul_assoc]
  have hmod1 : (A1 ^ 4 + B1 ^ 4) % 7 = 0 := by
    have : 7 ∣ 7 ^ 9 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 7 (by decide : 9 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1, hB1d⟩ := both_seven_dvd_of_sum_fourth_mod7_zero hmod1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1d
  have heq2src : (7 * A2) ^ 4 + (7 * B2) ^ 4 =
      7 ^ 9 * (B1 + k') ^ 13 := by
    rw [← hA2, ← hB2]; exact h9
  have heq2 : 2401 * (A2 ^ 4 + B2 ^ 4) = 7 ^ 9 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_seven]; exact heq2src
  have h5eq : A2 ^ 4 + B2 ^ 4 = 7 ^ 5 * (B1 + k') ^ 13 := by
    have hpow : (7 : ℕ) ^ 9 = 2401 * 7 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2401)
    rw [heq2, hpow, mul_assoc]
  have hmod2 : (A2 ^ 4 + B2 ^ 4) % 7 = 0 := by
    have : 7 ∣ 7 ^ 5 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 7 (by decide : 5 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h5eq ▸ this)
  obtain ⟨hA2e, hB2e⟩ := both_seven_dvd_of_sum_fourth_mod7_zero hmod2
  obtain ⟨A3, hA3e⟩ := hA2e
  obtain ⟨B3, hB3⟩ := hB2e
  have heq3src : (7 * A3) ^ 4 + (7 * B3) ^ 4 =
      7 ^ 5 * (B1 + k') ^ 13 := by
    rw [← hA3e, ← hB3]; exact h5eq
  have heq3 : 2401 * (A3 ^ 4 + B3 ^ 4) = 7 ^ 5 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_seven]; exact heq3src
  have h1eq : A3 ^ 4 + B3 ^ 4 = 7 * (B1 + k') ^ 13 := by
    have hpow : (7 : ℕ) ^ 5 = 2401 * 7 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2401)
    rw [heq3, hpow, mul_assoc]
  have hmod3 : (A3 ^ 4 + B3 ^ 4) % 7 = 0 := by
    have : 7 ∣ 7 * (B1 + k') ^ 13 := dvd_mul_right _ _
    exact Nat.mod_eq_zero_of_dvd (h1eq ▸ this)
  obtain ⟨hA3e', hB3e⟩ := both_seven_dvd_of_sum_fourth_mod7_zero hmod3
  obtain ⟨A4, hA4⟩ := hA3e'
  obtain ⟨B4, hB4⟩ := hB3e
  have heq4src : (7 * A4) ^ 4 + (7 * B4) ^ 4 =
      7 * (B1 + k') ^ 13 := by
    rw [← hA4, ← hB4]; exact h1eq
  have heq4 : 2401 * (A4 ^ 4 + B4 ^ 4) = 7 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_seven]; exact heq4src
  have h343 : 343 * (A4 ^ 4 + B4 ^ 4) = (B1 + k') ^ 13 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (7 : ℕ))
    have hL : 7 * (343 * (A4 ^ 4 + B4 ^ 4)) =
        2401 * (A4 ^ 4 + B4 ^ 4) := by
      rw [← mul_assoc]
      rfl
    rw [hL]
    exact heq4
  have hC13 : 7 ∣ (B1 + k') ^ 13 :=
    ⟨49 * (A4 ^ 4 + B4 ^ 4), by rw [← h343, ← mul_assoc]; rfl⟩
  have hC1 : 7 ∣ B1 + k' :=
    Nat.Prime.dvd_of_dvd_pow BealMatveevBeal.BealGap7.prime_seven hC13
  have hB1seven : 7 ∣ B1 := ⟨B2, hB2⟩
  have : 7 ∣ k' := (Nat.dvd_add_left hB1seven).mp hC1
  exact hk'n this

/-- `11 ∣ B` and `v_11(k)=1` die: last `1331 X = C₁¹³` with `C₁ ≡ k/11 ≢ 0`. -/
theorem no_sol_when_p_dvd_k_eleven_gapK {k A B : ℕ}
    (hk : 11 ∣ k) (hn121 : ¬ 121 ∣ k) (h : is_gapK_sol k A B)
    (h11 : 11 ∣ B) : False := by
  have hA11 :=
    p_dvd_k_forces_p_dvd_A_gapK
      BealMatveevBeal.BealGap11.prime_eleven hk h11 h
  obtain ⟨A1, hA⟩ := hA11
  obtain ⟨B1, hB⟩ := h11
  obtain ⟨k', hk', hk'n⟩ := val_one_of_prime_dvd hk (by
    simpa [pow_two] using hn121)
  have hC : B + k = 11 * (B1 + k') := by
    rw [hB, hk', mul_add]
  have hsol1 : (11 * A1) ^ 4 + (11 * B1) ^ 4 =
      (11 * (B1 + k')) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 14641 * (A1 ^ 4 + B1 ^ 4) = 11 ^ 13 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_eleven, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 11 ^ 9 * (B1 + k') ^ 13 := by
    have hpow : (11 : ℕ) ^ 13 = 14641 * 11 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 14641)
    rw [heq1, hpow, mul_assoc]
  have hmod1 : (A1 ^ 4 + B1 ^ 4) % 11 = 0 := by
    have : 11 ∣ 11 ^ 9 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 11 (by decide : 9 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1, hB1d⟩ := both_eleven_dvd_of_sum_fourth_mod11_zero hmod1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1d
  have heq2src : (11 * A2) ^ 4 + (11 * B2) ^ 4 =
      11 ^ 9 * (B1 + k') ^ 13 := by
    rw [← hA2, ← hB2]; exact h9
  have heq2 : 14641 * (A2 ^ 4 + B2 ^ 4) = 11 ^ 9 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_eleven]; exact heq2src
  have h5eq : A2 ^ 4 + B2 ^ 4 = 11 ^ 5 * (B1 + k') ^ 13 := by
    have hpow : (11 : ℕ) ^ 9 = 14641 * 11 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 14641)
    rw [heq2, hpow, mul_assoc]
  have hmod2 : (A2 ^ 4 + B2 ^ 4) % 11 = 0 := by
    have : 11 ∣ 11 ^ 5 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 11 (by decide : 5 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h5eq ▸ this)
  obtain ⟨hA2e, hB2e⟩ := both_eleven_dvd_of_sum_fourth_mod11_zero hmod2
  obtain ⟨A3, hA3e⟩ := hA2e
  obtain ⟨B3, hB3⟩ := hB2e
  have heq3src : (11 * A3) ^ 4 + (11 * B3) ^ 4 =
      11 ^ 5 * (B1 + k') ^ 13 := by
    rw [← hA3e, ← hB3]; exact h5eq
  have heq3 : 14641 * (A3 ^ 4 + B3 ^ 4) = 11 ^ 5 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_eleven]; exact heq3src
  have h1eq : A3 ^ 4 + B3 ^ 4 = 11 * (B1 + k') ^ 13 := by
    have hpow : (11 : ℕ) ^ 5 = 14641 * 11 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 14641)
    rw [heq3, hpow, mul_assoc]
  have hmod3 : (A3 ^ 4 + B3 ^ 4) % 11 = 0 := by
    have : 11 ∣ 11 * (B1 + k') ^ 13 := dvd_mul_right _ _
    exact Nat.mod_eq_zero_of_dvd (h1eq ▸ this)
  obtain ⟨hA3e', hB3e⟩ := both_eleven_dvd_of_sum_fourth_mod11_zero hmod3
  obtain ⟨A4, hA4⟩ := hA3e'
  obtain ⟨B4, hB4⟩ := hB3e
  have heq4src : (11 * A4) ^ 4 + (11 * B4) ^ 4 =
      11 * (B1 + k') ^ 13 := by
    rw [← hA4, ← hB4]; exact h1eq
  have heq4 : 14641 * (A4 ^ 4 + B4 ^ 4) = 11 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_eleven]; exact heq4src
  have h1331 : 1331 * (A4 ^ 4 + B4 ^ 4) = (B1 + k') ^ 13 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (11 : ℕ))
    have hL : 11 * (1331 * (A4 ^ 4 + B4 ^ 4)) =
        14641 * (A4 ^ 4 + B4 ^ 4) := by
      rw [← mul_assoc]
      rfl
    rw [hL]
    exact heq4
  have hC13 : 11 ∣ (B1 + k') ^ 13 :=
    ⟨121 * (A4 ^ 4 + B4 ^ 4), by rw [← h1331, ← mul_assoc]; rfl⟩
  have hC1 : 11 ∣ B1 + k' :=
    Nat.Prime.dvd_of_dvd_pow BealMatveevBeal.BealGap11.prime_eleven hC13
  have hB1el : 11 ∣ B1 := ⟨B2, hB2⟩
  have : 11 ∣ k' := (Nat.dvd_add_left hB1el).mp hC1
  exact hk'n this

/-- `13 ∣ B` and `v_13(k)=1` die: last `2197 X = C₁¹³` with `C₁ ≡ k/13 ≢ 0`. -/
theorem no_sol_when_p_dvd_k_thirteen_gapK {k A B : ℕ}
    (hk : 13 ∣ k) (hn169 : ¬ 169 ∣ k) (h : is_gapK_sol k A B)
    (h13 : 13 ∣ B) : False := by
  have hA13 :=
    p_dvd_k_forces_p_dvd_A_gapK
      BealMatveevBeal.BealGap13.prime_thirteen hk h13 h
  obtain ⟨A1, hA⟩ := hA13
  obtain ⟨B1, hB⟩ := h13
  obtain ⟨k', hk', hk'n⟩ := val_one_of_prime_dvd hk (by
    simpa [pow_two] using hn169)
  have hC : B + k = 13 * (B1 + k') := by
    rw [hB, hk', mul_add]
  have hsol1 : (13 * A1) ^ 4 + (13 * B1) ^ 4 =
      (13 * (B1 + k')) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 28561 * (A1 ^ 4 + B1 ^ 4) = 13 ^ 13 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_thirteen, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 13 ^ 9 * (B1 + k') ^ 13 := by
    have hpow : (13 : ℕ) ^ 13 = 28561 * 13 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 28561)
    rw [heq1, hpow, mul_assoc]
  have hmod1 : (A1 ^ 4 + B1 ^ 4) % 13 = 0 := by
    have : 13 ∣ 13 ^ 9 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 13 (by decide : 9 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1, hB1d⟩ := both_thirteen_dvd_of_sum_fourth_mod13_zero hmod1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1d
  have heq2src : (13 * A2) ^ 4 + (13 * B2) ^ 4 =
      13 ^ 9 * (B1 + k') ^ 13 := by
    rw [← hA2, ← hB2]; exact h9
  have heq2 : 28561 * (A2 ^ 4 + B2 ^ 4) = 13 ^ 9 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_thirteen]; exact heq2src
  have h5eq : A2 ^ 4 + B2 ^ 4 = 13 ^ 5 * (B1 + k') ^ 13 := by
    have hpow : (13 : ℕ) ^ 9 = 28561 * 13 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 28561)
    rw [heq2, hpow, mul_assoc]
  have hmod2 : (A2 ^ 4 + B2 ^ 4) % 13 = 0 := by
    have : 13 ∣ 13 ^ 5 * (B1 + k') ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 13 (by decide : 5 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h5eq ▸ this)
  obtain ⟨hA2e, hB2e⟩ := both_thirteen_dvd_of_sum_fourth_mod13_zero hmod2
  obtain ⟨A3, hA3e⟩ := hA2e
  obtain ⟨B3, hB3⟩ := hB2e
  have heq3src : (13 * A3) ^ 4 + (13 * B3) ^ 4 =
      13 ^ 5 * (B1 + k') ^ 13 := by
    rw [← hA3e, ← hB3]; exact h5eq
  have heq3 : 28561 * (A3 ^ 4 + B3 ^ 4) = 13 ^ 5 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_thirteen]; exact heq3src
  have h1eq : A3 ^ 4 + B3 ^ 4 = 13 * (B1 + k') ^ 13 := by
    have hpow : (13 : ℕ) ^ 5 = 28561 * 13 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 28561)
    rw [heq3, hpow, mul_assoc]
  have hmod3 : (A3 ^ 4 + B3 ^ 4) % 13 = 0 := by
    have : 13 ∣ 13 * (B1 + k') ^ 13 := dvd_mul_right _ _
    exact Nat.mod_eq_zero_of_dvd (h1eq ▸ this)
  obtain ⟨hA3e', hB3e⟩ := both_thirteen_dvd_of_sum_fourth_mod13_zero hmod3
  obtain ⟨A4, hA4⟩ := hA3e'
  obtain ⟨B4, hB4⟩ := hB3e
  have heq4src : (13 * A4) ^ 4 + (13 * B4) ^ 4 =
      13 * (B1 + k') ^ 13 := by
    rw [← hA4, ← hB4]; exact h1eq
  have heq4 : 28561 * (A4 ^ 4 + B4 ^ 4) = 13 * (B1 + k') ^ 13 := by
    rw [← sum_fourth_of_mul_thirteen]; exact heq4src
  have h2197 : 2197 * (A4 ^ 4 + B4 ^ 4) = (B1 + k') ^ 13 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (13 : ℕ))
    have hL : 13 * (2197 * (A4 ^ 4 + B4 ^ 4)) =
        28561 * (A4 ^ 4 + B4 ^ 4) := by
      rw [← mul_assoc]
      rfl
    rw [hL]
    exact heq4
  have hC13 : 13 ∣ (B1 + k') ^ 13 :=
    ⟨169 * (A4 ^ 4 + B4 ^ 4), by rw [← h2197, ← mul_assoc]; rfl⟩
  have hC1 : 13 ∣ B1 + k' :=
    Nat.Prime.dvd_of_dvd_pow BealMatveevBeal.BealGap13.prime_thirteen hC13
  have hB1th : 13 ∣ B1 := ⟨B2, hB2⟩
  have : 13 ∣ k' := (Nat.dvd_add_left hB1th).mp hC1
  exact hk'n this

/-! ## `p ∤ k` residue kills (congruence hypotheses) -/

theorem no_sol_when_three_dvd_B_residue_gapK {k A B : ℕ}
    (h : is_gapK_sol k A B) (hk : ¬ 3 ∣ k) (h3 : 3 ∣ B)
    (hkmod : k % 3 = 2) : False := by
  have hB4 : B ^ 4 % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h3 (by decide))
  have hC : (B + k) % 3 = 2 := by
    have : B % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    rw [Nat.add_mod, this, hkmod]
  have hC13 : (B + k) ^ 13 % 3 = 2 := by
    rw [pow13_mod3, hC]
  have hsum : (A ^ 4 + B ^ 4) % 3 = (B + k) ^ 13 % 3 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod3 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · rw [h1] at hsum
    exact absurd hsum (by decide)

theorem no_sol_when_five_dvd_B_residue_gapK {k A B : ℕ}
    (h : is_gapK_sol k A B) (_hk : ¬ 5 ∣ k) (h5 : 5 ∣ B)
    (hkmod : k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4) : False := by
  have hB4 : B ^ 4 % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h5 (by decide))
  have hC : (B + k) % 5 = k % 5 := by
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [Nat.add_mod, this]
  have hC13 : (B + k) ^ 13 % 5 = k % 5 := by
    rw [pow13_mod5, hC]
  have hsum : (A ^ 4 + B ^ 4) % 5 = (B + k) ^ 13 % 5 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  have hAres := fourth_pow_mod5 A
  rcases hkmod with hk2 | hk3 | hk4
  · rw [hk2] at hsum
    rcases hAres with h0 | h1
    · rw [h0] at hsum; exact absurd hsum (by decide)
    · rw [h1] at hsum; exact absurd hsum (by decide)
  · rw [hk3] at hsum
    rcases hAres with h0 | h1
    · rw [h0] at hsum; exact absurd hsum (by decide)
    · rw [h1] at hsum; exact absurd hsum (by decide)
  · rw [hk4] at hsum
    rcases hAres with h0 | h1
    · rw [h0] at hsum; exact absurd hsum (by decide)
    · rw [h1] at hsum; exact absurd hsum (by decide)

theorem no_sol_when_seven_dvd_B_residue_gapK {k A B : ℕ}
    (h : is_gapK_sol k A B) (_hk : ¬ 7 ∣ k) (h7 : 7 ∣ B)
    (hkmod : k % 7 = 3 ∨ k % 7 = 5 ∨ k % 7 = 6) : False := by
  have hB4 : B ^ 4 % 7 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h7 (by decide))
  have hC : (B + k) % 7 = k % 7 := by
    have : B % 7 = 0 := Nat.mod_eq_zero_of_dvd h7
    rw [Nat.add_mod, this]
  have hC13 : (B + k) ^ 13 % 7 = k % 7 := by
    rw [pow13_mod7, hC]
  have hsum : (A ^ 4 + B ^ 4) % 7 = (B + k) ^ 13 % 7 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  have hAres := fourth_pow_mod7 A
  rcases hkmod with hk3 | hk5 | hk6
  · rw [hk3] at hsum
    rcases hAres with h0 | h1 | h2 | h4
    · rw [h0] at hsum; exact absurd hsum (by decide)
    · rw [h1] at hsum; exact absurd hsum (by decide)
    · rw [h2] at hsum; exact absurd hsum (by decide)
    · rw [h4] at hsum; exact absurd hsum (by decide)
  · rw [hk5] at hsum
    rcases hAres with h0 | h1 | h2 | h4
    · rw [h0] at hsum; exact absurd hsum (by decide)
    · rw [h1] at hsum; exact absurd hsum (by decide)
    · rw [h2] at hsum; exact absurd hsum (by decide)
    · rw [h4] at hsum; exact absurd hsum (by decide)
  · rw [hk6] at hsum
    rcases hAres with h0 | h1 | h2 | h4
    · rw [h0] at hsum; exact absurd hsum (by decide)
    · rw [h1] at hsum; exact absurd hsum (by decide)
    · rw [h2] at hsum; exact absurd hsum (by decide)
    · rw [h4] at hsum; exact absurd hsum (by decide)

/-! ## Remaining coprime when no prime of `k` divides `B` -/

theorem gcd_A_B_eq_one_of_remaining_gapK {k A B : ℕ}
    (h : is_gapK_sol k A B)
    (hforall : ∀ p : ℕ, Nat.Prime p → p ∣ k → ¬ p ∣ B) :
    Nat.gcd A B = 1 := by
  set d := Nat.gcd A B
  by_contra hne
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
  have hpA : p ∣ A := dvd_trans hpd (Nat.gcd_dvd_left A B)
  have hpB : p ∣ B := dvd_trans hpd (Nat.gcd_dvd_right A B)
  have hpC13 : p ∣ (B + k) ^ 13 := by
    have hA4 : p ∣ A ^ 4 := dvd_pow hpA (by decide)
    have hB4 : p ∣ B ^ 4 := dvd_pow hpB (by decide)
    have hsum : p ∣ A ^ 4 + B ^ 4 := Nat.dvd_add hA4 hB4
    simpa [is_gapK_sol] using (h ▸ hsum)
  have hpC : p ∣ B + k := Nat.Prime.dvd_of_dvd_pow hp hpC13
  have hpk : p ∣ k := (Nat.dvd_add_left hpB).mp hpC
  exact hforall p hp hpk hpB

theorem coprime_of_remaining_gapK {k A B : ℕ}
    (h : is_gapK_sol k A B)
    (hforall : ∀ p : ℕ, Nat.Prime p → p ∣ k → ¬ p ∣ B) :
    Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_remaining_gapK h hforall

/-! ## Axiom-relative close on positive coprime solutions -/

theorem no_positive_coprime_gapK_of_axiom {k A B : ℕ}
    (h : is_gapK_sol k A B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcop : Nat.Coprime A B) : False := by
  have hDM := BealMatveevBeal.BealTrueV25.darmon_merel_4413_axiom
  have hA0 : A = 0 ∨ B = 0 := hDM A B (B + k) hcop h
  cases hA0 with
  | inl hA' => exact hA hA'
  | inr hB' => exact hB hB'

theorem baker_bound_gapK_true_of_positive_coprime {k A B : ℕ}
    (h : is_gapK_sol k A B) (hA : A ≠ 0) (hB : B ≠ 0)
    (hcop : Nat.Coprime A B) : B ≤ B0_nat :=
  (no_positive_coprime_gapK_of_axiom h hA hB hcop).elim

/-! ## Recover existing one-by-one axiom closes -/

theorem recover_no_gap2_of_axiom {A B : ℕ}
    (h : is_gapK_sol 2 A B) : False :=
  BealMatveevBeal.BealGap2.no_gap2_of_axiom h

theorem recover_no_gap3_of_axiom {A B : ℕ}
    (h : is_gapK_sol 3 A B) : False :=
  BealMatveevBeal.BealTrueV25.no_gap3_of_axiom A B h

theorem recover_no_gap4_of_axiom {A B : ℕ}
    (h : is_gapK_sol 4 A B) : False :=
  BealMatveevBeal.BealGap4.no_gap4_of_axiom h

theorem recover_no_gap5_of_axiom {A B : ℕ}
    (h : is_gapK_sol 5 A B) : False :=
  BealMatveevBeal.BealGap5.no_gap5_of_axiom h

theorem recover_no_gap6_of_axiom {A B : ℕ}
    (h : is_gapK_sol 6 A B) : False :=
  BealMatveevBeal.BealGap6.no_gap6_of_axiom h

theorem recover_no_gap7_of_axiom {A B : ℕ}
    (h : is_gapK_sol 7 A B) : False :=
  BealMatveevBeal.BealGap7.no_gap7_of_axiom h

theorem recover_no_gap8_of_axiom {A B : ℕ}
    (h : is_gapK_sol 8 A B) : False :=
  BealMatveevBeal.BealGap8.no_gap8_of_axiom h

theorem recover_no_gap9_of_axiom {A B : ℕ}
    (h : is_gapK_sol 9 A B) : False :=
  BealMatveevBeal.BealGap9.no_gap9_of_axiom h

theorem recover_no_gap10_of_odd_B_of_axiom {A B : ℕ}
    (h : is_gapK_sol 10 A B) (hOdd : Odd B) : False :=
  BealMatveevBeal.BealGap10.no_gap10_of_odd_B_of_axiom h hOdd

theorem recover_no_gap11_of_axiom {A B : ℕ}
    (h : is_gapK_sol 11 A B) : False :=
  BealMatveevBeal.BealGap11.no_gap11_of_axiom h

theorem recover_no_gap12_of_axiom {A B : ℕ}
    (h : is_gapK_sol 12 A B) : False :=
  BealMatveevBeal.BealGap12.no_gap12_of_axiom h

theorem recover_no_gap13_of_axiom {A B : ℕ}
    (h : is_gapK_sol 13 A B) : False :=
  BealMatveevBeal.BealGap13.no_gap13_of_axiom h

theorem recover_no_gap14_of_axiom {A B : ℕ}
    (h : is_gapK_sol 14 A B) : False :=
  BealMatveevBeal.BealGap14.no_gap14_of_axiom h

theorem recover_no_gap15_of_axiom {A B : ℕ}
    (h : is_gapK_sol 15 A B) : False :=
  BealMatveevBeal.BealGap15.no_gap15_of_axiom h

/-! ## Logarithmic form (`B+k`, `k ≥ 1`) -/

noncomputable def Lambda_gapK (k A B : ℕ) : ℝ :=
  4 * log (A : ℝ) - 13 * log ((B + k : ℕ) : ℝ)

theorem A_pow_real_add {k A B : ℕ} (h : is_gapK_sol k A B) :
    (A : ℝ) ^ 4 + (B : ℝ) ^ 4 = ((B + k : ℕ) : ℝ) ^ 13 := by
  have h' : ((A ^ 4 + B ^ 4 : ℕ) : ℝ) = (((B + k) ^ 13 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [Nat.cast_add, Nat.cast_pow] using h'

theorem A_pow_pos_of_sol {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) :
    (0 : ℝ) < (A : ℝ) ^ 4 := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol hk h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  exact pow_pos hApos 4

theorem Lambda_gapK_eq_log_div {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) :
    Lambda_gapK k A B =
      log ((A : ℝ) ^ 4 / ((B + k : ℕ) : ℝ) ^ 13) := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol hk h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hCpos : (0 : ℝ) < ((B + k : ℕ) : ℝ) := by
    have : 0 < B + k := Nat.add_pos_right B hk
    exact_mod_cast this
  unfold Lambda_gapK
  have h4 : (4 : ℝ) * log (A : ℝ) = log ((A : ℝ) ^ 4) :=
    (Real.log_pow (A : ℝ) 4).symm
  have h13 : (13 : ℝ) * log ((B + k : ℕ) : ℝ) =
      log (((B + k : ℕ) : ℝ) ^ 13) :=
    (Real.log_pow ((B + k : ℕ) : ℝ) 13).symm
  rw [h4, h13, Real.log_div (pow_pos hApos 4).ne' (pow_pos hCpos 13).ne']

theorem abs_Lambda_gapK_eq_log_one_plus {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 0 < B) :
    |Lambda_gapK k A B| = log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have hA4pos := A_pow_pos_of_sol hk h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hu : (0 : ℝ) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    div_pos (pow_pos hBpos 4) hA4pos
  have hsum := A_pow_real_add h
  have hratio :
      (A : ℝ) ^ 4 / ((B + k : ℕ) : ℝ) ^ 13 =
        1 / (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    have hne : (A : ℝ) ^ 4 ≠ 0 := hA4pos.ne'
    have hden :
        (1 : ℝ) + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 =
          ((A : ℝ) ^ 4 + (B : ℝ) ^ 4) / (A : ℝ) ^ 4 := by
      field_simp [hne]
    rw [hden, one_div_div, hsum]
  have hΛ := Lambda_gapK_eq_log_div hk h
  have h1u : (0 : ℝ) < 1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    add_pos_of_nonneg_of_pos zero_le_one hu
  have hlog :
      Lambda_gapK k A B = -log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    rw [hΛ, hratio, Real.log_div one_ne_zero h1u.ne', log_one, zero_sub]
  rw [hlog, abs_neg,
    abs_of_nonneg (log_nonneg (le_of_lt (lt_add_of_pos_right 1 hu)))]

theorem abs_Lambda_gapK_le_ratio {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 0 < B) :
    |Lambda_gapK k A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  have hA4pos := A_pow_pos_of_sol hk h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hu : (0 : ℝ) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    div_pos (pow_pos hBpos 4) hA4pos
  have hx : (0 : ℝ) < 1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    add_pos_of_nonneg_of_pos zero_le_one hu
  have hlog := Real.log_le_sub_one_of_pos hx
  have : log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ≤
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
    simpa using hlog
  rwa [abs_Lambda_gapK_eq_log_one_plus hk h hB]

theorem B_pow_five_add_B_pow_four_lt_add_k_pow {k B : ℕ}
    (hk : 1 ≤ k) (_hB : 0 < B) :
    (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + k : ℕ) : ℝ) ^ 13 := by
  have hx : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : ((B + k : ℕ) : ℝ) = (B : ℝ) + (k : ℝ) := by
    rw [Nat.cast_add]
  have h1 : ((B + 1 : ℕ) : ℝ) = (B : ℝ) + 1 := by
    rw [Nat.cast_add, Nat.cast_one]
  have h5 : (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 1 : ℕ) : ℝ) ^ 5 := by
    rw [h1]
    have hexp : ((B : ℝ) + 1) ^ 5 =
        (B : ℝ) ^ 5 + 5 * (B : ℝ) ^ 4 + 10 * (B : ℝ) ^ 3 +
          10 * (B : ℝ) ^ 2 + 5 * (B : ℝ) + 1 := by
      ring
    have h3 : (0 : ℝ) ≤ (B : ℝ) ^ 3 := pow_nonneg hx 3
    have h2 : (0 : ℝ) ≤ (B : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hexp, h3, h2, hx]
  have hle : ((B + 1 : ℕ) : ℝ) ≤ ((B + k : ℕ) : ℝ) := by
    have : B + 1 ≤ B + k := Nat.add_le_add_left hk B
    exact_mod_cast this
  have hC1 : (1 : ℝ) ≤ ((B + 1 : ℕ) : ℝ) := by
    have : 1 ≤ B + 1 := Nat.succ_le_succ (Nat.zero_le B)
    exact_mod_cast this
  have h513 : ((B + 1 : ℕ) : ℝ) ^ 5 ≤ ((B + 1 : ℕ) : ℝ) ^ 13 :=
    pow_le_pow_right hC1 (by decide : (5 : ℕ) ≤ 13)
  have h13 : ((B + 1 : ℕ) : ℝ) ^ 13 ≤ ((B + k : ℕ) : ℝ) ^ 13 :=
    pow_le_pow_left (le_trans (by norm_num : (0 : ℝ) ≤ 1) hC1) hle 13
  exact lt_of_lt_of_le (lt_of_lt_of_le h5 h513) h13

theorem A_pow_gt_B_pow_five {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 0 < B) :
    (B : ℝ) ^ 5 < (A : ℝ) ^ 4 := by
  have hA4 : (A : ℝ) ^ 4 =
      ((B + k : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 := by
    linarith [A_pow_real_add h]
  have hsum := B_pow_five_add_B_pow_four_lt_add_k_pow hk hB
  linarith [hA4, hsum]

theorem ratio_lt_inv_B {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 0 < B) :
    (B : ℝ) ^ 4 / (A : ℝ) ^ 4 < 1 / (B : ℝ) := by
  have hA4pos := A_pow_pos_of_sol hk h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hgt := A_pow_gt_B_pow_five hk h hB
  have : (B : ℝ) ^ 4 * (B : ℝ) < (A : ℝ) ^ 4 := by
    have : (B : ℝ) ^ 5 = (B : ℝ) ^ 4 * (B : ℝ) := by ring
    rwa [this] at hgt
  rw [div_lt_div_iff hA4pos hBpos, one_mul]
  exact this

theorem abs_Lambda_gapK_lt_inv_B {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 0 < B) :
    |Lambda_gapK k A B| < 1 / (B : ℝ) :=
  lt_of_le_of_lt (abs_Lambda_gapK_le_ratio hk h hB) (ratio_lt_inv_B hk h hB)

theorem A_pow_lt_C_pow {k A B : ℕ}
    (h : is_gapK_sol k A B) (hB : 0 < B) :
    (A : ℝ) ^ 4 < ((B + k : ℕ) : ℝ) ^ 13 := by
  have hB4 : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hB
  have hlt : A ^ 4 < (B + k) ^ 13 :=
    calc
      A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
      _ = (B + k) ^ 13 := h
  exact_mod_cast hlt

/-! ## Log-method no-go (`C1 ≥ 1` loses to `B⁴/A⁴`) -/

theorem logA_gt_thirteen_of_B_ge_B0 {k A B : ℕ}
    (hk : 1 ≤ k) (h : is_gapK_sol k A B) (hB : 0 < B)
    (hB0 : B0_nat ≤ B) :
    (13 : ℝ) < log (A : ℝ) := by
  have hAgt := A_gt_B_of_sol hk h hB
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

theorem hGen_exp_lt_ratio_gapK
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {k A B : ℕ} (hk : 1 ≤ k) (hsol : is_gapK_sol k A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  set a : ℝ := log (A : ℝ)
  set c : ℝ := log ((B + k : ℕ) : ℝ)
  set C : ℝ := ((B + k : ℕ) : ℝ)
  have hAgt1 : 1 < A := A_gt_one_of_sol_pos hk hsol hB
  have hBgt : 1 < B :=
    lt_of_lt_of_le (by decide : 1 < 1000000)
      (by simpa [B0_nat_eq] using hB0)
  have hCgt1 : 1 < B + k :=
    lt_of_lt_of_le hBgt (Nat.le_add_right B k)
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (0 : ℕ) < A := lt_trans Nat.zero_lt_one hAgt1
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C := by
    have : 0 < B + k := Nat.add_pos_right B hk
    have : (0 : ℝ) < ((B + k : ℕ) : ℝ) := by exact_mod_cast this
    simpa [C] using this
  have hCgt : (1 : ℝ) < C := by
    have : (1 : ℝ) < ((B + k : ℕ) : ℝ) := by exact_mod_cast hCgt1
    simpa [C] using this
  have ha : (13 : ℝ) < a := logA_gt_thirteen_of_B_ge_B0 hk hsol hB hB0
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

theorem C1_floor_hGen_loses_gapK {k A B : ℕ}
    (hk : 1 ≤ k) (hsol : is_gapK_sol k A B) (hB : 0 < B)
    (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio_gapK
    (le_of_lt (by
      simpa [C1_floor_eq_logs] using
        BealMatveevBeal.MatveevThreeLogs.C1_floor_gt_one))
    hk hsol hB hB0

/-! ## Floor form / LLL no-go (`B+k`) -/

noncomputable def floorFormThird_gapK (k : ℕ) (C : ℝ) (A B : ℕ) : ℝ :=
  (4 : ℝ) * ⌊C * log (A : ℝ)⌋ - 13 * ⌊C * log ((B + k : ℕ) : ℝ)⌋

theorem floor_form_approx_of_C_gapK (k : ℕ) (C : ℝ) (A B : ℕ) :
    |floorFormThird_gapK k C A B - C * Lambda_gapK k A B| < 17 := by
  set a : ℝ := C * log (A : ℝ)
  set cval : ℝ := C * log ((B + k : ℕ) : ℝ)
  have hΛ : C * Lambda_gapK k A B = 4 * a - 13 * cval := by
    simp only [Lambda_gapK, a, cval]
    ring
  have hft : floorFormThird_gapK k C A B = (4 : ℝ) * ⌊a⌋ - 13 * ⌊cval⌋ :=
    rfl
  have hform :
      floorFormThird_gapK k C A B - C * Lambda_gapK k A B =
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

theorem floor_form_third_abs_lt_gapK {k : ℕ} {C : ℝ} (hC : 0 < C)
    (A B : ℕ) :
    |floorFormThird_gapK k C A B| < 17 + C * |Lambda_gapK k A B| := by
  have happ := floor_form_approx_of_C_gapK k C A B
  have hmul : |C * Lambda_gapK k A B| = C * |Lambda_gapK k A B| := by
    rw [abs_mul, abs_of_pos hC]
  have := abs_sub_abs_le_abs_sub
    (floorFormThird_gapK k C A B) (C * Lambda_gapK k A B)
  linarith [happ, this, hmul]

theorem hLLL_method_fails_gapK {k : ℕ} (hk : 1 ≤ k) :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        is_gapK_sol k A B →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |floorFormThird_gapK k C A B| := by
  intro C hC A B hsol hB hB0
  rintro ⟨r, hgt, hle⟩
  have htri := floor_form_third_abs_lt_gapK (k := k) hC A B
  have hLam := abs_Lambda_gapK_lt_inv_B hk hsol hB
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hBle : (B0_nat : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hB0
  have hCΛ : C * |Lambda_gapK k A B| < C / (B0_nat : ℝ) := by
    have hmid : C * |Lambda_gapK k A B| < C * (1 / (B : ℝ)) :=
      mul_lt_mul_of_pos_left hLam hC
    have hrew : C * (1 / (B : ℝ)) = C / (B : ℝ) := mul_one_div _ _
    have hCB : C / (B : ℝ) ≤ C / (B0_nat : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hC) hB0pos hBle
    linarith [hmid, hrew, hCB]
  have hthird : |floorFormThird_gapK k C A B| < 17 + C / (B0_nat : ℝ) := by
    linarith [htri, hCΛ]
  linarith [hgt, hle, hthird]

theorem no_uniform_c_cubic_in_N_gapK :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (BealMatveevBeal.MatveevThreeLogs.coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) :=
  BealMatveevBeal.MatveevThreeLogs.no_uniform_c_cubic_in_N

theorem coeffCount3_zero_ten_ten_ten_gapK :
    BealMatveevBeal.MatveevThreeLogs.coeffCount3 0 10 10 10 = 1331 :=
  BealMatveevBeal.MatveevThreeLogs.coeffCount3_zero_ten_ten_ten

theorem no_uniform_c_easy_half_gapK :
    (1 / 2 : ℝ) * 1 * 1 < 242 := by
  norm_num

/-! ## `hGen_gapK` / `hLLL_gapK` stay `def Prop` -/

def hGen_gapK (k : ℕ) : Prop :=
  ∀ A B : ℕ,
    is_gapK_sol k A B →
      0 < B →
        |Lambda_gapK k A B| >
          exp (-(C1_floor : ℝ) * log (A : ℝ) *
            log ((B + k : ℕ) : ℝ))

def hLLL_gapK (k : ℕ) : Prop :=
  (∀ A B : ℕ, is_gapK_sol k A B → 0 < B →
      |Lambda_gapK k A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4) →
    baker_bound_gapK k

def baker_bound_gapK_of_hGen_hLLL (k : ℕ) : Prop :=
  hGen_gapK k → hLLL_gapK k → baker_bound_gapK k

def baker_bound_gapK_of_hGen_hLLL_gapK (k : ℕ) : Prop :=
  baker_bound_gapK_of_hGen_hLLL k

/-! ## Combined unconditional no-go (no Darmon–Merel axiom) -/

theorem baker_bound_gapK_unconditional_nogo {k A B : ℕ}
    (hk : 1 ≤ k) (hsol : is_gapK_sol k A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + k : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (∀ C : ℝ, 0 < C →
      ¬ ∃ r : ℝ,
        17 + C / (B0_nat : ℝ) < r ∧
          r ≤ |floorFormThird_gapK k C A B|) ∧
    B0_nat < A ∧
    (Even k → Even A) ∧
    (Odd k → Even B ∧ Odd A) ∧
    ((∀ p : ℕ, Nat.Prime p → p ∣ k → ¬ p ∣ B) →
      Nat.Coprime A B) ∧
    ((∀ p : ℕ, Nat.Prime p → p ∣ k → ¬ p ∣ B) →
      darmon_merel_44_13_no_coprime → False) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro C1 hC1
    exact hGen_exp_lt_ratio_gapK hC1 hk hsol hB hB0
  · intro C hC
    exact hLLL_method_fails_gapK hk C hC A B hsol hB hB0
  · exact Nat.lt_of_le_of_lt hB0 (A_gt_B_of_sol hk hsol hB)
  · intro he
    exact A_even_of_sol_of_even_k he hsol
  · intro ho
    exact ⟨B_even_of_sol_of_odd_k ho hsol, A_odd_of_sol_of_odd_k ho hsol⟩
  · intro hforall
    exact coprime_of_remaining_gapK hsol hforall
  · intro hforall hDM
    have hcop : Nat.Coprime A B := coprime_of_remaining_gapK hsol hforall
    have hA0 : A = 0 ∨ B = 0 := hDM A B (B + k) hcop hsol
    cases hA0 with
    | inl hA => exact A_ne_zero_of_sol hk hsol hA
    | inr hB0' => exact (ne_of_gt hB) hB0'

#check C1_floor_eq
#check B0_nat_eq
#check gap1_one_zero
#check fourth_power_gap_at_zero
#check gcd_B_C_eq_gcd_k
#check gcd_B_C_dvd_k
#check gcd_B_C_dvd_k_gapK
#check A_even_of_sol_of_even_k
#check B_even_of_sol_of_odd_k
#check A_odd_of_sol_of_odd_k
#check A_parity_of_sol_gapK
#check p_dvd_k_forces_p_dvd_A_gapK
#check no_sol_when_p_dvd_k_three_gapK
#check no_sol_when_p_dvd_k_five_gapK
#check no_sol_when_p_dvd_k_seven_gapK
#check no_sol_when_p_dvd_k_eleven_gapK
#check no_sol_when_p_dvd_k_thirteen_gapK
#check no_sol_when_three_dvd_B_residue_gapK
#check no_sol_when_five_dvd_B_residue_gapK
#check no_sol_when_seven_dvd_B_residue_gapK
#check gcd_A_B_eq_one_of_remaining_gapK
#check coprime_of_remaining_gapK
#check no_positive_coprime_gapK_of_axiom
#check baker_bound_gapK_true_of_positive_coprime
#check recover_no_gap15_of_axiom
#check recover_no_gap10_of_odd_B_of_axiom
#check hGen_exp_lt_ratio_gapK
#check C1_floor_hGen_loses_gapK
#check floor_form_approx_of_C_gapK
#check hLLL_method_fails_gapK
#check no_uniform_c_cubic_in_N_gapK
#check hGen_gapK
#check hLLL_gapK
#check baker_bound_gapK_of_hGen_hLLL
#check baker_bound_gapK_unconditional_nogo
#check baker_bound_gapK
#print axioms gcd_B_C_dvd_k
#print axioms A_even_of_sol_of_even_k
#print axioms B_even_of_sol_of_odd_k
#print axioms A_odd_of_sol_of_odd_k
#print axioms p_dvd_k_forces_p_dvd_A_gapK
#print axioms no_sol_when_p_dvd_k_three_gapK
#print axioms no_sol_when_p_dvd_k_five_gapK
#print axioms no_sol_when_three_dvd_B_residue_gapK
#print axioms gcd_A_B_eq_one_of_remaining_gapK
#print axioms hGen_exp_lt_ratio_gapK
#print axioms C1_floor_hGen_loses_gapK
#print axioms hLLL_method_fails_gapK
#print axioms baker_bound_gapK_unconditional_nogo
#print axioms no_positive_coprime_gapK_of_axiom
#print axioms recover_no_gap15_of_axiom

end BealMatveevBeal.BealGapK
