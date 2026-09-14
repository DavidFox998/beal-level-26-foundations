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
import BealDarmonMerel44p
import BealDarmonMerel
import BealCatalanZsig
import BealKraus

/-!
# FLT 13 / Darmon–Merel 44p / 3-adic descent no-go
(not a `B ≤ 10⁶` close)

Successor of `515d761` (`v24-v24x-final-Darmon-Merel-44p-nogo`).
`3 ∣ A` is **not** automatic on gap-3: if `B ≡ 2 mod 3` then
`A⁴ ≡ 1 mod 3`. When `3 ∣ B` one does have `3 ∣ A`, and a
three-step 3-adic descent is contradictory: writing
`A = 3 A₁`, `B = 3 B₁`, `C = 3 C₁` with `C₁ = B₁+1` yields
`A₁⁴+B₁⁴ = 3⁹ C₁¹³`, then after two more steps
`27 X = C₁¹³` while `27 ∣ B₁` forces `C₁ ≡ 1 mod 3`, so
`3 ∤ C₁`. Thus there are **no** gap-3 solutions with `3 ∣ B`.
On a solution one therefore has `3 ∤ B` and `gcd(A,B) = 1`,
which is exactly Darmon–Merel's coprime hypothesis. That
theorem, and FLT at exponent 13 (for the thirteenth-power
subcase), are not in Mathlib 4.12.

`baker_bound_gap3` stays uninhabited. Not v25.
`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

namespace BealMatveevBeal.BealFLT13

open BealMatveevBeal.BealDarmonMerel44p
open BealMatveevBeal.BealDarmonMerel
open BealMatveevBeal.BealCatalanZsig
open BealMatveevBeal.BealKraus

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_44p :
    C1_floor = BealMatveevBeal.BealDarmonMerel44p.C1_floor := rfl

theorem B0_nat_eq_44p :
    B0_nat = BealMatveevBeal.BealDarmonMerel44p.B0_nat := rfl

/-! ## Fourth powers modulo 3 -/

theorem three_dvd_both_of_three_dvd_sum_fourth {a b : ℕ}
    (h : 3 ∣ a ^ 4 + b ^ 4) : 3 ∣ a ∧ 3 ∣ b := by
  have h0 : (a ^ 4 + b ^ 4) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
  have ha := pow_four_mod_three_of_mod (n := a)
  have hb := pow_four_mod_three_of_mod (n := b)
  rw [Nat.add_mod] at h0
  rcases ha with ⟨ha0, ha3⟩ | ⟨ha1, _han⟩
  · rcases hb with ⟨_hb0, hb3⟩ | ⟨hb1, _hbn⟩
    · exact ⟨(Nat.dvd_iff_mod_eq_zero 3 a).mpr ha3,
        (Nat.dvd_iff_mod_eq_zero 3 b).mpr hb3⟩
    · rw [ha0, hb1] at h0
      exact absurd h0 (by decide : ¬ (0 + 1) % 3 = 0)
  · rcases hb with ⟨hb0, _hb3⟩ | ⟨hb1, _hbn⟩
    · rw [ha1, hb0] at h0
      exact absurd h0 (by decide : ¬ (1 + 0) % 3 = 0)
    · rw [ha1, hb1] at h0
      exact absurd h0 (by decide : ¬ (1 + 1) % 3 = 0)

/-! ## Scaling identities -/

theorem three_pow_four : (3 : ℕ) ^ 4 = 81 := by decide

theorem mul_three_pow_four (x : ℕ) :
    (3 * x) ^ 4 = 81 * x ^ 4 := by
  rw [mul_pow, three_pow_four]

theorem mul_three_pow_thirteen (x : ℕ) :
    (3 * x) ^ 13 = 3 ^ 13 * x ^ 13 :=
  mul_pow _ _ _

theorem sum_fourth_of_mul_three (a b : ℕ) :
    (3 * a) ^ 4 + (3 * b) ^ 4 = 81 * (a ^ 4 + b ^ 4) := by
  rw [mul_three_pow_four, mul_three_pow_four]
  ring

theorem cancel_three_pow_four {x y : ℕ}
    (h : 81 * x = 3 ^ 13 * y) : x = 3 ^ 9 * y := by
  have h' : (3 : ℕ) ^ 4 * x = 3 ^ 13 * y := by
    simpa [three_pow_four] using h
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (3 : ℕ) ^ 4)
  calc
    (3 : ℕ) ^ 4 * x = 3 ^ 13 * y := h'
    _ = (3 ^ 4 * 3 ^ 9) * y := by rw [← pow_add]
    _ = 3 ^ 4 * (3 ^ 9 * y) := by rw [mul_assoc]

theorem cancel_three_pow_four_to_five {x y : ℕ}
    (h : 81 * x = 3 ^ 9 * y) : x = 3 ^ 5 * y := by
  have h' : (3 : ℕ) ^ 4 * x = 3 ^ 9 * y := by
    simpa [three_pow_four] using h
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (3 : ℕ) ^ 4)
  calc
    (3 : ℕ) ^ 4 * x = 3 ^ 9 * y := h'
    _ = (3 ^ 4 * 3 ^ 5) * y := by rw [← pow_add]
    _ = 3 ^ 4 * (3 ^ 5 * y) := by rw [mul_assoc]

theorem cancel_three_pow_four_to_one {x y : ℕ}
    (h : 81 * x = 3 ^ 5 * y) : x = 3 * y := by
  have h' : (3 : ℕ) ^ 4 * x = 3 ^ 5 * y := by
    simpa [three_pow_four] using h
  have hpow : (3 : ℕ) ^ 5 = 3 ^ 4 * 3 := by
    rw [pow_succ, mul_comm]
  apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (3 : ℕ) ^ 4)
  rw [h', hpow, mul_assoc]

theorem three_dvd_pow_mul (k y : ℕ) (hk : k ≠ 0) :
    3 ∣ 3 ^ k * y :=
  dvd_mul_of_dvd_left (dvd_pow (dvd_refl 3) hk) y

/-! ## Infinite 3-adic descent: no solutions when `3 ∣ B` -/

/-- Gap-3 with `3 ∣ B` is impossible. Three steps of dividing out
    `3` from `A` and `B` produce `27 X = C₁¹³` with `C₁ = B₁+1` and
    `27 ∣ B₁`, so `3 ∤ C₁`. -/
theorem no_sol_when_three_dvd_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : 3 ∣ B) : False := by
  obtain ⟨A1, hA⟩ := three_dvd_A_of_three_dvd_B hsol h3
  obtain ⟨B1, hB⟩ := h3
  have hC : B + 3 = 3 * (B1 + 1) := by
    rw [hB, mul_add, mul_one]
  have hsol1 : (3 * A1) ^ 4 + (3 * B1) ^ 4 =
      (3 * (B1 + 1)) ^ 13 := by
    simpa [hA, hB, hC] using hsol
  have heq1 : 81 * (A1 ^ 4 + B1 ^ 4) =
      3 ^ 13 * (B1 + 1) ^ 13 := by
    rw [← sum_fourth_of_mul_three, hsol1, mul_three_pow_thirteen]
  have h9 : A1 ^ 4 + B1 ^ 4 = 3 ^ 9 * (B1 + 1) ^ 13 :=
    cancel_three_pow_four heq1
  have h3sum1 : 3 ∣ A1 ^ 4 + B1 ^ 4 :=
    h9.symm ▸ three_dvd_pow_mul 9 _ (by decide)
  obtain ⟨hA1, hB1three⟩ :=
    three_dvd_both_of_three_dvd_sum_fourth h3sum1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1three
  have heq2src : (3 * A2) ^ 4 + (3 * B2) ^ 4 =
      3 ^ 9 * (B1 + 1) ^ 13 := by
    simpa [hA2, hB2] using h9
  have heq2 : 81 * (A2 ^ 4 + B2 ^ 4) =
      3 ^ 9 * (B1 + 1) ^ 13 := by
    rwa [sum_fourth_of_mul_three] at heq2src
  have h5 : A2 ^ 4 + B2 ^ 4 = 3 ^ 5 * (B1 + 1) ^ 13 :=
    cancel_three_pow_four_to_five heq2
  have h3sum2 : 3 ∣ A2 ^ 4 + B2 ^ 4 :=
    h5.symm ▸ three_dvd_pow_mul 5 _ (by decide)
  obtain ⟨hA2three, hB2three⟩ :=
    three_dvd_both_of_three_dvd_sum_fourth h3sum2
  obtain ⟨A3, hA3⟩ := hA2three
  obtain ⟨B3, hB3⟩ := hB2three
  have heq3src : (3 * A3) ^ 4 + (3 * B3) ^ 4 =
      3 ^ 5 * (B1 + 1) ^ 13 := by
    simpa [hA3, hB3] using h5
  have heq3 : 81 * (A3 ^ 4 + B3 ^ 4) =
      3 ^ 5 * (B1 + 1) ^ 13 := by
    rwa [sum_fourth_of_mul_three] at heq3src
  have h1 : A3 ^ 4 + B3 ^ 4 = 3 * (B1 + 1) ^ 13 :=
    cancel_three_pow_four_to_one heq3
  have h3sum3 : 3 ∣ A3 ^ 4 + B3 ^ 4 :=
    ⟨(B1 + 1) ^ 13, h1⟩
  obtain ⟨hA3three, hB3three⟩ :=
    three_dvd_both_of_three_dvd_sum_fourth h3sum3
  obtain ⟨A4, hA4⟩ := hA3three
  obtain ⟨B4, hB4⟩ := hB3three
  have heq4src : (3 * A4) ^ 4 + (3 * B4) ^ 4 =
      3 * (B1 + 1) ^ 13 := by
    simpa [hA4, hB4] using h1
  have heq4 : 81 * (A4 ^ 4 + B4 ^ 4) =
      3 * (B1 + 1) ^ 13 := by
    rwa [sum_fourth_of_mul_three] at heq4src
  have h27 : 27 * (A4 ^ 4 + B4 ^ 4) = (B1 + 1) ^ 13 := by
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < (3 : ℕ))
    calc
      3 * (27 * (A4 ^ 4 + B4 ^ 4))
          = 81 * (A4 ^ 4 + B4 ^ 4) := by
            rw [← mul_assoc]
            rfl
      _ = 3 * (B1 + 1) ^ 13 := heq4
  have hC13 : 3 ∣ (B1 + 1) ^ 13 :=
    ⟨9 * (A4 ^ 4 + B4 ^ 4), by
      rw [← h27, ← mul_assoc]
      rfl⟩
  have hC1 : 3 ∣ B1 + 1 := Nat.prime_three.dvd_of_dvd_pow hC13
  have hB1_27 : B1 = 27 * B4 := by
    calc
      B1 = 3 * B2 := hB2
      _ = 3 * (3 * B3) := by rw [hB3]
      _ = 3 * (3 * (3 * B4)) := by rw [hB4]
      _ = 27 * B4 := by
            rw [← mul_assoc, ← mul_assoc]
            rfl
  have hB1_3 : 3 ∣ B1 :=
    ⟨9 * B4, by rw [hB1_27, ← mul_assoc]; rfl⟩
  have h1dvd : 3 ∣ 1 := by
    have hsub : 3 ∣ (B1 + 1) - B1 :=
      Nat.dvd_sub (Nat.le_add_right B1 1) hC1 hB1_3
    rwa [Nat.add_comm B1, Nat.add_sub_cancel] at hsub
  exact (by decide : ¬ (3 ∣ 1)) h1dvd

theorem three_not_dvd_B_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    ¬ 3 ∣ B :=
  fun h3 => no_sol_when_three_dvd_B hsol h3

theorem gcd_one_when_three_not_dvd_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : ¬ 3 ∣ B) :
    Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_not_three_dvd_B hsol h3

theorem coprime_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    Nat.Coprime A B :=
  gcd_one_when_three_not_dvd_B hsol (three_not_dvd_B_of_sol hsol)

/-! ## Fermat shape of thirteenth powers (FLT stays `def Prop`) -/

theorem fermat_shape_of_A_B_pth_powers_reexport {a b C : ℕ}
    (hsol : (a ^ 13) ^ 4 + (b ^ 13) ^ 4 = C ^ 13) :
    (a ^ 4) ^ 13 + (b ^ 4) ^ 13 = C ^ 13 :=
  fermat_shape_of_A_B_pth_powers hsol

/-! ## Remaining coprime case is Darmon–Merel, not in Mathlib 4.12 -/

/-- On a gap-3 solution one necessarily has `3 ∤ B` and
    `gcd(A,B) = 1`. That is Darmon–Merel's coprime hypothesis.
    The theorem itself, and FLT 13 for the thirteenth-power
    subcase, are not in Mathlib 4.12. The displayed residual is
    still not 32, and `A > B0`. -/
theorem baker_bound_gap3_flt13_darmon_merel_nogo {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    ¬ 3 ∣ B ∧
      Nat.Coprime A B ∧
      residualLevelEstimate A B ≠ 32 ∧
      B0_nat < A ∧
      ¬ 13 ∣ 8 ∧ 13 ∣ 26 := by
  have hnot3 : ¬ 3 ∣ B := three_not_dvd_B_of_sol hsol
  have hB044 : BealMatveevBeal.BealDarmonMerel44p.B0_nat ≤ B := by
    simpa [B0_nat_eq_44p] using hB0
  have hnogo := baker_bound_gap3_darmon_merel_44p_nogo hsol hB hB044
  refine ⟨hnot3, coprime_of_sol hsol, hnogo.2.1, ?_, hnogo.2.2.2⟩
  simpa [B0_nat_eq_44p] using hnogo.2.2.1

/-! ## Locked uninhabited Props -/

/-- Darmon–Merel signature `(4,4,13)`: no coprime solutions of
    `x⁴ + y⁴ = z¹³`. Not in Mathlib 4.12. -/
def darmon_merel_44_13_no_coprime : Prop :=
  ∀ x y z : ℕ, Nat.Coprime x y → x ^ 4 + y ^ 4 = z ^ 13 →
    x = 0 ∨ y = 0

def darmon_merel_signature_44p : Prop :=
  BealMatveevBeal.BealDarmonMerel44p.darmon_merel_signature_44p

def fermat_last_theorem_thirteen : Prop :=
  BealMatveevBeal.BealDarmonMerel44p.fermat_last_theorem_thirteen

def ribet_level_lowering_to_32 : Prop :=
  BealMatveevBeal.BealDarmonMerel44p.ribet_level_lowering_to_32

def baker_bound_gap3 : Prop :=
  BealMatveevBeal.BealDarmonMerel44p.baker_bound_gap3

def ribet_level_lowering : Prop :=
  BealMatveevBeal.BealDarmonMerel44p.ribet_level_lowering

#check C1_floor_eq
#check B0_nat_eq
#check three_dvd_both_of_three_dvd_sum_fourth
#check no_sol_when_three_dvd_B
#check three_not_dvd_B_of_sol
#check coprime_of_sol
#check baker_bound_gap3_flt13_darmon_merel_nogo
#check baker_bound_gap3
#check darmon_merel_44_13_no_coprime
#check fermat_last_theorem_thirteen
#print axioms three_dvd_both_of_three_dvd_sum_fourth
#print axioms no_sol_when_three_dvd_B
#print axioms three_not_dvd_B_of_sol
#print axioms coprime_of_sol
#print axioms baker_bound_gap3_flt13_darmon_merel_nogo

end BealMatveevBeal.BealFLT13
