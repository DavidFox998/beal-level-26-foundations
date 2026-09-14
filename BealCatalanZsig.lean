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
import BealKrausZsig
import BealKraus

/-!
# Catalan / Zsigmondy no-go (not a `B ≤ 10⁶` close)

Successor of `1a6e6a1` (`v24-v24x-final-Gaussian-Thue-nogo`).
Gap-3 is `C¹³ − B⁴ = A⁴` with `C = B+3`, not Catalan
`X^p − Y^q = 1`. On `B > 0` one has `C¹³ − B⁴ > 1`.
If `3 ∤ B` then `gcd(A,B) = 1`. A common Gaussian divisor of
`α = A² + i B²` and `ᾱ` still only divides `2A²` and `2B²`.
A hypothetical Zsigmondy prime in `B` does not divide `A`, so
it cannot force `13 ∣ v_p(A)`. Even assuming
`A² + i B² = ε (u+iv)¹³`, the Thue / argument form still
needs `C1 < 5 / log 13 < 2`. Every displayed constant —
`C1_floor`, `242`, `C1 = 2` — is too large.

Mihăilescu, Zsigmondy, and the Gaussian thirteenth-power
factorization stay `def Prop`. `baker_bound_gap3` stays
uninhabited. Not v25.
`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

open Real
open GaussianInt

namespace BealMatveevBeal.BealCatalanZsig

open BealMatveevBeal.BealKraus
open BealMatveevBeal.BealKrausZsig

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_zsig :
    C1_floor = BealMatveevBeal.BealKrausZsig.C1_floor := rfl

theorem B0_nat_eq_zsig :
    B0_nat = BealMatveevBeal.BealKrausZsig.B0_nat := rfl

/-! ## Gap-3 is `C¹³ − B⁴ = A⁴`, not Catalan `= 1` -/

theorem A_pow_four_eq_sub {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    A ^ 4 = (B + 3) ^ 13 - B ^ 4 := by
  rw [← hsol, add_comm, Nat.add_sub_cancel_left]

theorem C_pow_four_gt_B_pow_four_add_one {B : ℕ} (_hB : 0 < B) :
    B ^ 4 + 1 < (B + 3) ^ 4 := by
  have hexp : (B + 3) ^ 4 =
      B ^ 4 + 12 * B ^ 3 + 54 * B ^ 2 + 108 * B + 81 := by ring
  have h81 : B ^ 4 + 1 < B ^ 4 + 81 :=
    Nat.add_lt_add_left (by decide : 1 < 81) _
  have hle : B ^ 4 + 81 ≤ (B + 3) ^ 4 := by
    rw [hexp]
    omega
  exact lt_of_lt_of_le h81 hle

theorem C_pow_thirteen_gt_B_pow_four_add_one {B : ℕ} (hB : 0 < B) :
    B ^ 4 + 1 < (B + 3) ^ 13 := by
  have hCpos : 0 < B + 3 := Nat.add_pos_right B (by decide : 0 < 3)
  have hpow : (B + 3) ^ 4 ≤ (B + 3) ^ 13 :=
    Nat.pow_le_pow_right hCpos (by decide : 4 ≤ 13)
  exact lt_of_lt_of_le (C_pow_four_gt_B_pow_four_add_one hB) hpow

/-- Gap-3 is not Catalan: `C¹³ − B⁴ ≠ 1` for `B > 0`. -/
theorem gap3_not_catalan_shape {B : ℕ} (hB : 0 < B) :
    (B + 3) ^ 13 - B ^ 4 ≠ 1 := by
  have hlt := C_pow_thirteen_gt_B_pow_four_add_one hB
  have hle : B ^ 4 ≤ (B + 3) ^ 13 :=
    le_of_lt (lt_trans (Nat.lt_succ_self (B ^ 4)) hlt)
  intro h
  have heq : (B + 3) ^ 13 = B ^ 4 + 1 := by
    have h' := (Nat.sub_eq_iff_eq_add hle).mp h
    simpa [add_comm] using h'
  exact (ne_of_lt hlt) heq.symm

theorem gap3_A_pow_four_ne_one {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    A ^ 4 ≠ 1 := by
  rw [A_pow_four_eq_sub hsol]
  exact gap3_not_catalan_shape hB

/-! ## Parity: `B` is even -/

theorem even_pow_four_dvd_sixteen {n : ℕ} (h : Even n) :
    16 ∣ n ^ 4 := by
  obtain ⟨k, rfl⟩ := h
  have hk : k + k = 2 * k := (two_mul k).symm
  rw [hk]
  have : (2 * k) ^ 4 = 16 * k ^ 4 := by ring
  rw [this]
  exact dvd_mul_right _ _

theorem odd_pow_four_mod_sixteen {n : ℕ} (h : Odd n) :
    n ^ 4 % 16 = 1 := by
  obtain ⟨k, rfl⟩ := h
  have hexp : (2 * k + 1) ^ 4 =
      16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2) + 8 * k * (k + 1) + 1 := by
    ring
  have heven : Even (k * (k + 1)) :=
    (Nat.even_or_odd k).elim
      (fun hk => hk.mul_right (k + 1))
      (fun hk => (hk.add_odd odd_one).mul_left k)
  obtain ⟨m, hm⟩ := heven
  have h8 : 8 * (k * (k + 1)) = 16 * m := by
    rw [hm]
    ring
  have hrw : (2 * k + 1) ^ 4 =
      16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2 + m) + 1 := by
    calc
      (2 * k + 1) ^ 4
        = 16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2) + 8 * k * (k + 1) + 1 := hexp
      _ = 16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2) + 8 * (k * (k + 1)) + 1 := by
          ring
      _ = 16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2) + 16 * m + 1 := by
          rw [h8]
      _ = 16 * (k ^ 4 + 2 * k ^ 3 + k ^ 2 + m) + 1 := by
          ring
  rw [hrw]
  have hmod : ∀ t : ℕ, (16 * t + 1) % 16 = 1 := fun t => by
    rw [Nat.add_mod, Nat.mul_mod_right]
  exact hmod _

theorem B_even_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    Even B := by
  have hA := A_odd_of_sol hsol
  by_contra hne
  have hBodd : Odd B := Nat.not_even_iff_odd.1 hne
  have h3 : Odd (3 : ℕ) := ⟨1, by decide⟩
  have hCeven : Even (B + 3) := hBodd.add_odd h3
  have h16C : 16 ∣ (B + 3) ^ 4 := even_pow_four_dvd_sixteen hCeven
  have h16R : 16 ∣ (B + 3) ^ 13 :=
    dvd_trans h16C (pow_dvd_pow (B + 3) (by decide : 4 ≤ 13))
  have hL : (A ^ 4 + B ^ 4) % 16 = 2 := by
    have hA4 : A ^ 4 % 16 = 1 := odd_pow_four_mod_sixteen hA
    have hB4 : B ^ 4 % 16 = 1 := odd_pow_four_mod_sixteen hBodd
    rw [Nat.add_mod, hA4, hB4]
  have hR : (B + 3) ^ 13 % 16 = 0 := Nat.mod_eq_zero_of_dvd h16R
  have : (A ^ 4 + B ^ 4) % 16 = (B + 3) ^ 13 % 16 := by
    rw [hsol]
  rw [hL, hR] at this
  exact (by decide : (2 : ℕ) ≠ 0) this

/-! ## `3 ∤ B` ⇒ `gcd(A,B) = 1` -/

theorem gcd_A_B_eq_one_of_not_three_dvd_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : ¬ 3 ∣ B) :
    Nat.gcd A B = 1 := by
  have hcop : Nat.Coprime A B := by
    by_contra h
    obtain ⟨p, hp, hpA, hpB⟩ := Nat.Prime.not_coprime_iff_dvd.mp h
    have hp3 : p = 3 := prime_dvd_A_B_eq_three hp hsol hpA hpB
    exact h3 (hp3 ▸ hpB)
  exact hcop

theorem gaussian_coprime_when_three_not_dvd_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : ¬ 3 ∣ B) :
    Nat.Coprime A B :=
  gcd_A_B_eq_one_of_not_three_dvd_B hsol h3

/-- A prime dividing `B` cannot divide `A` when `3 ∤ B`.
    A Zsigmondy prime in `B` therefore does not force
    `13 ∣ v_p(A)`. -/
theorem zsigmondy_prime_in_B_not_dvd_A {p A B : ℕ}
    (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : ¬ 3 ∣ B) (hpB : p ∣ B) :
    ¬ p ∣ A := by
  have hgcd : Nat.gcd A B = 1 :=
    gcd_A_B_eq_one_of_not_three_dvd_B hsol h3
  intro hpA
  have : p ∣ Nat.gcd A B := Nat.dvd_gcd hpA hpB
  rw [hgcd] at this
  exact hp.not_dvd_one this

theorem zsigmondy_does_not_force_thirteen_divides_vpA {p A B : ℕ}
    (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : ¬ 3 ∣ B) (hpB : p ∣ B) :
    padicValNat p A = 0 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hpA := zsigmondy_prime_in_B_not_dvd_A hp hsol h3 hpB
  rw [padicValNat.eq_zero_iff]
  exact Or.inr (Or.inr hpA)

/-! ## `mod 3` of fourth powers -/

theorem pow_four_mod_three (n : ℕ) :
    n ^ 4 % 3 = (n % 3) ^ 4 % 3 :=
  Nat.pow_mod n 4 3

theorem pow_four_mod_three_of_mod {n : ℕ} :
    n ^ 4 % 3 = 0 ∧ n % 3 = 0 ∨
      n ^ 4 % 3 = 1 ∧ n % 3 ≠ 0 := by
  have hlt : n % 3 < 3 := Nat.mod_lt n (by decide)
  interval_cases h : n % 3
  · refine Or.inl ⟨?_, rfl⟩
    rw [pow_four_mod_three, h]
    norm_num
  · refine Or.inr ⟨?_, by decide⟩
    rw [pow_four_mod_three, h]
    norm_num
  · refine Or.inr ⟨?_, by decide⟩
    rw [pow_four_mod_three, h]
    norm_num

theorem three_dvd_iff_pow_four {n : ℕ} :
    3 ∣ n ↔ 3 ∣ n ^ 4 := by
  constructor
  · intro h
    exact dvd_pow h (by decide)
  · intro h
    exact (Nat.prime_three.dvd_of_dvd_pow h)

/-! ## Valuation at primes in `B` (Zsigmondy would live here) -/

theorem padicValNat_freyDiscNat_at_B {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hp2 : p ≠ 2) (hpA : ¬ p ∣ A) (hpC : ¬ p ∣ (B + 3)) :
    padicValNat p (freyDiscNat A B) = 8 * padicValNat p B := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hvalA : padicValNat p A = 0 := by
    rw [padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr hpA)
  have hvalC : padicValNat p (B + 3) = 0 := by
    rw [padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr hpC)
  have hCne : B + 3 ≠ 0 := Nat.succ_ne_zero _
  have hvalS : padicValNat p (A ^ 4 + B ^ 4) = 0 := by
    rw [hsol, padicValNat.pow 13 hCne, hvalC]
  rw [padicValNat_freyDiscNat hp hA hB,
    padicValNat_sixteen_of_ne_two hp hp2, hvalA, hvalS]
  ring

/-- A prime `p ∤ 6` dividing `B` is not 13-lowered unless
    `13 ∣ v_p(B)`. Zsigmondy in `B` does not produce Fermat-style
    uniform level 32. -/
theorem frey_B_not_ribet_lowered {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : A ≠ 0) (hB : 0 < B)
    (hp6 : ¬ p ∣ 6) (hpB : p ∣ B)
    (hnot13 : ¬ 13 ∣ padicValNat p B) :
    ¬ 13 ∣ padicValNat p (freyDiscNat A B) := by
  have hBne : B ≠ 0 := Nat.pos_iff_ne_zero.mp hB
  have hpne : ¬ (p = 2 ∨ p = 3) := by
    intro h
    exact hp6 ((prime_dvd_six_iff hp).2 h)
  have hp2 : p ≠ 2 := fun h => hpne (Or.inl h)
  have hp3 : p ≠ 3 := fun h => hpne (Or.inr h)
  have hpA : ¬ p ∣ A := by
    intro hpA
    exact hp3 (prime_dvd_A_B_eq_three hp hsol hpA hpB)
  have hpC : ¬ p ∣ (B + 3) := by
    intro hpC
    have hp3' : p ∣ 3 := by
      have hsub : p ∣ (B + 3) - B :=
        Nat.dvd_sub (Nat.le_add_right B 3) hpC hpB
      simpa [Nat.add_sub_cancel_left] using hsub
    exact hp3 ((Nat.prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 hp3')
  have hval :=
    padicValNat_freyDiscNat_at_B hp hsol hA hBne hp2 hpA hpC
  rw [hval, thirteen_dvd_eight_mul]
  exact hnot13

/-! ## Gaussian gcd still only divides `2A²` and `2B²` -/

theorem gaussian_gcd_divides_two {d : GaussianInt} {A B : ℕ}
    (hα : d ∣ gaussianAlpha A B)
    (hstar : d ∣ star (gaussianAlpha A B)) :
    d ∣ (⟨2 * (A : ℤ) ^ 2, 0⟩ : GaussianInt) ∧
      d ∣ (⟨0, 2 * (B : ℤ) ^ 2⟩ : GaussianInt) :=
  gaussian_common_dvd hα hstar

/-! ## Even with UFD + Catalan + Zsigmondy, need `C1 < 2` -/

/-- Even assuming a Gaussian thirteenth-power factorization
    (which stays `def Prop`), the squared argument-form comparison
    is strictly below `B⁴ / C¹³` for every `C1 ≥ 2` on `B ≥ B0`. -/
theorem baker_bound_gap3_mihailescu_zsigmondy_nogo
    {C1 : ℝ} (hC1 : 2 ≤ C1)
    {B : ℕ} (hB0 : B0_nat ≤ B) :
    exp (-C1 * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 := by
  have hB0' : BealMatveevBeal.BealKrausZsig.B0_nat ≤ B := by
    simpa [B0_nat_eq_zsig] using hB0
  exact baker_bound_gap3_gaussian_nogo hC1 hB0'

theorem baker_bound_gap3_catalan_zsig_nogo
    {C1 : ℝ} (hC1 : 2 ≤ C1)
    {B : ℕ} (hB0 : B0_nat ≤ B) :
    exp (-C1 * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 :=
  baker_bound_gap3_mihailescu_zsigmondy_nogo hC1 hB0

theorem C1_floor_mihailescu_zsigmondy_nogo {B : ℕ} (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 :=
  baker_bound_gap3_mihailescu_zsigmondy_nogo
    (le_of_lt (by rw [C1_floor_eq]; norm_num : (2 : ℝ) < (C1_floor : ℝ)))
    hB0

theorem two_forty_two_mihailescu_zsigmondy_nogo {B : ℕ}
    (hB0 : B0_nat ≤ B) :
    exp (-(242 : ℝ) * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 :=
  baker_bound_gap3_mihailescu_zsigmondy_nogo (by norm_num : (2 : ℝ) ≤ 242) hB0

theorem two_mihailescu_zsigmondy_nogo {B : ℕ} (hB0 : B0_nat ≤ B) :
    exp (-(2 : ℝ) * log ((B + 3 : ℕ) : ℝ) * log (13 : ℝ)) ^ 2 <
      (B : ℝ) ^ 4 / ((B + 3 : ℕ) : ℝ) ^ 13 :=
  baker_bound_gap3_mihailescu_zsigmondy_nogo (le_refl (2 : ℝ)) hB0

theorem five_div_log_thirteen_lt_two_reexport :
    (5 : ℝ) / log (13 : ℝ) < 2 :=
  BealMatveevBeal.BealKrausZsig.five_div_log_thirteen_lt_two

/-! ## Locked uninhabited Props -/

def baker_bound_gap3 : Prop :=
  BealMatveevBeal.BealKrausZsig.baker_bound_gap3

def gaussian_associate_thirteenth_power : Prop :=
  BealMatveevBeal.BealKrausZsig.gaussian_associate_thirteenth_power

def zsigmondy_gaussian_primitive_divisor : Prop :=
  BealMatveevBeal.BealKrausZsig.zsigmondy_gaussian_primitive_divisor

def mihailescu_catalan : Prop :=
  BealMatveevBeal.BealKrausZsig.mihailescu_catalan

def darmon_merel_signature_44p : Prop :=
  BealMatveevBeal.BealKrausZsig.darmon_merel_signature_44p

def kraus_uniform_residual_level : Prop :=
  BealMatveevBeal.BealKrausZsig.kraus_uniform_residual_level

def ribet_level_lowering : Prop :=
  BealMatveevBeal.BealKrausZsig.ribet_level_lowering

#check C1_floor_eq
#check B0_nat_eq
#check gap3_not_catalan_shape
#check B_even_of_sol
#check gcd_A_B_eq_one_of_not_three_dvd_B
#check gaussian_coprime_when_three_not_dvd_B
#check zsigmondy_prime_in_B_not_dvd_A
#check zsigmondy_does_not_force_thirteen_divides_vpA
#check padicValNat_freyDiscNat_at_B
#check frey_B_not_ribet_lowered
#check gaussian_gcd_divides_two
#check baker_bound_gap3_mihailescu_zsigmondy_nogo
#check C1_floor_mihailescu_zsigmondy_nogo
#check baker_bound_gap3
#check gaussian_associate_thirteenth_power
#check zsigmondy_gaussian_primitive_divisor
#check mihailescu_catalan
#print axioms gap3_not_catalan_shape
#print axioms B_even_of_sol
#print axioms gcd_A_B_eq_one_of_not_three_dvd_B
#print axioms baker_bound_gap3_mihailescu_zsigmondy_nogo
#print axioms frey_B_not_ribet_lowered
#print axioms zsigmondy_does_not_force_thirteen_divides_vpA

end BealMatveevBeal.BealCatalanZsig
