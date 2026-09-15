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
import BealGap9

/-!
# Gap-10 `A⁴ + B⁴ = (B+10)¹³` (not a `B ≤ 10⁶` close)

Successor of `8b5543e` (`v24-v24x-final-gap9-nogo`).
`C = B+10` so `gcd(B,C) ∣ 10`. Parity is gap-2/4/6/8, not gap-1/5/7/9:
`A` is even (odd `A` makes the left side `1` or `2` mod 16 while
even `C` is `0` and odd `C` is odd, never `2`). Even `B` dies
after three divisions by `2`, leaving
`A₃⁴ + B₃⁴ = 2 (4 B₃ + 5)¹³`. The both-odd last step is killed
in `ℤ[i]`: `S + Di` is associated to a 13th power. Units permute
so one of `|Re|`, `|Im|` of `δ¹³` equals `64 B²`. That forces
`Re(⟨d,e⟩¹³) = ±(d²+e²-10)²` with `d,e` odd and coprime. The
cones `e ≥ 5d` and `d ≥ 10e` are polynomial identities
(`re13_gt_of_five_mul`, `re13_gt_of_ten_mul`); `|d|=1` is
`re13_one_ne_pm_rhs`. So `B` is odd and `A` is even.
`(1,0)` is **not** a solution (`1 ≠ 10¹³`). `3 ∣ B` is compatible
(`C ≡ 1 mod 3`, `A⁴ ≡ 1`). `5 ∣ B` kills by 5-descent
(`C₁ = B₁+2`, last step `125 X = (125 B₄ + 2)¹³ ≡ 2` mod 5).
`7 ∣ B` kills residue (`C ≡ 3 mod 7`, `C¹³ ≡ 3` not in `{0,1,2,4}`).
Remaining solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 10`, but `B`
is odd and `5 ∤ B`) and pure Darmon–Merel signature `(4,4,13)`.

`hGen_gap10` / `hLLL_gap10` stay `def Prop`. Every `C1 ≥ 1` loses
to `B⁴/A⁴` on `B ≥ B0`; no scaling yields a Baker–Davenport
witness above `17 + C/B0`. Named theorem `baker_bound_gap10`
stays a `def Prop`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

set_option maxHeartbeats 800000

open Real

namespace BealMatveevBeal.BealGap10

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_logs :
    C1_floor = BealMatveevBeal.MatveevThreeLogs.C1_floor := rfl

theorem B0_nat_eq_logs :
    B0_nat = BealMatveevBeal.MatveevThreeLogs.B0_nat := rfl

/-! ## Gap-10 equation -/

def is_gap10_sol (A B : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = (B + 10) ^ 13

/-- Kernel Baker bound for gap-10. Stays a `def Prop`. -/
def baker_bound_gap10 : Prop :=
  ∀ A B : ℕ, is_gap10_sol A B → B ≤ B0_nat

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealTrueV25.darmon_merel_44_13_no_coprime

/-! ## `(1,0)` is not a solution -/

theorem not_gap10_one_zero : ¬ is_gap10_sol 1 0 := by
  unfold is_gap10_sol
  decide

theorem even_ten : Even (10 : ℕ) := ⟨5, rfl⟩

/-! ## `gcd(B, B+10) = gcd(B, 10)` divides `10` -/

theorem gcd_B_C_eq_gcd_ten (B : ℕ) : Nat.gcd B (B + 10) = Nat.gcd B 10 := by
  rw [Nat.gcd_comm B (B + 10), Nat.add_comm B 10]
  exact (Nat.gcd_add_self_left (10 : ℕ) B).trans (Nat.gcd_comm 10 B)

theorem gcd_B_C_dvd_ten (B : ℕ) : Nat.gcd B (B + 10) ∣ 10 := by
  rw [gcd_B_C_eq_gcd_ten]
  exact Nat.gcd_dvd_right B 10

theorem gcd_B_C_dvd_ten_gap10 (B : ℕ) : Nat.gcd B (B + 10) ∣ 10 :=
  gcd_B_C_dvd_ten B

/-! ## Parity: `A` is even. -/

theorem A_even_of_sol_gap10 {A B : ℕ} (h : is_gap10_sol A B) : Even A := by
  by_contra hne
  have hAodd : Odd A := Nat.not_even_iff_odd.1 hne
  have hA4 : A ^ 4 % 16 = 1 :=
    BealCatalanZsig.odd_pow_four_mod_sixteen hAodd
  by_cases hBeven : Even B
  · have hCeven : Even (B + 10) := hBeven.add even_ten
    have h16C : 16 ∣ (B + 10) ^ 4 :=
      BealCatalanZsig.even_pow_four_dvd_sixteen hCeven
    have h16R : 16 ∣ (B + 10) ^ 13 :=
      dvd_trans h16C (pow_dvd_pow (B + 10) (by decide : 4 ≤ 13))
    have hR : (B + 10) ^ 13 % 16 = 0 := Nat.mod_eq_zero_of_dvd h16R
    have hB4 : B ^ 4 % 16 = 0 :=
      Nat.mod_eq_zero_of_dvd (BealCatalanZsig.even_pow_four_dvd_sixteen hBeven)
    have hL : (A ^ 4 + B ^ 4) % 16 = 1 := by
      rw [Nat.add_mod, hA4, hB4]
    have : (A ^ 4 + B ^ 4) % 16 = (B + 10) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    exact (by decide : (1 : ℕ) ≠ 0) this
  · have hBodd : Odd B := Nat.not_even_iff_odd.1 hBeven
    have hCodd : Odd (B + 10) := hBodd.add_even even_ten
    have hB4 : B ^ 4 % 16 = 1 :=
      BealCatalanZsig.odd_pow_four_mod_sixteen hBodd
    have hL : (A ^ 4 + B ^ 4) % 16 = 2 := by
      rw [Nat.add_mod, hA4, hB4]
    have hR : (B + 10) ^ 13 % 16 = (B + 10) % 16 :=
      BealGap2.odd_pow_thirteen_mod_sixteen hCodd
    have : (A ^ 4 + B ^ 4) % 16 = (B + 10) ^ 13 % 16 := by rw [h]
    rw [hL, hR] at this
    have hC2 : (B + 10) % 2 = 0 := by
      have h16 : (B + 10) % 16 = 2 := this.symm
      have : ((B + 10) % 16) % 2 = 0 := by rw [h16]
      rwa [Nat.mod_mod_of_dvd (B + 10) (by decide : 2 ∣ 16)] at this
    exact Nat.not_even_iff_odd.2 hCodd (Nat.even_iff.2 hC2)

/-! ## Gaussian powers for the last-step identity -/ 

theorem gaussian_pow2 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 2 = ⟨d * d - e * e, 2 * d * e⟩ := by
  ext <;> simp [pow_two, Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow3 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 3 =
      ⟨d ^ 3 - 3 * d * e ^ 2, 3 * d ^ 2 * e - e ^ 3⟩ := by
  have hprev := gaussian_pow2 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 3 =
      (⟨d, e⟩ : GaussianInt) ^ 2 * ⟨d, e⟩ := pow_succ _ 2
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow4 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 4 =
      ⟨d ^ 4 - 6 * d ^ 2 * e ^ 2 + e ^ 4, 4 * d ^ 3 * e - 4 * d * e ^ 3⟩ := by
  have hprev := gaussian_pow3 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 4 =
      (⟨d, e⟩ : GaussianInt) ^ 3 * ⟨d, e⟩ := pow_succ _ 3
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow5 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 5 =
      ⟨d ^ 5 - 10 * d ^ 3 * e ^ 2 + 5 * d * e ^ 4, 5 * d ^ 4 * e - 10 * d ^ 2 * e ^ 3 + e ^ 5⟩ := by
  have hprev := gaussian_pow4 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 5 =
      (⟨d, e⟩ : GaussianInt) ^ 4 * ⟨d, e⟩ := pow_succ _ 4
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow6 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 6 =
      ⟨d ^ 6 - 15 * d ^ 4 * e ^ 2 + 15 * d ^ 2 * e ^ 4 - e ^ 6, 6 * d ^ 5 * e - 20 * d ^ 3 * e ^ 3 + 6 * d * e ^ 5⟩ := by
  have hprev := gaussian_pow5 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 6 =
      (⟨d, e⟩ : GaussianInt) ^ 5 * ⟨d, e⟩ := pow_succ _ 5
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow7 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 7 =
      ⟨d ^ 7 - 21 * d ^ 5 * e ^ 2 + 35 * d ^ 3 * e ^ 4 - 7 * d * e ^ 6, 7 * d ^ 6 * e - 35 * d ^ 4 * e ^ 3 + 21 * d ^ 2 * e ^ 5 - e ^ 7⟩ := by
  have hprev := gaussian_pow6 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 7 =
      (⟨d, e⟩ : GaussianInt) ^ 6 * ⟨d, e⟩ := pow_succ _ 6
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow8 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 8 =
      ⟨d ^ 8 - 28 * d ^ 6 * e ^ 2 + 70 * d ^ 4 * e ^ 4 - 28 * d ^ 2 * e ^ 6 + e ^ 8, 8 * d ^ 7 * e - 56 * d ^ 5 * e ^ 3 + 56 * d ^ 3 * e ^ 5 - 8 * d * e ^ 7⟩ := by
  have hprev := gaussian_pow7 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 8 =
      (⟨d, e⟩ : GaussianInt) ^ 7 * ⟨d, e⟩ := pow_succ _ 7
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow9 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 9 =
      ⟨d ^ 9 - 36 * d ^ 7 * e ^ 2 + 126 * d ^ 5 * e ^ 4 - 84 * d ^ 3 * e ^ 6 + 9 * d * e ^ 8, 9 * d ^ 8 * e - 84 * d ^ 6 * e ^ 3 + 126 * d ^ 4 * e ^ 5 - 36 * d ^ 2 * e ^ 7 + e ^ 9⟩ := by
  have hprev := gaussian_pow8 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 9 =
      (⟨d, e⟩ : GaussianInt) ^ 8 * ⟨d, e⟩ := pow_succ _ 8
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow10 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 10 =
      ⟨d ^ 10 - 45 * d ^ 8 * e ^ 2 + 210 * d ^ 6 * e ^ 4 - 210 * d ^ 4 * e ^ 6 + 45 * d ^ 2 * e ^ 8 - e ^ 10, 10 * d ^ 9 * e - 120 * d ^ 7 * e ^ 3 + 252 * d ^ 5 * e ^ 5 - 120 * d ^ 3 * e ^ 7 + 10 * d * e ^ 9⟩ := by
  have hprev := gaussian_pow9 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 10 =
      (⟨d, e⟩ : GaussianInt) ^ 9 * ⟨d, e⟩ := pow_succ _ 9
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow11 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 11 =
      ⟨d ^ 11 - 55 * d ^ 9 * e ^ 2 + 330 * d ^ 7 * e ^ 4 - 462 * d ^ 5 * e ^ 6 + 165 * d ^ 3 * e ^ 8 - 11 * d * e ^ 10, 11 * d ^ 10 * e - 165 * d ^ 8 * e ^ 3 + 462 * d ^ 6 * e ^ 5 - 330 * d ^ 4 * e ^ 7 + 55 * d ^ 2 * e ^ 9 - e ^ 11⟩ := by
  have hprev := gaussian_pow10 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 11 =
      (⟨d, e⟩ : GaussianInt) ^ 10 * ⟨d, e⟩ := pow_succ _ 10
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow12 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 12 =
      ⟨d ^ 12 - 66 * d ^ 10 * e ^ 2 + 495 * d ^ 8 * e ^ 4 - 924 * d ^ 6 * e ^ 6 + 495 * d ^ 4 * e ^ 8 - 66 * d ^ 2 * e ^ 10 + e ^ 12, 12 * d ^ 11 * e - 220 * d ^ 9 * e ^ 3 + 792 * d ^ 7 * e ^ 5 - 792 * d ^ 5 * e ^ 7 + 220 * d ^ 3 * e ^ 9 - 12 * d * e ^ 11⟩ := by
  have hprev := gaussian_pow11 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 12 =
      (⟨d, e⟩ : GaussianInt) ^ 11 * ⟨d, e⟩ := pow_succ _ 11
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring
theorem gaussian_pow13 (d e : ℤ) :
    (⟨d, e⟩ : GaussianInt) ^ 13 =
      ⟨d ^ 13 - 78 * d ^ 11 * e ^ 2 + 715 * d ^ 9 * e ^ 4 - 1716 * d ^ 7 * e ^ 6 + 1287 * d ^ 5 * e ^ 8 - 286 * d ^ 3 * e ^ 10 + 13 * d * e ^ 12, 13 * d ^ 12 * e - 286 * d ^ 10 * e ^ 3 + 1287 * d ^ 8 * e ^ 5 - 1716 * d ^ 6 * e ^ 7 + 715 * d ^ 4 * e ^ 9 - 78 * d ^ 2 * e ^ 11 + e ^ 13⟩ := by
  have hprev := gaussian_pow12 d e
  have hsucc : (⟨d, e⟩ : GaussianInt) ^ 13 =
      (⟨d, e⟩ : GaussianInt) ^ 12 * ⟨d, e⟩ := pow_succ _ 12
  rw [hsucc, hprev]
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring

/-! ## Units of `ℤ[i]` and `(1+i)¹² = −64` -/

theorem one_add_I_pow_twelve :
    (⟨(1 : ℤ), 1⟩ : GaussianInt) ^ 12 = ⟨-64, 0⟩ := by
  native_decide

theorem gaussian_units {u : GaussianInt} (hu : IsUnit u) :
    u = 1 ∨ u = -1 ∨ u = ⟨0, 1⟩ ∨ u = ⟨0, -1⟩ := by
  have hn : u.norm.natAbs = 1 := Zsqrtd.norm_eq_one_iff.2 hu
  have hsum := GaussianInt.natAbs_norm_eq u
  rw [hn] at hsum
  have hlea : u.re.natAbs ≤ 1 := by
    have := Nat.le_add_right (u.re.natAbs * u.re.natAbs)
      (u.im.natAbs * u.im.natAbs)
    have : u.re.natAbs * u.re.natAbs ≤ 1 := by
      simpa [← hsum] using this
    nlinarith
  have hleb : u.im.natAbs ≤ 1 := by
    have := Nat.le_add_left (u.im.natAbs * u.im.natAbs)
      (u.re.natAbs * u.re.natAbs)
    have : u.im.natAbs * u.im.natAbs ≤ 1 := by
      simpa [← hsum] using this
    nlinarith
  have hre : u.re.natAbs = 1 ∧ u.im.natAbs = 0 ∨
      u.re.natAbs = 0 ∧ u.im.natAbs = 1 := by
    interval_cases u.re.natAbs <;> interval_cases u.im.natAbs <;>
      simp at hsum ⊢
  rcases hre with ⟨hra, hia⟩ | ⟨hra, hia⟩
  · have him0 : u.im = 0 := Int.natAbs_eq_zero.mp hia
    have hreu : u.re = 1 ∨ u.re = -1 := Int.natAbs_eq_iff.mp hra
    rcases hreu with h1 | h1
    · left; ext <;> simp [h1, him0]
    · right; left; ext <;> simp [h1, him0]
  · have hre0 : u.re = 0 := Int.natAbs_eq_zero.mp hra
    have himu : u.im = 1 ∨ u.im = -1 := Int.natAbs_eq_iff.mp hia
    rcases himu with h1 | h1
    · right; right; left; ext <;> simp [h1, hre0]
    · right; right; right; ext <;> simp [h1, hre0]

theorem one_add_I_mul (S D : ℤ) :
    (⟨(1 : ℤ), 1⟩ : GaussianInt) * ⟨S, D⟩ = ⟨S - D, S + D⟩ := by
  ext <;> simp [Zsqrtd.mul_re, Zsqrtd.mul_im] <;> ring

theorem int_sq_natAbs (n : ℤ) : (n.natAbs : ℤ) ^ 2 = n ^ 2 := by
  rw [pow_two, pow_two, Int.natAbs_mul_self]

lemma re13_one_gt_rhs (e : ℕ) (he : 5 ≤ e) :
    (13 : ℤ) * (e : ℤ) ^ 12 - 286 * (e : ℤ) ^ 10 + 1287 * (e : ℤ) ^ 8
      - 1716 * (e : ℤ) ^ 6 + 715 * (e : ℤ) ^ 4 - 78 * (e : ℤ) ^ 2 + 1
    > ((e : ℤ) ^ 2 - 9) ^ 2 := by
  have h5 : 5 ≤ (e : ℤ) := by exact_mod_cast he
  have h0 : 0 ≤ (e : ℤ) := by exact_mod_cast (Nat.zero_le e)
  have hdom : (13 : ℤ) * e ^ 12 - 286 * e ^ 10 ≥ 39 * e ^ 10 := by
    have : (13 : ℤ) * e ^ 12 - 286 * e ^ 10 =
        e ^ 10 * (13 * e ^ 2 - 286) := by ring
    rw [this]
    nlinarith [pow_nonneg h0 10]
  have hrhs : ((e : ℤ) ^ 2 - 9) ^ 2 ≤ e ^ 4 := by
    nlinarith [sq_nonneg ((e : ℤ) ^ 2 - 9), sq_nonneg (e : ℤ), h5]
  have hrest : (39 : ℤ) * e ^ 10 ≥ 1716 * e ^ 6 + 78 * e ^ 2 + e ^ 4 + 1 := by
    have hex : (e : ℤ) ^ 10 = e ^ 6 * e ^ 4 := by ring
    have h4 : (5 : ℤ) ^ 4 ≤ e ^ 4 :=
      pow_le_pow_left (by norm_num : (0 : ℤ) ≤ 5) h5 4
    nlinarith [hex, h4, pow_nonneg h0 6, pow_nonneg h0 2, pow_nonneg h0 4, h5]
  nlinarith [hdom, hrest, hrhs, pow_nonneg h0 8, pow_nonneg h0 4]

theorem gaussian_pow13_re (d e : ℤ) :
    ((⟨d, e⟩ : GaussianInt) ^ 13).re =
      d ^ 13 - 78 * d ^ 11 * e ^ 2 + 715 * d ^ 9 * e ^ 4
        - 1716 * d ^ 7 * e ^ 6 + 1287 * d ^ 5 * e ^ 8
        - 286 * d ^ 3 * e ^ 10 + 13 * d * e ^ 12 := by
  simpa using congrArg Zsqrtd.re (gaussian_pow13 d e)

theorem gaussian_pow13_im (d e : ℤ) :
    ((⟨d, e⟩ : GaussianInt) ^ 13).im =
      13 * d ^ 12 * e - 286 * d ^ 10 * e ^ 3 + 1287 * d ^ 8 * e ^ 5
        - 1716 * d ^ 6 * e ^ 7 + 715 * d ^ 4 * e ^ 9
        - 78 * d ^ 2 * e ^ 11 + e ^ 13 := by
  simpa using congrArg Zsqrtd.im (gaussian_pow13 d e)

theorem re13_one_eq_poly_natAbs (e : ℤ) :
    ((⟨(1 : ℤ), e⟩ : GaussianInt) ^ 13).re =
      (13 : ℤ) * (e.natAbs : ℤ) ^ 12 - 286 * (e.natAbs : ℤ) ^ 10
        + 1287 * (e.natAbs : ℤ) ^ 8 - 1716 * (e.natAbs : ℤ) ^ 6
        + 715 * (e.natAbs : ℤ) ^ 4 - 78 * (e.natAbs : ℤ) ^ 2 + 1 := by
  rw [gaussian_pow13_re]
  have h2 : e ^ 2 = (e.natAbs : ℤ) ^ 2 := (int_sq_natAbs e).symm
  have h4 : e ^ 4 = (e.natAbs : ℤ) ^ 4 := by
    have : e ^ 4 = (e ^ 2) ^ 2 := by ring
    rw [this, h2]; ring
  have h6 : e ^ 6 = (e.natAbs : ℤ) ^ 6 := by
    have : e ^ 6 = (e ^ 2) ^ 3 := by ring
    rw [this, h2]; ring
  have h8 : e ^ 8 = (e.natAbs : ℤ) ^ 8 := by
    have : e ^ 8 = (e ^ 2) ^ 4 := by ring
    rw [this, h2]; ring
  have h10 : e ^ 10 = (e.natAbs : ℤ) ^ 10 := by
    have : e ^ 10 = (e ^ 2) ^ 5 := by ring
    rw [this, h2]; ring
  have h12 : e ^ 12 = (e.natAbs : ℤ) ^ 12 := by
    have : e ^ 12 = (e ^ 2) ^ 6 := by ring
    rw [this, h2]; ring
  simp [h2, h4, h6, h8, h10, h12]
  ring

theorem rhs_eq_poly_natAbs (e : ℤ) :
    (1 + e ^ 2 - 10) ^ 2 = ((e.natAbs : ℤ) ^ 2 - 9) ^ 2 := by
  have h2 : e ^ 2 = (e.natAbs : ℤ) ^ 2 := (int_sq_natAbs e).symm
  rw [h2]; ring

theorem re13_one_ne_pm_rhs {e : ℤ} (hne : e.natAbs ≠ 1) :
    ((⟨(1 : ℤ), e⟩ : GaussianInt) ^ 13).re ≠ (1 + e ^ 2 - 10) ^ 2 ∧
    ((⟨(1 : ℤ), e⟩ : GaussianInt) ^ 13).re ≠ -((1 + e ^ 2 - 10) ^ 2) := by
  rw [re13_one_eq_poly_natAbs, rhs_eq_poly_natAbs]
  set n := e.natAbs
  have hcases : n = 0 ∨ n = 2 ∨ n = 3 ∨ n = 4 ∨ 5 ≤ n := by omega
  rcases hcases with h0 | h2 | h3 | h4 | h5
  · subst h0; native_decide
  · subst h2; native_decide
  · subst h3; native_decide
  · subst h4; native_decide
  · have hgt := re13_one_gt_rhs n h5
    have hrhs0 : 0 ≤ ((n : ℤ) ^ 2 - 9) ^ 2 := sq_nonneg _
    constructor
    · exact ne_of_gt hgt
    · intro hneg
      have hle : (13 : ℤ) * (n : ℤ) ^ 12 - 286 * (n : ℤ) ^ 10 + 1287 * (n : ℤ) ^ 8
          - 1716 * (n : ℤ) ^ 6 + 715 * (n : ℤ) ^ 4 - 78 * (n : ℤ) ^ 2 + 1
        ≤ 0 := by
        have : -((n : ℤ) ^ 2 - 9) ^ 2 ≤ 0 := neg_nonpos.2 hrhs0
        linarith
      linarith [hgt, hrhs0]

/-- Expanded `P(d,5d+k) - ((d)²+(5d+k)²-10)²` is strictly positive. -/
theorem re13_gt_of_five_mul_k (d k : ℕ) (hd : 1 ≤ d) :
    (13 : ℤ) * d * (5 * d + k : ℤ) ^ 12
      - 286 * (d : ℤ) ^ 3 * (5 * d + k) ^ 10
      + 1287 * (d : ℤ) ^ 5 * (5 * d + k) ^ 8
      - 1716 * (d : ℤ) ^ 7 * (5 * d + k) ^ 6
      + 715 * (d : ℤ) ^ 9 * (5 * d + k) ^ 4
      - 78 * (d : ℤ) ^ 11 * (5 * d + k) ^ 2
      + (d : ℤ) ^ 13
    > ((d : ℤ) ^ 2 + (5 * d + k : ℤ) ^ 2 - 10) ^ 2 := by
  have h1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have h0d : (0 : ℤ) ≤ d := le_trans (by norm_num) h1
  have h0k : (0 : ℤ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hd4 : (1 : ℤ) ≤ d ^ 4 := one_le_pow_of_one_le h1 4
  have hd9 : (1 : ℤ) ≤ d ^ 9 := one_le_pow_of_one_le h1 9
  have hd12 : (1 : ℤ) ≤ d ^ 12 := one_le_pow_of_one_le h1 12
  have hd11 : (1 : ℤ) ≤ d ^ 11 := one_le_pow_of_one_le h1 11
  have hd10 : (1 : ℤ) ≤ d ^ 10 := one_le_pow_of_one_le h1 10
  have hd3 : (1 : ℤ) ≤ d ^ 3 := one_le_pow_of_one_le h1 3
  have hd2 : (1 : ℤ) ≤ d ^ 2 := one_le_pow_of_one_le h1 2
  have hexp :
      (13 : ℤ) * d * (5 * d + k) ^ 12
        - 286 * d ^ 3 * (5 * d + k) ^ 10
        + 1287 * d ^ 5 * (5 * d + k) ^ 8
        - 1716 * d ^ 7 * (5 * d + k) ^ 6
        + 715 * d ^ 9 * (5 * d + k) ^ 4
        - 78 * d ^ 11 * (5 * d + k) ^ 2
        + d ^ 13
        - ((d : ℤ) ^ 2 + (5 * d + k) ^ 2 - 10) ^ 2
      = (857226176 : ℤ) * d ^ 13
        + 2803806720 * d ^ 12 * k
        + 3898644672 * d ^ 11 * k ^ 2
        + 3125636800 * d ^ 10 * k ^ 3
        + 1630897840 * d ^ 9 * k ^ 4
        + 588107520 * d ^ 8 * k ^ 5
        + 151049184 * d ^ 7 * k ^ 6
        + 27936480 * d ^ 6 * k ^ 7
        + 3701412 * d ^ 5 * k ^ 8
        + 343200 * d ^ 4 * k ^ 9
        + 21164 * d ^ 3 * k ^ 10
        + 780 * d ^ 2 * k ^ 11
        + 13 * d * k ^ 12
        - 676 * d ^ 4
        - 520 * d ^ 3 * k
        - 152 * d ^ 2 * k ^ 2
        - 20 * d * k ^ 3
        - k ^ 4
        + 520 * d ^ 2
        + 200 * d * k
        + 20 * k ^ 2
        - 100 := by
    ring
  have hA : (0 : ℤ) < 857226176 * d ^ 13 - 676 * d ^ 4 - 100 := by
    have hfac : (857226176 : ℤ) * d ^ 13 - 676 * d ^ 4 =
        d ^ 4 * (857226176 * d ^ 9 - 676) := by ring
    have hinner : (777 : ℤ) ≤ 857226176 * d ^ 9 - 676 := by
      have : (1 : ℤ) * 857226176 ≤ 857226176 * d ^ 9 :=
        mul_le_mul_of_nonneg_left hd9 (by norm_num)
      linarith
    have hmul : (101 : ℤ) ≤ d ^ 4 * (857226176 * d ^ 9 - 676) := by
      have h101 : (101 : ℤ) ≤ 857226176 * d ^ 9 - 676 := le_trans (by norm_num) hinner
      have : (1 : ℤ) * 101 ≤ d ^ 4 * (857226176 * d ^ 9 - 676) :=
        mul_le_mul hd4 h101 (by linarith) (le_trans (by norm_num : (0 : ℤ) ≤ 1) hd4)
      simpa using this
    linarith [hfac, hmul]
  have hB : (0 : ℤ) ≤ 2803806720 * d ^ 12 * k - 520 * d ^ 3 * k := by
    have hcoeff : (520 : ℤ) * d ^ 3 ≤ 2803806720 * d ^ 12 := by
      have hpow : (d : ℤ) ^ 3 ≤ d ^ 12 :=
        pow_le_pow_right h1 (by decide : (3 : ℕ) ≤ 12)
      nlinarith [hpow, hd3, hd12]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_right hcoeff h0k)
  have hC : (0 : ℤ) ≤ 3898644672 * d ^ 11 * k ^ 2 - 152 * d ^ 2 * k ^ 2 := by
    have hcoeff : (152 : ℤ) * d ^ 2 ≤ 3898644672 * d ^ 11 := by
      have hpow : (d : ℤ) ^ 2 ≤ d ^ 11 :=
        pow_le_pow_right h1 (by decide : (2 : ℕ) ≤ 11)
      nlinarith [hpow, hd2, hd11]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg h0k 2))
  have hD : (0 : ℤ) ≤ 3125636800 * d ^ 10 * k ^ 3 - 20 * d * k ^ 3 := by
    have hcoeff : (20 : ℤ) * d ≤ 3125636800 * d ^ 10 := by
      have hpow : (d : ℤ) ^ 1 ≤ d ^ 10 :=
        pow_le_pow_right h1 (by decide : (1 : ℕ) ≤ 10)
      have hpow' : (d : ℤ) ≤ d ^ 10 := by simpa using hpow
      nlinarith [hpow', h1, hd10]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg h0k 3))
  have hE : (0 : ℤ) ≤ 1630897840 * d ^ 9 * k ^ 4 - k ^ 4 := by
    have hcoeff : (1 : ℤ) ≤ 1630897840 * d ^ 9 := by
      have : (1 : ℤ) ≤ 1630897840 := by norm_num
      nlinarith [hd9, this]
    have := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg h0k 4)
    have : (k : ℤ) ^ 4 ≤ 1630897840 * d ^ 9 * k ^ 4 := by
      simpa [one_mul] using this
    exact sub_nonneg.2 this
  have hF : (0 : ℤ) ≤ 588107520 * d ^ 8 * k ^ 5
        + 151049184 * d ^ 7 * k ^ 6
        + 27936480 * d ^ 6 * k ^ 7
        + 3701412 * d ^ 5 * k ^ 8
        + 343200 * d ^ 4 * k ^ 9
        + 21164 * d ^ 3 * k ^ 10
        + 780 * d ^ 2 * k ^ 11
        + 13 * d * k ^ 12
        + 520 * d ^ 2
        + 200 * d * k
        + 20 * k ^ 2 := by
    nlinarith [pow_nonneg h0d 8, pow_nonneg h0k 5, pow_nonneg h0d 7, pow_nonneg h0k 6,
      pow_nonneg h0d 6, pow_nonneg h0k 7, pow_nonneg h0d 5, pow_nonneg h0k 8,
      pow_nonneg h0d 4, pow_nonneg h0k 9, pow_nonneg h0d 3, pow_nonneg h0k 10,
      pow_nonneg h0d 2, pow_nonneg h0k 11, pow_nonneg h0k 12, h0d, h0k, hd2]
  have hgt : (0 : ℤ) <
      (13 : ℤ) * d * (5 * d + k) ^ 12
        - 286 * d ^ 3 * (5 * d + k) ^ 10
        + 1287 * d ^ 5 * (5 * d + k) ^ 8
        - 1716 * d ^ 7 * (5 * d + k) ^ 6
        + 715 * d ^ 9 * (5 * d + k) ^ 4
        - 78 * d ^ 11 * (5 * d + k) ^ 2
        + d ^ 13
        - ((d : ℤ) ^ 2 + (5 * d + k) ^ 2 - 10) ^ 2 := by
    rw [hexp]
    linarith [hA, hB, hC, hD, hE, hF]
  exact hgt

theorem re13_gt_of_five_mul (d e : ℕ) (hd : 1 ≤ d) (he : 5 * d ≤ e) :
    (13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set k := e - 5 * d
  have hk : e = 5 * d + k := (Nat.add_sub_of_le he).symm
  rw [hk]
  exact re13_gt_of_five_mul_k d k hd

/-- Expanded `P(10e+k, e) - ((10e+k)²+e²-10)²` is strictly positive. -/
theorem re13_gt_of_ten_mul_k (e k : ℕ) (he : 1 ≤ e) :
    (13 : ℤ) * (10 * e + k) * (e : ℤ) ^ 12
      - 286 * (10 * e + k : ℤ) ^ 3 * e ^ 10
      + 1287 * (10 * e + k : ℤ) ^ 5 * e ^ 8
      - 1716 * (10 * e + k : ℤ) ^ 7 * e ^ 6
      + 715 * (10 * e + k : ℤ) ^ 9 * e ^ 4
      - 78 * (10 * e + k : ℤ) ^ 11 * e ^ 2
      + (10 * e + k : ℤ) ^ 13
    > ((10 * e + k : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  have h1 : (1 : ℤ) ≤ e := by exact_mod_cast he
  have h0e : (0 : ℤ) ≤ e := le_trans (by norm_num) h1
  have h0k : (0 : ℤ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have he4 : (1 : ℤ) ≤ e ^ 4 := one_le_pow_of_one_le h1 4
  have he9 : (1 : ℤ) ≤ e ^ 9 := one_le_pow_of_one_le h1 9
  have he12 : (1 : ℤ) ≤ e ^ 12 := one_le_pow_of_one_le h1 12
  have he11 : (1 : ℤ) ≤ e ^ 11 := one_le_pow_of_one_le h1 11
  have he10 : (1 : ℤ) ≤ e ^ 10 := one_le_pow_of_one_le h1 10
  have he3 : (1 : ℤ) ≤ e ^ 3 := one_le_pow_of_one_le h1 3
  have he2 : (1 : ℤ) ≤ e ^ 2 := one_le_pow_of_one_le h1 2
  have hexp :
      (13 : ℤ) * (10 * e + k) * e ^ 12
        - 286 * (10 * e + k) ^ 3 * e ^ 10
        + 1287 * (10 * e + k) ^ 5 * e ^ 8
        - 1716 * (10 * e + k) ^ 7 * e ^ 6
        + 715 * (10 * e + k) ^ 9 * e ^ 4
        - 78 * (10 * e + k) ^ 11 * e ^ 2
        + (10 * e + k) ^ 13
        - ((10 * e + k : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2
      = (2897968414130 : ℤ) * e ^ 13
        + 5051552264213 * e ^ 12 * k
        + 3763809261420 * e ^ 11 * k ^ 2
        + 1632460686714 * e ^ 10 * k ^ 3
        + 466549004350 * e ^ 9 * k ^ 4
        + 93561297687 * e ^ 8 * k ^ 5
        + 13616339880 * e ^ 7 * k ^ 6
        + 1461172284 * e ^ 6 * k ^ 7
        + 115894350 * e ^ 5 * k ^ 8
        + 6721715 * e ^ 4 * k ^ 9
        + 277420 * e ^ 3 * k ^ 10
        + 7722 * e ^ 2 * k ^ 11
        + 130 * e * k ^ 12
        + k ^ 13
        - 10201 * e ^ 4
        - 4040 * e ^ 3 * k
        - 602 * e ^ 2 * k ^ 2
        - 40 * e * k ^ 3
        - k ^ 4
        + 2020 * e ^ 2
        + 400 * e * k
        + 20 * k ^ 2
        - 100 := by
    ring
  have hA : (0 : ℤ) < 2897968414130 * e ^ 13 - 10201 * e ^ 4 - 100 := by
    have hfac : (2897968414130 : ℤ) * e ^ 13 - 10201 * e ^ 4 =
        e ^ 4 * (2897968414130 * e ^ 9 - 10201) := by ring
    have hinner : (10301 : ℤ) ≤ 2897968414130 * e ^ 9 - 10201 := by
      have : (1 : ℤ) * 2897968414130 ≤ 2897968414130 * e ^ 9 :=
        mul_le_mul_of_nonneg_left he9 (by norm_num)
      linarith
    have hmul : (101 : ℤ) ≤ e ^ 4 * (2897968414130 * e ^ 9 - 10201) := by
      have h101 : (101 : ℤ) ≤ 2897968414130 * e ^ 9 - 10201 :=
        le_trans (by norm_num) hinner
      have : (1 : ℤ) * 101 ≤ e ^ 4 * (2897968414130 * e ^ 9 - 10201) :=
        mul_le_mul he4 h101 (by linarith) (le_trans (by norm_num : (0 : ℤ) ≤ 1) he4)
      simpa using this
    linarith [hfac, hmul]
  have hB : (0 : ℤ) ≤ 5051552264213 * e ^ 12 * k - 4040 * e ^ 3 * k := by
    have hcoeff : (4040 : ℤ) * e ^ 3 ≤ 5051552264213 * e ^ 12 := by
      have hpow : (e : ℤ) ^ 3 ≤ e ^ 12 :=
        pow_le_pow_right h1 (by decide : (3 : ℕ) ≤ 12)
      nlinarith [hpow, he3, he12]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_right hcoeff h0k)
  have hC : (0 : ℤ) ≤ 3763809261420 * e ^ 11 * k ^ 2 - 602 * e ^ 2 * k ^ 2 := by
    have hcoeff : (602 : ℤ) * e ^ 2 ≤ 3763809261420 * e ^ 11 := by
      have hpow : (e : ℤ) ^ 2 ≤ e ^ 11 :=
        pow_le_pow_right h1 (by decide : (2 : ℕ) ≤ 11)
      nlinarith [hpow, he2, he11]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg h0k 2))
  have hD : (0 : ℤ) ≤ 1632460686714 * e ^ 10 * k ^ 3 - 40 * e * k ^ 3 := by
    have hcoeff : (40 : ℤ) * e ≤ 1632460686714 * e ^ 10 := by
      have hpow : (e : ℤ) ^ 1 ≤ e ^ 10 :=
        pow_le_pow_right h1 (by decide : (1 : ℕ) ≤ 10)
      have hpow' : (e : ℤ) ≤ e ^ 10 := by simpa using hpow
      nlinarith [hpow', h1, he10]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg h0k 3))
  have hE : (0 : ℤ) ≤ 466549004350 * e ^ 9 * k ^ 4 - k ^ 4 := by
    have hcoeff : (1 : ℤ) ≤ 466549004350 * e ^ 9 := by
      have : (1 : ℤ) ≤ 466549004350 := by norm_num
      nlinarith [he9, this]
    have := mul_le_mul_of_nonneg_right hcoeff (pow_nonneg h0k 4)
    have : (k : ℤ) ^ 4 ≤ 466549004350 * e ^ 9 * k ^ 4 := by
      simpa [one_mul] using this
    exact sub_nonneg.2 this
  have hF : (0 : ℤ) ≤ 93561297687 * e ^ 8 * k ^ 5
        + 13616339880 * e ^ 7 * k ^ 6
        + 1461172284 * e ^ 6 * k ^ 7
        + 115894350 * e ^ 5 * k ^ 8
        + 6721715 * e ^ 4 * k ^ 9
        + 277420 * e ^ 3 * k ^ 10
        + 7722 * e ^ 2 * k ^ 11
        + 130 * e * k ^ 12
        + k ^ 13
        + 2020 * e ^ 2
        + 400 * e * k
        + 20 * k ^ 2 := by
    nlinarith [pow_nonneg h0e 8, pow_nonneg h0k 5, pow_nonneg h0e 7, pow_nonneg h0k 6,
      pow_nonneg h0e 6, pow_nonneg h0k 7, pow_nonneg h0e 5, pow_nonneg h0k 8,
      pow_nonneg h0e 4, pow_nonneg h0k 9, pow_nonneg h0e 3, pow_nonneg h0k 10,
      pow_nonneg h0e 2, pow_nonneg h0k 11, pow_nonneg h0k 12, pow_nonneg h0k 13,
      h0e, h0k, he2]
  have hgt : (0 : ℤ) <
      (13 : ℤ) * (10 * e + k) * e ^ 12
        - 286 * (10 * e + k) ^ 3 * e ^ 10
        + 1287 * (10 * e + k) ^ 5 * e ^ 8
        - 1716 * (10 * e + k) ^ 7 * e ^ 6
        + 715 * (10 * e + k) ^ 9 * e ^ 4
        - 78 * (10 * e + k) ^ 11 * e ^ 2
        + (10 * e + k) ^ 13
        - ((10 * e + k : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
    rw [hexp]
    linarith [hA, hB, hC, hD, hE, hF]
  exact hgt

theorem re13_gt_of_ten_mul (d e : ℕ) (he : 1 ≤ e) (hd : 10 * e ≤ d) :
    (13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set k := d - 10 * e
  have hk : d = 10 * e + k := (Nat.add_sub_of_le hd).symm
  rw [hk]
  exact re13_gt_of_ten_mul_k e k he

/-! ## Last-step 5-descent for `A⁴ + B⁴ = 2 (4B+5)¹³` -/

theorem fourth_pow_mod5 (a : ℕ) : a ^ 4 % 5 = 0 ∨ a ^ 4 % 5 = 1 :=
  BealMatveevBeal.BealGap1.fourth_pow_mod5 a

theorem pow13_mod5 (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  BealMatveevBeal.BealGap1.pow13_mod5_eq_self c

theorem five_dvd_of_fourth_pow_mod_zero {n : ℕ}
    (h : n ^ 4 % 5 = 0) : 5 ∣ n :=
  Nat.Prime.dvd_of_dvd_pow Nat.prime_five (Nat.dvd_of_mod_eq_zero h)

theorem both_five_dvd_of_sum_fourth_mod5_zero {X Y : ℕ}
    (h : (X ^ 4 + Y ^ 4) % 5 = 0) : 5 ∣ X ∧ 5 ∣ Y :=
  BealMatveevBeal.BealGap5.both_five_dvd_of_sum_fourth_mod5_zero h

theorem sum_fourth_of_mul_five (x y : ℕ) :
    (5 * x) ^ 4 + (5 * y) ^ 4 = 625 * (x ^ 4 + y ^ 4) :=
  BealMatveevBeal.BealGap5.sum_fourth_of_mul_five x y

theorem five_dvd_last_forces_five_dvd_A {A B : ℕ}
    (h : A ^ 4 + B ^ 4 = 2 * (4 * B + 5) ^ 13) (h5 : 5 ∣ B) : 5 ∣ A := by
  have hB4 : B ^ 4 % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h5 (by decide))
  have hC : (4 * B + 5) % 5 = 0 := by
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [Nat.add_mod, Nat.mul_mod, this]
  have hC13 : (4 * B + 5) ^ 13 % 5 = 0 := by
    rw [pow13_mod5, hC]
  have hR : (2 * (4 * B + 5) ^ 13) % 5 = 0 := by
    rw [Nat.mul_mod, hC13]
  have hsum : (A ^ 4 + B ^ 4) % 5 = (2 * (4 * B + 5) ^ 13) % 5 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hR] at hsum
  exact five_dvd_of_fourth_pow_mod_zero hsum

theorem no_sol_when_five_dvd_last {A B : ℕ}
    (h : A ^ 4 + B ^ 4 = 2 * (4 * B + 5) ^ 13) (h5 : 5 ∣ B) : False := by
  have hA5 := five_dvd_last_forces_five_dvd_A h h5
  obtain ⟨A1, hA⟩ := hA5
  obtain ⟨B1, hB⟩ := h5
  have hC : 4 * B + 5 = 5 * (4 * B1 + 1) := by
    rw [hB]; ring
  have hsol1 : (5 * A1) ^ 4 + (5 * B1) ^ 4 =
      2 * (5 * (4 * B1 + 1)) ^ 13 := by
    rw [← hA, ← hC]; exact h
  have heq1 : 625 * (A1 ^ 4 + B1 ^ 4) =
      2 * 5 ^ 13 * (4 * B1 + 1) ^ 13 := by
    have hr : (5 * (4 * B1 + 1)) ^ 13 = 5 ^ 13 * (4 * B1 + 1) ^ 13 :=
      mul_pow _ _ 13
    rw [← sum_fourth_of_mul_five, hsol1, hr, mul_assoc]
  have h9 : A1 ^ 4 + B1 ^ 4 = 2 * 5 ^ 9 * (4 * B1 + 1) ^ 13 := by
    have hpow : (5 : ℕ) ^ 13 = 625 * 5 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 625)
    rw [heq1, hpow]
    ring
  have hmod1 : (A1 ^ 4 + B1 ^ 4) % 5 = 0 := by
    have : 5 ∣ 2 * 5 ^ 9 * (4 * B1 + 1) ^ 13 := by
      refine dvd_mul_of_dvd_left ?_ _
      exact dvd_mul_of_dvd_right (dvd_pow_self 5 (by decide : 9 ≠ 0)) 2
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1, hB1d⟩ := both_five_dvd_of_sum_fourth_mod5_zero hmod1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1d
  have heq2src : (5 * A2) ^ 4 + (5 * B2) ^ 4 =
      2 * 5 ^ 9 * (20 * B2 + 1) ^ 13 := by
    have hC2 : 4 * B1 + 1 = 20 * B2 + 1 := by
      rw [hB2]; ring
    rw [← hA2, ← hB2, ← hC2]; exact h9
  have heq2 : 625 * (A2 ^ 4 + B2 ^ 4) =
      2 * 5 ^ 9 * (20 * B2 + 1) ^ 13 := by
    rw [← sum_fourth_of_mul_five]; exact heq2src
  have h5eq : A2 ^ 4 + B2 ^ 4 = 2 * 5 ^ 5 * (20 * B2 + 1) ^ 13 := by
    have hpow : (5 : ℕ) ^ 9 = 625 * 5 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 625)
    rw [heq2, hpow]
    ring
  have hmod2 : (A2 ^ 4 + B2 ^ 4) % 5 = 0 := by
    have : 5 ∣ 2 * 5 ^ 5 * (20 * B2 + 1) ^ 13 := by
      refine dvd_mul_of_dvd_left ?_ _
      exact dvd_mul_of_dvd_right (dvd_pow_self 5 (by decide : 5 ≠ 0)) 2
    exact Nat.mod_eq_zero_of_dvd (h5eq ▸ this)
  obtain ⟨hA2e, hB2e⟩ := both_five_dvd_of_sum_fourth_mod5_zero hmod2
  obtain ⟨A3, hA3⟩ := hA2e
  obtain ⟨B3, hB3⟩ := hB2e
  have heq3src : (5 * A3) ^ 4 + (5 * B3) ^ 4 =
      2 * 5 ^ 5 * (100 * B3 + 1) ^ 13 := by
    have hB21 : 20 * B2 + 1 = 100 * B3 + 1 := by
      rw [hB3]; ring
    rw [← hA3, ← hB3, ← hB21]; exact h5eq
  have heq3 : 625 * (A3 ^ 4 + B3 ^ 4) =
      2 * 5 ^ 5 * (100 * B3 + 1) ^ 13 := by
    rw [← sum_fourth_of_mul_five]; exact heq3src
  have h1eq : A3 ^ 4 + B3 ^ 4 = 2 * 5 * (100 * B3 + 1) ^ 13 := by
    have hpow : (5 : ℕ) ^ 5 = 625 * 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 625)
    rw [heq3, hpow]
    ring
  have hmod3 : (A3 ^ 4 + B3 ^ 4) % 5 = 0 := by
    have : 5 ∣ 2 * 5 * (100 * B3 + 1) ^ 13 :=
      dvd_mul_of_dvd_left (dvd_mul_right 2 5) _
    exact Nat.mod_eq_zero_of_dvd (h1eq ▸ this)
  obtain ⟨hA3e, hB3e⟩ := both_five_dvd_of_sum_fourth_mod5_zero hmod3
  obtain ⟨A4, hA4⟩ := hA3e
  obtain ⟨B4, hB4⟩ := hB3e
  have heq4src : (5 * A4) ^ 4 + (5 * B4) ^ 4 =
      2 * 5 * (500 * B4 + 1) ^ 13 := by
    have hB21 : 100 * B3 + 1 = 500 * B4 + 1 := by
      rw [hB4]; ring
    rw [← hA4, ← hB4, ← hB21]; exact h1eq
  have heq4 : 625 * (A4 ^ 4 + B4 ^ 4) =
      2 * 5 * (500 * B4 + 1) ^ 13 := by
    rw [← sum_fourth_of_mul_five]; exact heq4src
  have hlast : 125 * (A4 ^ 4 + B4 ^ 4) =
      2 * (500 * B4 + 1) ^ 13 := by
    have hpow : (625 : ℕ) = 5 * 125 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5)
    have hL : 5 * (125 * (A4 ^ 4 + B4 ^ 4)) =
        625 * (A4 ^ 4 + B4 ^ 4) := by
      rw [hpow, mul_assoc]
    rw [hL, heq4]
    ring
  have hLmod : (125 * (A4 ^ 4 + B4 ^ 4)) % 5 = 0 := by
    have : 5 ∣ 125 * (A4 ^ 4 + B4 ^ 4) :=
      dvd_mul_of_dvd_left (by decide : 5 ∣ 125) _
    exact Nat.mod_eq_zero_of_dvd this
  have hRmod : (2 * (500 * B4 + 1) ^ 13) % 5 = 2 := by
    have hC : (500 * B4 + 1) % 5 = 1 := by
      rw [Nat.add_mod, Nat.mul_mod]
      norm_num
    have h13 : (500 * B4 + 1) ^ 13 % 5 = 1 := by
      rw [pow13_mod5, hC]
    rw [Nat.mul_mod, h13]
  have hmod : (125 * (A4 ^ 4 + B4 ^ 4)) % 5 =
      (2 * (500 * B4 + 1) ^ 13) % 5 := by rw [hlast]
  rw [hLmod, hRmod] at hmod
  exact (by decide : (0 : ℕ) ≠ 2) hmod

/-! ## Original equation: `3 ∣ B` is compatible; `7 ∣ B` dies. -/

theorem fourth_pow_mod3 (a : ℕ) : a ^ 4 % 3 = 0 ∨ a ^ 4 % 3 = 1 :=
  BealMatveevBeal.BealGap4.fourth_pow_mod3 a

theorem pow13_mod3 (c : ℕ) : c ^ 13 % 3 = c % 3 :=
  BealMatveevBeal.BealGap4.pow13_mod3 c

/-- `C = B+10 ≡ 1 mod 3`, so `C¹³ ≡ 1` and `A⁴ ≡ 1`. No contradiction.
    Do **not** prove `no_sol_when_three_dvd_B`. -/
theorem A_pow_four_mod3_eq_one_of_three_dvd_B {A B : ℕ}
    (h : is_gap10_sol A B) (h3 : 3 ∣ B) : A ^ 4 % 3 = 1 := by
  have hB4 : B ^ 4 % 3 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h3 (by decide))
  have hC : (B + 10) % 3 = 1 := by
    have : B % 3 = 0 := Nat.mod_eq_zero_of_dvd h3
    rw [Nat.add_mod, this]
  have hC13 : (B + 10) ^ 13 % 3 = 1 := by
    rw [pow13_mod3, hC]
  have hsum : (A ^ 4 + B ^ 4) % 3 = (B + 10) ^ 13 % 3 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 := fourth_pow_mod3 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · exact h1

theorem fourth_pow_mod7 (a : ℕ) :
    a ^ 4 % 7 = 0 ∨ a ^ 4 % 7 = 1 ∨ a ^ 4 % 7 = 2 ∨ a ^ 4 % 7 = 4 :=
  BealMatveevBeal.BealGap7.fourth_pow_mod7 a

theorem pow13_mod7 (c : ℕ) : c ^ 13 % 7 = c % 7 :=
  BealMatveevBeal.BealGap7.pow13_mod7 c

/-- `C = B+10 ≡ 3 mod 7`, so `C¹³ ≡ 3` not in `{0,1,2,4}`. -/
theorem no_sol_when_seven_dvd_B_gap10 {A B : ℕ}
    (h : is_gap10_sol A B) (h7 : 7 ∣ B) : False := by
  have hB4 : B ^ 4 % 7 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h7 (by decide))
  have hC : (B + 10) % 7 = 3 := by
    have : B % 7 = 0 := Nat.mod_eq_zero_of_dvd h7
    rw [Nat.add_mod, this]
  have hC13 : (B + 10) ^ 13 % 7 = 3 := by
    rw [pow13_mod7, hC]
  have hsum : (A ^ 4 + B ^ 4) % 7 = (B + 10) ^ 13 % 7 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  obtain h0 | h1 | h2 | h4 := fourth_pow_mod7 A
  · rw [h0] at hsum
    exact absurd hsum (by decide)
  · rw [h1] at hsum
    exact absurd hsum (by decide)
  · rw [h2] at hsum
    exact absurd hsum (by decide)
  · rw [h4] at hsum
    exact absurd hsum (by decide)

theorem seven_not_dvd_B_of_sol {A B : ℕ}
    (h : is_gap10_sol A B) : ¬ 7 ∣ B :=
  fun h7 => no_sol_when_seven_dvd_B_gap10 h h7

end BealMatveevBeal.BealGap10
