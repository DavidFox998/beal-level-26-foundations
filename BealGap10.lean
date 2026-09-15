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
even `C` is `0` and odd `C` is odd, never `2`). Even `B` reduces
after three `/2` to last-step `A₃⁴ + B₃⁴ = 2 (4 B₃ + 5)¹³`.
Even `B₃` dies as residue `10` mod 16; last-step `5 ∣ B₃` dies
by 5-descent; last-step `B ≡ 1,3 mod 5` die. Remaining even-`B`
last-step is both-odd 5-free `B₃ ≡ 2 ∨ 4` (not killed here).
Do **not** prove `B_odd_of_sol_gap10` / `no_sol_when_even_B`.
The original Gaussian cones `e ≥ 5d` and `d ≥ 10e` are polynomial
identities (`re13_gt_of_five_mul`, `re13_gt_of_ten_mul`); `|d|=1`
is `re13_one_ne_pm_rhs`. Middle cone leftover bands plus brute
`d ≤ 100` and gcd-scale are `re13_gt_of_middle_cone` (extra `hfin`;
tan-ray primitives `d ≥ 101` remain). `(1,0)` is **not** a solution
(`1 ≠ 10¹³`). `3 ∣ B` is compatible (`C ≡ 1 mod 3`, `A⁴ ≡ 1`).
`5 ∣ B` kills by original 5-descent (`C₁ = B₁+2`, last step
`125 X = (125 B₄ + 2)¹³ ≡ 2` mod 5). `7 ∣ B` kills residue
(`C ≡ 3 mod 7`, `C¹³ ≡ 3` not in `{0,1,2,4}`). Odd-`B` remaining
solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 10`, but `B` is odd and
`5 ∤ B`) and pure Darmon–Merel signature `(4,4,13)`.

`hGen_gap10` / `hLLL_gap10` stay `def Prop`. Every `C1 ≥ 1` loses
to `B⁴/A⁴` on `B ≥ B0`; no scaling yields a Baker–Davenport
witness above `17 + C/B0`. Named theorem `baker_bound_gap10`
stays a `def Prop`. 0 sorry. No new axiom.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

set_option maxHeartbeats 4000000

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
  rw [Int.natCast_natAbs, sq_abs]

/-- `C x¹³ − D x⁴ − K > 0` when `1 ≤ x` and `D + K < C`. -/
lemma pow13_sub_pow4_const_pos (x C D K : ℤ) (hx : 1 ≤ x)
    (hD : 0 ≤ D) (hK : 0 ≤ K) (hC : D + K < C) :
    0 < C * x ^ 13 - D * x ^ 4 - K := by
  have hx13 : (1 : ℤ) ≤ x ^ 13 := one_le_pow_of_one_le hx 13
  have hle : x ^ 4 ≤ x ^ 13 := pow_le_pow_right hx (by decide : (4 : ℕ) ≤ 13)
  have h1 : C * x ^ 13 - D * x ^ 4 - K ≥ C * x ^ 13 - D * x ^ 13 - K := by
    nlinarith
  have h2 : C * x ^ 13 - D * x ^ 13 - K = (C - D) * x ^ 13 - K := by ring
  have hCD : (1 : ℤ) ≤ C - D := by linarith
  have h3 : (C - D) * x ^ 13 - K ≥ (C - D) * 1 - K := by
    nlinarith [hx13, hCD]
  linarith

/-- AM-GM: `2xy ≤ x² + y²`. -/
lemma two_mul_le_sq_add (x y : ℤ) : 2 * x * y ≤ x ^ 2 + y ^ 2 := by
  have h : 0 ≤ (x - y) ^ 2 := sq_nonneg (x - y)
  have : (x - y) ^ 2 = x ^ 2 - 2 * x * y + y ^ 2 := by ring
  linarith

lemma re13_one_gt_rhs (e : ℕ) (he : 5 ≤ e) :
    (13 : ℤ) * (e : ℤ) ^ 12 - 286 * (e : ℤ) ^ 10 + 1287 * (e : ℤ) ^ 8
      - 1716 * (e : ℤ) ^ 6 + 715 * (e : ℤ) ^ 4 - 78 * (e : ℤ) ^ 2 + 1
    > ((e : ℤ) ^ 2 - 9) ^ 2 := by
  have h5 : 5 ≤ (e : ℤ) := by exact_mod_cast he
  have h0 : 0 ≤ (e : ℤ) := by exact_mod_cast (Nat.zero_le e)
  have hdom : (13 : ℤ) * e ^ 12 - 286 * e ^ 10 ≥ 39 * e ^ 10 := by
    have hfac : (13 : ℤ) * e ^ 12 - 286 * e ^ 10 =
        e ^ 10 * (13 * e ^ 2 - 286) := by ring
    have hcoeff : (39 : ℤ) ≤ 13 * e ^ 2 - 286 := by
      nlinarith [h5, sq_nonneg (e : ℤ)]
    have hpos : (0 : ℤ) ≤ e ^ 10 := pow_nonneg h0 10
    have : (39 : ℤ) * e ^ 10 ≤ e ^ 10 * (13 * e ^ 2 - 286) := by
      simpa [mul_comm] using mul_le_mul_of_nonneg_left hcoeff hpos
    linarith [hfac]
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
  rw [h2, h4, h6, h8, h10, h12]
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
  · rw [h0]; native_decide
  · rw [h2]; native_decide
  · rw [h3]; native_decide
  · rw [h4]; native_decide
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
  linarith [hgt]

theorem re13_poly_gt_of_five_mul (d e : ℕ) (hd : 1 ≤ d) (he : 5 * d ≤ e) :
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
  linarith [hgt]

theorem re13_poly_gt_of_ten_mul (d e : ℕ) (he : 1 ≤ e) (hd : 10 * e ≤ d) :
    (13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set k := d - 10 * e
  have hk : d = 10 * e + k := (Nat.add_sub_of_le hd).symm
  rw [hk]
  exact re13_gt_of_ten_mul_k e k he


/-! ## Middle cone: `2d ≤ e ≤ 4d` (between tan rays `1.905` and `4.057`) -/

lemma pow_le_of_le_two_mul {d k : ℕ} (n : ℕ)
    (h0k : (0 : ℤ) ≤ k) (hk : (k : ℤ) ≤ 2 * d) :
    (k : ℤ) ^ n ≤ (2 : ℤ) ^ n * d ^ n := by
  have h := pow_le_pow_left h0k hk n
  have : ((2 : ℤ) * d) ^ n = (2 : ℤ) ^ n * d ^ n := mul_pow _ _ n
  rwa [this] at h

lemma re13_neg_gt_two_four_k (d k : ℕ) (hd : 1 ≤ d) (hk : k ≤ 2 * d) :
    -((13 : ℤ) * d * (2 * d + k : ℤ) ^ 12
      - 286 * (d : ℤ) ^ 3 * (2 * d + k) ^ 10
      + 1287 * (d : ℤ) ^ 5 * (2 * d + k) ^ 8
      - 1716 * (d : ℤ) ^ 7 * (2 * d + k) ^ 6
      + 715 * (d : ℤ) ^ 9 * (2 * d + k) ^ 4
      - 78 * (d : ℤ) ^ 11 * (2 * d + k) ^ 2
      + (d : ℤ) ^ 13)
    > ((d : ℤ) ^ 2 + (2 * d + k : ℤ) ^ 2 - 10) ^ 2 := by
  have h1 : (1 : ℤ) ≤ d := by exact_mod_cast hd
  have h0d : (0 : ℤ) ≤ d := le_trans (by norm_num) h1
  have h0k : (0 : ℤ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hk' : (k : ℤ) ≤ 2 * d := by exact_mod_cast hk
  have hd4 : (1 : ℤ) ≤ d ^ 4 := one_le_pow_of_one_le h1 4
  have hk2 : (k : ℤ) ^ 2 ≤ 4 * d ^ 2 := by
    simpa using pow_le_of_le_two_mul 2 h0k hk'
  have hk3 : (k : ℤ) ^ 3 ≤ 8 * d ^ 3 := by
    simpa using pow_le_of_le_two_mul 3 h0k hk'
  have hk4 : (k : ℤ) ^ 4 ≤ 16 * d ^ 4 := by
    simpa using pow_le_of_le_two_mul 4 h0k hk'
  have hk5 : (k : ℤ) ^ 5 ≤ 32 * d ^ 5 := by
    simpa using pow_le_of_le_two_mul 5 h0k hk'
  have hk6 : (k : ℤ) ^ 6 ≤ 64 * d ^ 6 := by
    simpa using pow_le_of_le_two_mul 6 h0k hk'
  have hk7 : (k : ℤ) ^ 7 ≤ 128 * d ^ 7 := by
    simpa using pow_le_of_le_two_mul 7 h0k hk'
  have hexp :
      -((13 : ℤ) * d * (2 * d + k) ^ 12
        - 286 * d ^ 3 * (2 * d + k) ^ 10
        + 1287 * d ^ 5 * (2 * d + k) ^ 8
        - 1716 * d ^ 7 * (2 * d + k) ^ 6
        + 715 * d ^ 9 * (2 * d + k) ^ 4
        - 78 * d ^ 11 * (2 * d + k) ^ 2
        + d ^ 13)
      - ((d : ℤ) ^ 2 + (2 * d + k) ^ 2 - 10) ^ 2
      = (8839 : ℤ) * d ^ 13
        + 133848 * d ^ 12 * k
        + 504582 * d ^ 11 * k ^ 2
        + 891176 * d ^ 10 * k ^ 3
        + 857285 * d ^ 9 * k ^ 4
        + 432432 * d ^ 8 * k ^ 5
        + 49764 * d ^ 7 * k ^ 6
        - 75504 * d ^ 6 * k ^ 7
        - 52767 * d ^ 5 * k ^ 8
        - 17160 * d ^ 4 * k ^ 9
        - 3146 * d ^ 3 * k ^ 10
        - 312 * d ^ 2 * k ^ 11
        - 13 * d * k ^ 12
        - 25 * d ^ 4
        - 40 * d ^ 3 * k
        - 26 * d ^ 2 * k ^ 2
        - 8 * d * k ^ 3
        - k ^ 4
        + 100 * d ^ 2
        + 80 * d * k
        + 20 * k ^ 2
        - 100 := by
    ring
  have hA : (0 : ℤ) <
      8839 * d ^ 13 - 25 * d ^ 4 - 40 * d ^ 3 * k - 26 * d ^ 2 * k ^ 2
        - 8 * d * k ^ 3 - k ^ 4 - 100 := by
    have hb1 : (40 : ℤ) * d ^ 3 * k ≤ 80 * d ^ 4 := by
      have : (40 : ℤ) * d ^ 3 * k ≤ 40 * d ^ 3 * (2 * d) :=
        mul_le_mul_of_nonneg_left hk' (mul_nonneg (by norm_num) (pow_nonneg h0d 3))
      have hrew : (40 : ℤ) * d ^ 3 * (2 * d) = 80 * d ^ 4 := by ring
      linarith [hrew]
    have hb2 : (26 : ℤ) * d ^ 2 * k ^ 2 ≤ 104 * d ^ 4 := by
      have : (26 : ℤ) * d ^ 2 * k ^ 2 ≤ 26 * d ^ 2 * (4 * d ^ 2) :=
        mul_le_mul_of_nonneg_left hk2 (mul_nonneg (by norm_num) (pow_nonneg h0d 2))
      have hrew : (26 : ℤ) * d ^ 2 * (4 * d ^ 2) = 104 * d ^ 4 := by ring
      linarith [hrew]
    have hb3 : (8 : ℤ) * d * k ^ 3 ≤ 64 * d ^ 4 := by
      have : (8 : ℤ) * d * k ^ 3 ≤ 8 * d * (8 * d ^ 3) :=
        mul_le_mul_of_nonneg_left hk3 (mul_nonneg (by norm_num) h0d)
      have hrew : (8 : ℤ) * d * (8 * d ^ 3) = 64 * d ^ 4 := by ring
      linarith [hrew]
    have hb4 : (k : ℤ) ^ 4 ≤ 16 * d ^ 4 := hk4
    have hbound :
        (25 : ℤ) * d ^ 4 + 40 * d ^ 3 * k + 26 * d ^ 2 * k ^ 2
          + 8 * d * k ^ 3 + k ^ 4 + 100 ≤ 289 * d ^ 4 + 100 := by
      linarith [hb1, hb2, hb3, hb4]
    have hbig : (0 : ℤ) < 8839 * d ^ 13 - 289 * d ^ 4 - 100 := by
      have hfac : (8839 : ℤ) * d ^ 13 - 289 * d ^ 4 =
          d ^ 4 * (8839 * d ^ 9 - 289) := by ring
      have hd9 : (1 : ℤ) ≤ d ^ 9 := one_le_pow_of_one_le h1 9
      have hinner : (390 : ℤ) ≤ 8839 * d ^ 9 - 289 := by
        have : (1 : ℤ) * 8839 ≤ 8839 * d ^ 9 :=
          mul_le_mul_of_nonneg_left hd9 (by norm_num)
        linarith
      have hmul : (101 : ℤ) ≤ d ^ 4 * (8839 * d ^ 9 - 289) := by
        have h101 : (101 : ℤ) ≤ 8839 * d ^ 9 - 289 := le_trans (by norm_num) hinner
        have : (1 : ℤ) * 101 ≤ d ^ 4 * (8839 * d ^ 9 - 289) :=
          mul_le_mul hd4 h101 (by linarith) (le_trans (by norm_num : (0 : ℤ) ≤ 1) hd4)
        simpa using this
      linarith [hfac, hmul]
    linarith [hbound, hbig]
  have hn2 : (0 : ℤ) ≤ 857285 * d ^ 9 * k ^ 4 - 52767 * d ^ 5 * k ^ 8 := by
    have hfac : (857285 : ℤ) * d ^ 9 * k ^ 4 - 52767 * d ^ 5 * k ^ 8 =
        d ^ 5 * k ^ 4 * (857285 * d ^ 4 - 52767 * k ^ 4) := by ring
    have hinter : (0 : ℤ) ≤ 857285 * d ^ 4 - 52767 * k ^ 4 := by
      have hle : (52767 : ℤ) * k ^ 4 ≤ 52767 * (16 * d ^ 4) :=
        mul_le_mul_of_nonneg_left hk4 (by norm_num)
      have hrew : (52767 : ℤ) * (16 * d ^ 4) = 844272 * d ^ 4 := by ring
      have hco : (844272 : ℤ) * d ^ 4 ≤ 857285 * d ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num : (844272 : ℤ) ≤ 857285)
          (pow_nonneg h0d 4)
      linarith [hle, hrew, hco]
    have hmul : (0 : ℤ) ≤ d ^ 5 * k ^ 4 * (857285 * d ^ 4 - 52767 * k ^ 4) :=
      mul_nonneg (mul_nonneg (pow_nonneg h0d 5) (pow_nonneg h0k 4)) hinter
    linarith [hfac, hmul]
  have hn3 : (0 : ℤ) ≤
      504582 * d ^ 11 * k ^ 2 + 891176 * d ^ 10 * k ^ 3 - 17160 * d ^ 4 * k ^ 9 := by
    have hle9 : (17160 : ℤ) * d ^ 4 * k ^ 9 ≤ 1098240 * d ^ 10 * k ^ 3 := by
      have hfac : (17160 : ℤ) * d ^ 4 * k ^ 9 = 17160 * d ^ 4 * k ^ 3 * k ^ 6 := by ring
      have hle : (17160 : ℤ) * d ^ 4 * k ^ 3 * k ^ 6 ≤
          17160 * d ^ 4 * k ^ 3 * (64 * d ^ 6) := by
        have hpos : (0 : ℤ) ≤ 17160 * d ^ 4 * k ^ 3 :=
          mul_nonneg (mul_nonneg (by norm_num : (0 : ℤ) ≤ 17160) (pow_nonneg h0d 4))
            (pow_nonneg h0k 3)
        exact mul_le_mul_of_nonneg_left hk6 hpos
      have hrew : (17160 : ℤ) * d ^ 4 * k ^ 3 * (64 * d ^ 6) =
          1098240 * d ^ 10 * k ^ 3 := by ring
      linarith [hfac, hle, hrew]
    have hcomb : (891176 : ℤ) * d ^ 10 * k ^ 3 - 17160 * d ^ 4 * k ^ 9 ≥
        891176 * d ^ 10 * k ^ 3 - 1098240 * d ^ 10 * k ^ 3 := by
      linarith [hle9]
    have hrew : (891176 : ℤ) * d ^ 10 * k ^ 3 - 1098240 * d ^ 10 * k ^ 3 =
        (891176 - 1098240 : ℤ) * d ^ 10 * k ^ 3 := by ring
    have hC : (0 : ℤ) ≤ 504582 * d ^ 11 * k ^ 2 +
        (891176 - 1098240 : ℤ) * d ^ 10 * k ^ 3 := by
      have hfac : (504582 : ℤ) * d ^ 11 * k ^ 2 +
          (891176 - 1098240 : ℤ) * d ^ 10 * k ^ 3 =
          d ^ 10 * k ^ 2 * (504582 * d + (891176 - 1098240 : ℤ) * k) := by ring
      have hinter : (0 : ℤ) ≤ 504582 * d + (891176 - 1098240 : ℤ) * k := by
        have hk2d : (k : ℤ) ≤ 2 * d := hk'
        have hneg : (891176 - 1098240 : ℤ) * k ≥ (891176 - 1098240 : ℤ) * (2 * d) := by
          have hco : (891176 - 1098240 : ℤ) ≤ 0 := by norm_num
          exact mul_le_mul_of_nonpos_left hk2d hco
        have hrew2 : (891176 - 1098240 : ℤ) * (2 * d) = (891176 - 1098240 : ℤ) * 2 * d := by
          ring
        have hsum : (504582 : ℤ) * d + (891176 - 1098240 : ℤ) * 2 * d =
            (504582 + (891176 - 1098240 : ℤ) * 2) * d := by ring
        have hpos : (0 : ℤ) ≤ (504582 + (891176 - 1098240 : ℤ) * 2) * d := by
          have : (0 : ℤ) ≤ 504582 + (891176 - 1098240 : ℤ) * 2 := by norm_num
          exact mul_nonneg this h0d
        linarith [hneg, hrew2, hsum, hpos]
      have : (0 : ℤ) ≤ d ^ 10 * k ^ 2 *
          (504582 * d + (891176 - 1098240 : ℤ) * k) :=
        mul_nonneg (mul_nonneg (pow_nonneg h0d 10) (pow_nonneg h0k 2)) hinter
      linarith [hfac, this]
    linarith [hcomb, hrew, hC]
  have hF1 : (130416 : ℤ) * d ^ 8 * k ^ 5 ≤
      432432 * d ^ 8 * k ^ 5 - 75504 * d ^ 6 * k ^ 7 := by
    have hfac : (432432 : ℤ) * d ^ 8 * k ^ 5 - 75504 * d ^ 6 * k ^ 7 =
        d ^ 6 * k ^ 5 * (432432 * d ^ 2 - 75504 * k ^ 2) := by ring
    have hinter : (130416 : ℤ) * d ^ 2 ≤ 432432 * d ^ 2 - 75504 * k ^ 2 := by
      have hle : (75504 : ℤ) * k ^ 2 ≤ 302016 * d ^ 2 := by
        have : (75504 : ℤ) * k ^ 2 ≤ 75504 * (4 * d ^ 2) :=
          mul_le_mul_of_nonneg_left hk2 (by norm_num)
        have hrew : (75504 : ℤ) * (4 * d ^ 2) = 302016 * d ^ 2 := by ring
        linarith [this, hrew]
      linarith [hle]
    have hrew : (130416 : ℤ) * d ^ 8 * k ^ 5 =
        d ^ 6 * k ^ 5 * (130416 * d ^ 2) := by ring
    have := mul_le_mul_of_nonneg_left hinter
      (mul_nonneg (pow_nonneg h0d 6) (pow_nonneg h0k 5))
    linarith [hfac, hrew, this]
  have hF2 : (29744 : ℤ) * d ^ 8 * k ^ 5 ≤
      130416 * d ^ 8 * k ^ 5 - 3146 * d ^ 3 * k ^ 10 := by
    have hfac : (130416 : ℤ) * d ^ 8 * k ^ 5 - 3146 * d ^ 3 * k ^ 10 =
        d ^ 3 * k ^ 5 * (130416 * d ^ 5 - 3146 * k ^ 5) := by ring
    have hinter : (29744 : ℤ) * d ^ 5 ≤ 130416 * d ^ 5 - 3146 * k ^ 5 := by
      have hle : (3146 : ℤ) * k ^ 5 ≤ 100672 * d ^ 5 := by
        have : (3146 : ℤ) * k ^ 5 ≤ 3146 * (32 * d ^ 5) :=
          mul_le_mul_of_nonneg_left hk5 (by norm_num)
        have hrew : (3146 : ℤ) * (32 * d ^ 5) = 100672 * d ^ 5 := by ring
        linarith [this, hrew]
      linarith [hle]
    have hrew : (29744 : ℤ) * d ^ 8 * k ^ 5 =
        d ^ 3 * k ^ 5 * (29744 * d ^ 5) := by ring
    have := mul_le_mul_of_nonneg_left hinter
      (mul_nonneg (pow_nonneg h0d 3) (pow_nonneg h0k 5))
    linarith [hfac, hrew, this]
  have hF3 : (9776 : ℤ) * d ^ 8 * k ^ 5 ≤
      29744 * d ^ 8 * k ^ 5 - 312 * d ^ 2 * k ^ 11 := by
    have hfac : (29744 : ℤ) * d ^ 8 * k ^ 5 - 312 * d ^ 2 * k ^ 11 =
        d ^ 2 * k ^ 5 * (29744 * d ^ 6 - 312 * k ^ 6) := by ring
    have hinter : (9776 : ℤ) * d ^ 6 ≤ 29744 * d ^ 6 - 312 * k ^ 6 := by
      have hle : (312 : ℤ) * k ^ 6 ≤ 19968 * d ^ 6 := by
        have : (312 : ℤ) * k ^ 6 ≤ 312 * (64 * d ^ 6) :=
          mul_le_mul_of_nonneg_left hk6 (by norm_num)
        have hrew : (312 : ℤ) * (64 * d ^ 6) = 19968 * d ^ 6 := by ring
        linarith [this, hrew]
      linarith [hle]
    have hrew : (9776 : ℤ) * d ^ 8 * k ^ 5 =
        d ^ 2 * k ^ 5 * (9776 * d ^ 6) := by ring
    have := mul_le_mul_of_nonneg_left hinter
      (mul_nonneg (pow_nonneg h0d 2) (pow_nonneg h0k 5))
    linarith [hfac, hrew, this]
  have hF4 : (0 : ℤ) ≤ 9776 * d ^ 8 * k ^ 5 - 13 * d * k ^ 12 := by
    have hfac : (9776 : ℤ) * d ^ 8 * k ^ 5 - 13 * d * k ^ 12 =
        d * k ^ 5 * (9776 * d ^ 7 - 13 * k ^ 7) := by ring
    have hinter : (0 : ℤ) ≤ 9776 * d ^ 7 - 13 * k ^ 7 := by
      have hle : (13 : ℤ) * k ^ 7 ≤ 1664 * d ^ 7 := by
        have : (13 : ℤ) * k ^ 7 ≤ 13 * (128 * d ^ 7) :=
          mul_le_mul_of_nonneg_left hk7 (by norm_num)
        have hrew : (13 : ℤ) * (128 * d ^ 7) = 1664 * d ^ 7 := by ring
        linarith [this, hrew]
      have hco : (1664 : ℤ) * d ^ 7 ≤ 9776 * d ^ 7 :=
        mul_le_mul_of_nonneg_right (by norm_num : (1664 : ℤ) ≤ 9776)
          (pow_nonneg h0d 7)
      linarith [hle, hco]
    have := mul_nonneg (mul_nonneg h0d (pow_nonneg h0k 5)) hinter
    linarith [hfac, this]
  have hFchain : (0 : ℤ) ≤
      432432 * d ^ 8 * k ^ 5 - 75504 * d ^ 6 * k ^ 7
        - 3146 * d ^ 3 * k ^ 10 - 312 * d ^ 2 * k ^ 11 - 13 * d * k ^ 12 := by
    linarith [hF1, hF2, hF3, hF4]
  have hrest : (0 : ℤ) ≤ 133848 * d ^ 12 * k + 49764 * d ^ 7 * k ^ 6
      + 100 * d ^ 2 + 80 * d * k + 20 * k ^ 2 := by
    have hr1 : (0 : ℤ) ≤ 133848 * d ^ 12 * k :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0d 12)) h0k
    have hr2 : (0 : ℤ) ≤ 49764 * d ^ 7 * k ^ 6 :=
      mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg h0d 7)) (pow_nonneg h0k 6)
    have hr3 : (0 : ℤ) ≤ 100 * d ^ 2 :=
      mul_nonneg (by norm_num) (pow_nonneg h0d 2)
    have hr4 : (0 : ℤ) ≤ 80 * d * k :=
      mul_nonneg (mul_nonneg (by norm_num) h0d) h0k
    have hr5 : (0 : ℤ) ≤ 20 * k ^ 2 :=
      mul_nonneg (by norm_num) (pow_nonneg h0k 2)
    linarith [hr1, hr2, hr3, hr4, hr5]
  have hgt : (0 : ℤ) <
      -((13 : ℤ) * d * (2 * d + k) ^ 12
        - 286 * d ^ 3 * (2 * d + k) ^ 10
        + 1287 * d ^ 5 * (2 * d + k) ^ 8
        - 1716 * d ^ 7 * (2 * d + k) ^ 6
        + 715 * d ^ 9 * (2 * d + k) ^ 4
        - 78 * d ^ 11 * (2 * d + k) ^ 2
        + d ^ 13)
      - ((d : ℤ) ^ 2 + (2 * d + k) ^ 2 - 10) ^ 2 := by
    rw [hexp]
    linarith [hA, hn2, hn3, hFchain, hrest]
  linarith [hgt]


theorem re13_gt_of_two_four (d e : ℕ) (hd : 1 ≤ d) (h2 : 2 * d ≤ e) (h4 : e ≤ 4 * d) :
    -((13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13)
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set k := e - 2 * d
  have hk : e = 2 * d + k := (Nat.add_sub_of_le h2).symm
  have hk2 : k ≤ 2 * d := by
    simp only [k]
    omega
  rw [hk]
  exact re13_neg_gt_two_four_k d k hd hk2

lemma pow_le_of_le_four_mul {e k : ℕ} (n : ℕ)
    (h0k : (0 : ℤ) ≤ k) (hk : (k : ℤ) ≤ 4 * e) :
    (k : ℤ) ^ n ≤ (4 : ℤ) ^ n * e ^ n := by
  have h := pow_le_pow_left h0k hk n
  have : ((4 : ℤ) * e) ^ n = (4 : ℤ) ^ n * e ^ n := mul_pow _ _ n
  rwa [this] at h

/-- `d = 3e+k` with `k ≤ 4e` covers `t = e/d ∈ [1/7, 1/3]`. -/
lemma re13_neg_gt_three_seven_k (e k : ℕ) (he : 1 ≤ e) (hk : k ≤ 4 * e) :
    -((13 : ℤ) * (3 * e + k) * (e : ℤ) ^ 12
      - 286 * (3 * e + k : ℤ) ^ 3 * e ^ 10
      + 1287 * (3 * e + k : ℤ) ^ 5 * e ^ 8
      - 1716 * (3 * e + k : ℤ) ^ 7 * e ^ 6
      + 715 * (3 * e + k : ℤ) ^ 9 * e ^ 4
      - 78 * (3 * e + k : ℤ) ^ 11 * e ^ 2
      + (3 * e + k : ℤ) ^ 13)
    > ((3 * e + k : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  have h1 : (1 : ℤ) ≤ e := by exact_mod_cast he
  have h0e : (0 : ℤ) ≤ e := le_trans (by norm_num) h1
  have h0k : (0 : ℤ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hk' : (k : ℤ) ≤ 4 * e := by exact_mod_cast hk
  have he4 : (1 : ℤ) ≤ e ^ 4 := one_le_pow_of_one_le h1 4
  have hk4 : (k : ℤ) ^ 4 ≤ 256 * e ^ 4 := by
    have := pow_le_of_le_four_mul 4 h0k hk'
    simpa using this
  have hk9 : (k : ℤ) ^ 9 ≤ 262144 * e ^ 9 := by
    have := pow_le_of_le_four_mul 9 h0k hk'
    simpa using this
  have hexp :
      -((13 : ℤ) * (3 * e + k) * e ^ 12
        - 286 * (3 * e + k) ^ 3 * e ^ 10
        + 1287 * (3 * e + k) ^ 5 * e ^ 8
        - 1716 * (3 * e + k) ^ 7 * e ^ 6
        + 715 * (3 * e + k) ^ 9 * e ^ 4
        - 78 * (3 * e + k) ^ 11 * e ^ 2
        + (3 * e + k) ^ 13)
      - ((3 * e + k : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2
      = (1597632 : ℤ) * e ^ 13
        + 9778496 * e ^ 12 * k
        + 22741056 * e ^ 11 * k ^ 2
        + 28517632 * e ^ 10 * k ^ 3
        + 21930480 * e ^ 9 * k ^ 4
        + 10851984 * e ^ 8 * k ^ 5
        + 3418272 * e ^ 7 * k ^ 6
        + 604032 * e ^ 6 * k ^ 7
        + 15444 * e ^ 5 * k ^ 8
        - 20020 * e ^ 4 * k ^ 9
        - 5148 * e ^ 3 * k ^ 10
        - 624 * e ^ 2 * k ^ 11
        - 39 * e * k ^ 12
        - k ^ 13
        - 100 * e ^ 4
        - 120 * e ^ 3 * k
        - 56 * e ^ 2 * k ^ 2
        - 12 * e * k ^ 3
        - k ^ 4
        + 200 * e ^ 2
        + 120 * e * k
        + 20 * k ^ 2
        - 100 := by
    ring
  have hn1 : (0 : ℤ) ≤ 10851984 * e ^ 8 * k ^ 5 - 20020 * e ^ 4 * k ^ 9 := by
    have hfac : (10851984 : ℤ) * e ^ 8 * k ^ 5 - 20020 * e ^ 4 * k ^ 9 =
        e ^ 4 * k ^ 5 * (10851984 * e ^ 4 - 20020 * k ^ 4) := by ring
    have hinter : (0 : ℤ) ≤ 10851984 * e ^ 4 - 20020 * k ^ 4 := by
      have hle : (20020 : ℤ) * k ^ 4 ≤ 20020 * (256 * e ^ 4) :=
        mul_le_mul_of_nonneg_left hk4 (by norm_num)
      have hrew : (20020 : ℤ) * (256 * e ^ 4) = 5125120 * e ^ 4 := by ring
      have hco : (5125120 : ℤ) * e ^ 4 ≤ 10851984 * e ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num : (5125120 : ℤ) ≤ 10851984)
          (pow_nonneg h0e 4)
      linarith [hle, hrew, hco]
    have := mul_nonneg (mul_nonneg (pow_nonneg h0e 4) (pow_nonneg h0k 5)) hinter
    linarith [hfac, this]
  have hn2 : (0 : ℤ) ≤ 3418272 * e ^ 7 * k ^ 6 - 5148 * e ^ 3 * k ^ 10 := by
    have hfac : (3418272 : ℤ) * e ^ 7 * k ^ 6 - 5148 * e ^ 3 * k ^ 10 =
        e ^ 3 * k ^ 6 * (3418272 * e ^ 4 - 5148 * k ^ 4) := by ring
    have hinter : (0 : ℤ) ≤ 3418272 * e ^ 4 - 5148 * k ^ 4 := by
      have hle : (5148 : ℤ) * k ^ 4 ≤ 5148 * (256 * e ^ 4) :=
        mul_le_mul_of_nonneg_left hk4 (by norm_num)
      have hrew : (5148 : ℤ) * (256 * e ^ 4) = 1317888 * e ^ 4 := by ring
      have hco : (1317888 : ℤ) * e ^ 4 ≤ 3418272 * e ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num : (1317888 : ℤ) ≤ 3418272)
          (pow_nonneg h0e 4)
      linarith [hle, hrew, hco]
    have := mul_nonneg (mul_nonneg (pow_nonneg h0e 3) (pow_nonneg h0k 6)) hinter
    linarith [hfac, this]
  have hn3 : (0 : ℤ) ≤ 604032 * e ^ 6 * k ^ 7 - 624 * e ^ 2 * k ^ 11 := by
    have hfac : (604032 : ℤ) * e ^ 6 * k ^ 7 - 624 * e ^ 2 * k ^ 11 =
        e ^ 2 * k ^ 7 * (604032 * e ^ 4 - 624 * k ^ 4) := by ring
    have hinter : (0 : ℤ) ≤ 604032 * e ^ 4 - 624 * k ^ 4 := by
      have hle : (624 : ℤ) * k ^ 4 ≤ 624 * (256 * e ^ 4) :=
        mul_le_mul_of_nonneg_left hk4 (by norm_num)
      have hrew : (624 : ℤ) * (256 * e ^ 4) = 159744 * e ^ 4 := by ring
      have hco : (159744 : ℤ) * e ^ 4 ≤ 604032 * e ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num : (159744 : ℤ) ≤ 604032)
          (pow_nonneg h0e 4)
      linarith [hle, hrew, hco]
    have := mul_nonneg (mul_nonneg (pow_nonneg h0e 2) (pow_nonneg h0k 7)) hinter
    linarith [hfac, this]
  have hn4 : (0 : ℤ) ≤ 15444 * e ^ 5 * k ^ 8 - 39 * e * k ^ 12 := by
    have hfac : (15444 : ℤ) * e ^ 5 * k ^ 8 - 39 * e * k ^ 12 =
        e * k ^ 8 * (15444 * e ^ 4 - 39 * k ^ 4) := by ring
    have hinter : (0 : ℤ) ≤ 15444 * e ^ 4 - 39 * k ^ 4 := by
      have hle : (39 : ℤ) * k ^ 4 ≤ 39 * (256 * e ^ 4) :=
        mul_le_mul_of_nonneg_left hk4 (by norm_num)
      have hrew : (39 : ℤ) * (256 * e ^ 4) = 9984 * e ^ 4 := by ring
      have hco : (9984 : ℤ) * e ^ 4 ≤ 15444 * e ^ 4 :=
        mul_le_mul_of_nonneg_right (by norm_num : (9984 : ℤ) ≤ 15444)
          (pow_nonneg h0e 4)
      linarith [hle, hrew, hco]
    have := mul_nonneg (mul_nonneg h0e (pow_nonneg h0k 8)) hinter
    linarith [hfac, this]
  have hn5 : (0 : ℤ) ≤ 21930480 * e ^ 9 * k ^ 4 - k ^ 13 := by
    have hfac : (21930480 : ℤ) * e ^ 9 * k ^ 4 - k ^ 13 =
        k ^ 4 * (21930480 * e ^ 9 - k ^ 9) := by ring
    have hinter : (0 : ℤ) ≤ 21930480 * e ^ 9 - k ^ 9 := by
      have hle : (k : ℤ) ^ 9 ≤ 262144 * e ^ 9 := hk9
      have hco : (262144 : ℤ) * e ^ 9 ≤ 21930480 * e ^ 9 :=
        mul_le_mul_of_nonneg_right (by norm_num : (262144 : ℤ) ≤ 21930480)
          (pow_nonneg h0e 9)
      linarith [hle, hco]
    have := mul_nonneg (pow_nonneg h0k 4) hinter
    linarith [hfac, this]
  have hA : (0 : ℤ) < 1597632 * e ^ 13 - 100 * e ^ 4 - k ^ 4 - 100 := by
    have hk4e : (k : ℤ) ^ 4 ≤ 256 * e ^ 4 := hk4
    have hfac : (1597632 : ℤ) * e ^ 13 - 356 * e ^ 4 =
        e ^ 4 * (1597632 * e ^ 9 - 356) := by ring
    have he9 : (1 : ℤ) ≤ e ^ 9 := one_le_pow_of_one_le h1 9
    have hinner : (200 : ℤ) ≤ 1597632 * e ^ 9 - 356 := by
      have : (1 : ℤ) * 1597632 ≤ 1597632 * e ^ 9 :=
        mul_le_mul_of_nonneg_left he9 (by norm_num)
      linarith
    have hmul : (101 : ℤ) ≤ e ^ 4 * (1597632 * e ^ 9 - 356) := by
      have h101 : (101 : ℤ) ≤ 1597632 * e ^ 9 - 356 := le_trans (by norm_num) hinner
      have : (1 : ℤ) * 101 ≤ e ^ 4 * (1597632 * e ^ 9 - 356) :=
        mul_le_mul he4 h101 (by linarith) (le_trans (by norm_num : (0 : ℤ) ≤ 1) he4)
      simpa using this
    linarith [hfac, hmul, hk4e]
  have hB : (0 : ℤ) ≤ 9778496 * e ^ 12 * k - 120 * e ^ 3 * k := by
    have hcoeff : (120 : ℤ) * e ^ 3 ≤ 9778496 * e ^ 12 := by
      have hpow : (e : ℤ) ^ 3 ≤ e ^ 12 := pow_le_pow_right h1 (by decide : (3 : ℕ) ≤ 12)
      nlinarith [hpow, h1, one_le_pow_of_one_le h1 3, one_le_pow_of_one_le h1 12]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_right hcoeff h0k)
  have hC : (0 : ℤ) ≤ 22741056 * e ^ 11 * k ^ 2 - 56 * e ^ 2 * k ^ 2 := by
    have hcoeff : (56 : ℤ) * e ^ 2 ≤ 22741056 * e ^ 11 := by
      have hpow : (e : ℤ) ^ 2 ≤ e ^ 11 := pow_le_pow_right h1 (by decide : (2 : ℕ) ≤ 11)
      nlinarith [hpow, one_le_pow_of_one_le h1 2, one_le_pow_of_one_le h1 11]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg h0k 2))
  have hD : (0 : ℤ) ≤ 28517632 * e ^ 10 * k ^ 3 - 12 * e * k ^ 3 := by
    have hcoeff : (12 : ℤ) * e ≤ 28517632 * e ^ 10 := by
      have hpow : (e : ℤ) ≤ e ^ 10 := by
        simpa using (pow_le_pow_right h1 (by decide : (1 : ℕ) ≤ 10) : (e : ℤ) ^ 1 ≤ e ^ 10)
      nlinarith [hpow, h1, one_le_pow_of_one_le h1 10]
    exact sub_nonneg.2 (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg h0k 3))
  have hrest : (0 : ℤ) ≤ 200 * e ^ 2 + 120 * e * k + 20 * k ^ 2 := by
    nlinarith [pow_nonneg h0e 2, h0e, h0k, pow_nonneg h0k 2]
  have hgt : (0 : ℤ) <
      -((13 : ℤ) * (3 * e + k) * e ^ 12
        - 286 * (3 * e + k) ^ 3 * e ^ 10
        + 1287 * (3 * e + k) ^ 5 * e ^ 8
        - 1716 * (3 * e + k) ^ 7 * e ^ 6
        + 715 * (3 * e + k) ^ 9 * e ^ 4
        - 78 * (3 * e + k) ^ 11 * e ^ 2
        + (3 * e + k) ^ 13)
      - ((3 * e + k : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
    rw [hexp]
    linarith [hA, hB, hC, hD, hn1, hn2, hn3, hn4, hn5, hrest]
  linarith [hgt]

theorem re13_gt_of_three_seven (d e : ℕ) (he : 1 ≤ e) (h3 : 3 * e ≤ d) (h7 : d ≤ 7 * e) :
    -((13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13)
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set k := d - 3 * e
  have hk : d = 3 * e + k := (Nat.add_sub_of_le h3).symm
  have hk2 : k ≤ 4 * e := by
    simp only [k]
    omega
  rw [hk]
  exact re13_neg_gt_three_seven_k e k he hk2

/-! ## Middle cone leftover: `7e ≤ d ≤ 8e` and `9e ≤ d ≤ 10e`. -/
lemma re13_neg_gt_seven_k (e k : ℕ) (he : 1 ≤ e) (hk : k ≤ e) :
    -((13 : ℤ) * (7 * e + k) * (e : ℤ) ^ 12
      - 286 * (7 * e + k : ℤ) ^ 3 * e ^ 10
      + 1287 * (7 * e + k) ^ 5 * e ^ 8
      - 1716 * (7 * e + k) ^ 7 * e ^ 6
      + 715 * (7 * e + k) ^ 9 * e ^ 4
      - 78 * (7 * e + k) ^ 11 * e ^ 2
      + (7 * e + k) ^ 13)
    > ((7 * e + k : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  have h1 : (1 : ℤ) ≤ e := by exact_mod_cast he
  have h0e : (0 : ℤ) ≤ e := le_trans (by norm_num) h1
  have h0k : (0 : ℤ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hk' : (k : ℤ) ≤ e := by exact_mod_cast hk
  have hk2 : (k : ℤ) ^ 2 ≤ e ^ 2 := pow_le_pow_left h0k hk' 2
  have hk3 : (k : ℤ) ^ 3 ≤ e ^ 3 := pow_le_pow_left h0k hk' 3
  have hk4 : (k : ℤ) ^ 4 ≤ e ^ 4 := pow_le_pow_left h0k hk' 4
  have hk5 : (k : ℤ) ^ 5 ≤ e ^ 5 := pow_le_pow_left h0k hk' 5
  have hk6 : (k : ℤ) ^ 6 ≤ e ^ 6 := pow_le_pow_left h0k hk' 6
  have hk7 : (k : ℤ) ^ 7 ≤ e ^ 7 := pow_le_pow_left h0k hk' 7
  have hk8 : (k : ℤ) ^ 8 ≤ e ^ 8 := pow_le_pow_left h0k hk' 8
  have hk9 : (k : ℤ) ^ 9 ≤ e ^ 9 := pow_le_pow_left h0k hk' 9
  have hk10 : (k : ℤ) ^ 10 ≤ e ^ 10 := pow_le_pow_left h0k hk' 10
  have hk11 : (k : ℤ) ^ 11 ≤ e ^ 11 := pow_le_pow_left h0k hk' 11
  have hk12 : (k : ℤ) ^ 12 ≤ e ^ 12 := pow_le_pow_left h0k hk' 12
  have hk13 : (k : ℤ) ^ 13 ≤ e ^ 13 := pow_le_pow_left h0k hk' 13
  have hexp :
      -((13 : ℤ) * (7 * e + k) * e ^ 12
        - 286 * (7 * e + k) ^ 3 * e ^ 10
        + 1287 * (7 * e + k) ^ 5 * e ^ 8
        - 1716 * (7 * e + k) ^ 7 * e ^ 6
        + 715 * (7 * e + k) ^ 9 * e ^ 4
        - 78 * (7 * e + k) ^ 11 * e ^ 2
        + (7 * e + k) ^ 13)
      - ((7 * e + k : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2
      = (29881313728 : ℤ) * e ^ 13
        + 26728326976 * e ^ 12 * k
        + (-1711260096) * e ^ 11 * k ^ 2
        + (-13517357568) * e ^ 10 * k ^ 3
        + (-9148419280) * e ^ 9 * k ^ 4
        + (-3394241136) * e ^ 8 * k ^ 5
        + (-828059232) * e ^ 7 * k ^ 6
        + (-141343488) * e ^ 6 * k ^ 7
        + (-17261244) * e ^ 5 * k ^ 8
        + (-1507220) * e ^ 4 * k ^ 9
        + (-92092) * e ^ 3 * k ^ 10
        + (-3744) * e ^ 2 * k ^ 11
        + (-91) * e * k ^ 12
        + (-1) * k ^ 13
        + (-2500) * e ^ 4
        + (-1400) * e ^ 3 * k
        + (-296) * e ^ 2 * k ^ 2
        + (-28) * e * k ^ 3
        + (-1) * k ^ 4
        + 1000 * e ^ 2
        + 280 * e * k
        + 20 * k ^ 2
        + (-100) := by
    ring
  have hgt : (0 : ℤ) <
      -((13 : ℤ) * (7 * e + k) * e ^ 12
        - 286 * (7 * e + k) ^ 3 * e ^ 10
        + 1287 * (7 * e + k) ^ 5 * e ^ 8
        - 1716 * (7 * e + k) ^ 7 * e ^ 6
        + 715 * (7 * e + k) ^ 9 * e ^ 4
        - 78 * (7 * e + k) ^ 11 * e ^ 2
        + (7 * e + k) ^ 13)
      - ((7 * e + k : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
    rw [hexp]
    nlinarith [h1, h0e, h0k, hk', hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9, hk10, hk11, hk12, hk13,
      pow_nonneg h0e 13, pow_nonneg h0e 12, pow_nonneg h0e 11, pow_nonneg h0e 10,
      pow_nonneg h0e 9, pow_nonneg h0e 8, pow_nonneg h0e 7, pow_nonneg h0e 6,
      pow_nonneg h0e 5, pow_nonneg h0e 4, pow_nonneg h0e 3, pow_nonneg h0e 2,
      pow_nonneg h0k 2, pow_nonneg h0k 3, pow_nonneg h0k 4, pow_nonneg h0k 5,
      pow_nonneg h0k 6, pow_nonneg h0k 7, pow_nonneg h0k 8, pow_nonneg h0k 9,
      pow_nonneg h0k 10, pow_nonneg h0k 11, pow_nonneg h0k 12, pow_nonneg h0k 13]
  linarith [hgt]


theorem re13_gt_of_seven (d e : ℕ) (he : 1 ≤ e) (h7 : 7 * e ≤ d) (h8 : d ≤ 8 * e) :
    -((13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13)
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set k := d - 7 * e
  have hk : d = 7 * e + k := (Nat.add_sub_of_le h7).symm
  have hk2 : k ≤ e := by simp only [k]; omega
  rw [hk]
  exact re13_neg_gt_seven_k e k he hk2

lemma re13_pos_gt_nine_k (e k : ℕ) (hbase : 1 ≤ e) (hk_le : k ≤ e) :
    ((13 : ℤ) * (9 * e + k) * (e) ^ 12
        - 286 * (9 * e + k) ^ 3 * (e) ^ 10
        + 1287 * (9 * e + k) ^ 5 * (e) ^ 8
        - 1716 * (9 * e + k) ^ 7 * (e) ^ 6
        + 715 * (9 * e + k) ^ 9 * (e) ^ 4
        - 78 * (9 * e + k) ^ 11 * (e) ^ 2
        + (9 * e + k) ^ 13)
    > ((9 * e + k) ^ 2 + (e) ^ 2 - 10) ^ 2 := by
  have h1 : (1 : ℤ) ≤ e := by exact_mod_cast hbase
  have h0b : (0 : ℤ) ≤ e := le_trans (by norm_num) h1
  have h0k : (0 : ℤ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hk' : (k : ℤ) ≤ e := by exact_mod_cast hk_le
  have hk2 : (k : ℤ) ^ 2 ≤ e ^ 2 := pow_le_pow_left h0k hk' 2
  have hk3 : (k : ℤ) ^ 3 ≤ e ^ 3 := pow_le_pow_left h0k hk' 3
  have hk4 : (k : ℤ) ^ 4 ≤ e ^ 4 := pow_le_pow_left h0k hk' 4
  have hk5 : (k : ℤ) ^ 5 ≤ e ^ 5 := pow_le_pow_left h0k hk' 5
  have hk6 : (k : ℤ) ^ 6 ≤ e ^ 6 := pow_le_pow_left h0k hk' 6
  have hk7 : (k : ℤ) ^ 7 ≤ e ^ 7 := pow_le_pow_left h0k hk' 7
  have hk8 : (k : ℤ) ^ 8 ≤ e ^ 8 := pow_le_pow_left h0k hk' 8
  have hk9 : (k : ℤ) ^ 9 ≤ e ^ 9 := pow_le_pow_left h0k hk' 9
  have hk10 : (k : ℤ) ^ 10 ≤ e ^ 10 := pow_le_pow_left h0k hk' 10
  have hk11 : (k : ℤ) ^ 11 ≤ e ^ 11 := pow_le_pow_left h0k hk' 11
  have hk12 : (k : ℤ) ^ 12 ≤ e ^ 12 := pow_le_pow_left h0k hk' 12
  have hk13 : (k : ℤ) ^ 13 ≤ e ^ 13 := pow_le_pow_left h0k hk' 13
  have hexp :
      ((13 : ℤ) * (9 * e + k) * (e) ^ 12
        - 286 * (9 * e + k) ^ 3 * (e) ^ 10
        + 1287 * (9 * e + k) ^ 5 * (e) ^ 8
        - 1716 * (9 * e + k) ^ 7 * (e) ^ 6
        + 715 * (9 * e + k) ^ 9 * (e) ^ 4
        - 78 * (9 * e + k) ^ 11 * (e) ^ 2
        + (9 * e + k) ^ 13)
      - ((9 * e + k) ^ 2 + (e) ^ 2 - 10) ^ 2
      = 363017041344 * e ^ 13
        + 950587089088 * e ^ 12 * k
        + 906683858496 * e ^ 11 * k ^ 2
        + 474734374400 * e ^ 10 * k ^ 3
        + 159168026160 * e ^ 9 * k ^ 4
        + 36838284912 * e ^ 8 * k ^ 5
        + 6123360672 * e ^ 7 * k ^ 6
        + 745155840 * e ^ 6 * k ^ 7
        + 66671748 * e ^ 5 * k ^ 8
        + 4344340 * e ^ 4 * k ^ 9
        + 200772 * e ^ 3 * k ^ 10
        + 6240 * e ^ 2 * k ^ 11
        + 117 * e * k ^ 12
        + 1 * k ^ 13
        + (-6724 : ℤ) * e ^ 4
        + (-2952 : ℤ) * e ^ 3 * k
        + (-488 : ℤ) * e ^ 2 * k ^ 2
        + (-36 : ℤ) * e * k ^ 3
        + (-1 : ℤ) * k ^ 4
        + 1640 * e ^ 2
        + 360 * e * k
        + 20 * k ^ 2
        + (-100 : ℤ) := by
    ring
  have hgt : (0 : ℤ) <
      ((13 : ℤ) * (9 * e + k) * (e) ^ 12
        - 286 * (9 * e + k) ^ 3 * (e) ^ 10
        + 1287 * (9 * e + k) ^ 5 * (e) ^ 8
        - 1716 * (9 * e + k) ^ 7 * (e) ^ 6
        + 715 * (9 * e + k) ^ 9 * (e) ^ 4
        - 78 * (9 * e + k) ^ 11 * (e) ^ 2
        + (9 * e + k) ^ 13)
      - ((9 * e + k) ^ 2 + (e) ^ 2 - 10) ^ 2 := by
    rw [hexp]
    nlinarith [h1, h0b, h0k, hk', hk2, hk3, hk4, hk5, hk6, hk7, hk8, hk9, hk10, hk11, hk12, hk13,
      pow_nonneg h0b 2, pow_nonneg h0b 3, pow_nonneg h0b 4, pow_nonneg h0b 5, pow_nonneg h0b 6, pow_nonneg h0b 7, pow_nonneg h0b 8, pow_nonneg h0b 9, pow_nonneg h0b 10, pow_nonneg h0b 11, pow_nonneg h0b 12, pow_nonneg h0b 13, pow_nonneg h0k 2, pow_nonneg h0k 3, pow_nonneg h0k 4, pow_nonneg h0k 5, pow_nonneg h0k 6, pow_nonneg h0k 7, pow_nonneg h0k 8, pow_nonneg h0k 9, pow_nonneg h0k 10, pow_nonneg h0k 11, pow_nonneg h0k 12, pow_nonneg h0k 13]
  linarith [hgt]


theorem re13_gt_of_nine (d e : ℕ) (he : 1 ≤ e) (h9 : 9 * e ≤ d) (h10 : d ≤ 10 * e) :
    (13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set k := d - 9 * e
  have hk : d = 9 * e + k := (Nat.add_sub_of_le h9).symm
  have hk2 : k ≤ e := by simp only [k]; omega
  rw [hk]
  exact re13_pos_gt_nine_k e k he hk2

lemma re13_neg_gt_eight_k (e k : ℕ) (hbase : 1 ≤ e) (hk5 : 5 * k ≤ e) :
    -((13 : ℤ) * (8 * e + k) * ((e : ℤ)) ^ 12
        - 286 * (8 * e + k) ^ 3 * ((e : ℤ)) ^ 10
        + 1287 * (8 * e + k) ^ 5 * ((e : ℤ)) ^ 8
        - 1716 * (8 * e + k) ^ 7 * ((e : ℤ)) ^ 6
        + 715 * (8 * e + k) ^ 9 * ((e : ℤ)) ^ 4
        - 78 * (8 * e + k) ^ 11 * ((e : ℤ)) ^ 2
        + (8 * e + k) ^ 13)
    > ((8 * e + k) ^ 2 + ((e : ℤ)) ^ 2 - 10) ^ 2 := by
  have h1 : (1 : ℤ) ≤ e := by exact_mod_cast hbase
  have h0b : (0 : ℤ) ≤ e := le_trans (by norm_num) h1
  have h0k : (0 : ℤ) ≤ k := by exact_mod_cast (Nat.zero_le k)
  have hk5' : (5 : ℤ) * k ≤ e := by exact_mod_cast hk5
  have hexp :
      -((13 : ℤ) * (8 * e + k) * ((e : ℤ)) ^ 12
        - 286 * (8 * e + k) ^ 3 * ((e : ℤ)) ^ 10
        + 1287 * (8 * e + k) ^ 5 * ((e : ℤ)) ^ 8
        - 1716 * (8 * e + k) ^ 7 * ((e : ℤ)) ^ 6
        + 715 * (8 * e + k) ^ 9 * ((e : ℤ)) ^ 4
        - 78 * (8 * e + k) ^ 11 * ((e : ℤ)) ^ 2
        + (8 * e + k) ^ 13)
      - ((8 * e + k) ^ 2 + ((e : ℤ)) ^ 2 - 10) ^ 2
      = 27850095512 * e ^ 13
        + (-76921526669 : ℤ) * e ^ 12 * k
        + (-147027292464 : ℤ) * e ^ 11 * k ^ 2
        + (-106666578018 : ℤ) * e ^ 10 * k ^ 3
        + (-44906352920 : ℤ) * e ^ 9 * k ^ 4
        + (-12512359431 : ℤ) * e ^ 8 * k ^ 5
        + (-2448539808 : ℤ) * e ^ 7 * k ^ 6
        + (-346053708 : ℤ) * e ^ 6 * k ^ 7
        + (-35634456 : ℤ) * e ^ 5 * k ^ 8
        + (-2654795 : ℤ) * e ^ 4 * k ^ 9
        + (-139568 : ℤ) * e ^ 3 * k ^ 10
        + (-4914 : ℤ) * e ^ 2 * k ^ 11
        + (-104 : ℤ) * e * k ^ 12
        + (-1 : ℤ) * k ^ 13
        + (-4225 : ℤ) * e ^ 4
        + (-2080 : ℤ) * e ^ 3 * k
        + (-386 : ℤ) * e ^ 2 * k ^ 2
        + (-32 : ℤ) * e * k ^ 3
        + (-1 : ℤ) * k ^ 4
        + 1300 * e ^ 2
        + 320 * e * k
        + 20 * k ^ 2
        + (-100 : ℤ) := by
    ring
  have hgt : (0 : ℤ) <
      -((13 : ℤ) * (8 * e + k) * ((e : ℤ)) ^ 12
        - 286 * (8 * e + k) ^ 3 * ((e : ℤ)) ^ 10
        + 1287 * (8 * e + k) ^ 5 * ((e : ℤ)) ^ 8
        - 1716 * (8 * e + k) ^ 7 * ((e : ℤ)) ^ 6
        + 715 * (8 * e + k) ^ 9 * ((e : ℤ)) ^ 4
        - 78 * (8 * e + k) ^ 11 * ((e : ℤ)) ^ 2
        + (8 * e + k) ^ 13)
      - ((8 * e + k) ^ 2 + ((e : ℤ)) ^ 2 - 10) ^ 2 := by
    rw [hexp]
    nlinarith [h1, h0b, h0k, hk5',
      pow_nonneg h0b 2, pow_nonneg h0b 3, pow_nonneg h0b 4, pow_nonneg h0b 5, pow_nonneg h0b 6, pow_nonneg h0b 7, pow_nonneg h0b 8, pow_nonneg h0b 9, pow_nonneg h0b 10, pow_nonneg h0b 11, pow_nonneg h0b 12, pow_nonneg h0b 13, pow_nonneg h0k 2, pow_nonneg h0k 3, pow_nonneg h0k 4, pow_nonneg h0k 5, pow_nonneg h0k 6, pow_nonneg h0k 7, pow_nonneg h0k 8, pow_nonneg h0k 9, pow_nonneg h0k 10, pow_nonneg h0k 11, pow_nonneg h0k 12, pow_nonneg h0k 13]
  linarith [hgt]


theorem re13_gt_of_eight_collar (d e : ℕ) (he : 1 ≤ e)
    (h8 : 8 * e ≤ d) (hk5 : 5 * (d - 8 * e) ≤ e) :
    -((13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13)
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set k := d - 8 * e
  have hk : d = 8 * e + k := (Nat.add_sub_of_le h8).symm
  have hk5' : 5 * k ≤ e := by simp only [k]; exact hk5
  rw [hk]
  exact re13_neg_gt_eight_k e k he hk5'

/-! ## Farey leftover `3/4 ≤ e/d ≤ 1`. -/
lemma re13_neg_gt_three_four (a b : ℕ) (hsum : 1 ≤ a + b)
    (hN : 10 < (4 * a + b) * (4 * a + b) + (3 * a + b) * (3 * a + b)) :
    -((13 : ℤ) * (4 * a + 1 * b) * (3 * a + 1 * b) ^ 12
        - 286 * (4 * a + 1 * b) ^ 3 * (3 * a + 1 * b) ^ 10
        + 1287 * (4 * a + 1 * b) ^ 5 * (3 * a + 1 * b) ^ 8
        - 1716 * (4 * a + 1 * b) ^ 7 * (3 * a + 1 * b) ^ 6
        + 715 * (4 * a + 1 * b) ^ 9 * (3 * a + 1 * b) ^ 4
        - 78 * (4 * a + 1 * b) ^ 11 * (3 * a + 1 * b) ^ 2
        + (4 * a + 1 * b) ^ 13)
    > ((4 * a + 1 * b) ^ 2 + (3 * a + 1 * b) ^ 2 - 10) ^ 2 := by
  have h0a : (0 : ℤ) ≤ a := by exact_mod_cast (Nat.zero_le a)
  have h0b : (0 : ℤ) ≤ b := by exact_mod_cast (Nat.zero_le b)
  have h1 : (1 : ℤ) ≤ a + b := by exact_mod_cast hsum
  have hexp :
      -((13 : ℤ) * (4 * a + 1 * b) * (3 * a + 1 * b) ^ 12
        - 286 * (4 * a + 1 * b) ^ 3 * (3 * a + 1 * b) ^ 10
        + 1287 * (4 * a + 1 * b) ^ 5 * (3 * a + 1 * b) ^ 8
        - 1716 * (4 * a + 1 * b) ^ 7 * (3 * a + 1 * b) ^ 6
        + 715 * (4 * a + 1 * b) ^ 9 * (3 * a + 1 * b) ^ 4
        - 78 * (4 * a + 1 * b) ^ 11 * (3 * a + 1 * b) ^ 2
        + (4 * a + 1 * b) ^ 13)
      - ((4 * a + 1 * b) ^ 2 + (3 * a + 1 * b) ^ 2 - 10) ^ 2
      = 597551756 * a ^ 13
        + 2728600979 * a ^ 12 * b
        + 5439376332 * a ^ 11 * b ^ 2
        + 6366515012 * a ^ 10 * b ^ 3
        + 4924245040 * a ^ 9 * b ^ 4
        + 2671693596 * a ^ 8 * b ^ 5
        + 1049409504 * a ^ 7 * b ^ 6
        + 302688672 * a ^ 6 * b ^ 7
        + 64164672 * a ^ 5 * b ^ 8
        + 9872720 * a ^ 4 * b ^ 9
        + 1070784 * a ^ 3 * b ^ 10
        + 77376 * a ^ 2 * b ^ 11
        + 3328 * a * b ^ 12
        + 64 * b ^ 13
        + (-625 : ℤ) * a ^ 4
        + (-700 : ℤ) * a ^ 3 * b
        + (-296 : ℤ) * a ^ 2 * b ^ 2
        + (-56 : ℤ) * a * b ^ 3
        + (-4 : ℤ) * b ^ 4
        + 500 * a ^ 2
        + 280 * a * b
        + 40 * b ^ 2
        + (-100 : ℤ) := by
    ring
  have hgt : (0 : ℤ) <
      -((13 : ℤ) * (4 * a + 1 * b) * (3 * a + 1 * b) ^ 12
        - 286 * (4 * a + 1 * b) ^ 3 * (3 * a + 1 * b) ^ 10
        + 1287 * (4 * a + 1 * b) ^ 5 * (3 * a + 1 * b) ^ 8
        - 1716 * (4 * a + 1 * b) ^ 7 * (3 * a + 1 * b) ^ 6
        + 715 * (4 * a + 1 * b) ^ 9 * (3 * a + 1 * b) ^ 4
        - 78 * (4 * a + 1 * b) ^ 11 * (3 * a + 1 * b) ^ 2
        + (4 * a + 1 * b) ^ 13)
      - ((4 * a + 1 * b) ^ 2 + (3 * a + 1 * b) ^ 2 - 10) ^ 2 := by
    rw [hexp]
    have ha0 : a = 0 ∨ 1 ≤ a := by omega
    have hb0 : b = 0 ∨ 1 ≤ b := by omega
    have hrest : (0 : ℤ) ≤
        2728600979 * a ^ 12 * b
        + 5439376332 * a ^ 11 * b ^ 2
        + 6366515012 * a ^ 10 * b ^ 3
        + 4924245040 * a ^ 9 * b ^ 4
        + 2671693596 * a ^ 8 * b ^ 5
        + 1049409504 * a ^ 7 * b ^ 6
        + 302688672 * a ^ 6 * b ^ 7
        + 64164672 * a ^ 5 * b ^ 8
        + 9872720 * a ^ 4 * b ^ 9
        + 1070784 * a ^ 3 * b ^ 10
        + 77376 * a ^ 2 * b ^ 11
        + 3328 * a * b ^ 12
        + 500 * a ^ 2
        + 280 * a * b
        + 40 * b ^ 2 := by
      nlinarith [h0a, h0b, pow_nonneg h0a 2, pow_nonneg h0a 3, pow_nonneg h0a 4,
        pow_nonneg h0a 5, pow_nonneg h0a 6, pow_nonneg h0a 7, pow_nonneg h0a 8,
        pow_nonneg h0a 9, pow_nonneg h0a 10, pow_nonneg h0a 11, pow_nonneg h0a 12,
        pow_nonneg h0b 2, pow_nonneg h0b 3, pow_nonneg h0b 4, pow_nonneg h0b 5,
        pow_nonneg h0b 6, pow_nonneg h0b 7, pow_nonneg h0b 8, pow_nonneg h0b 9,
        pow_nonneg h0b 10, pow_nonneg h0b 11, pow_nonneg h0b 12]
    have hA : (0 : ℤ) <
        597551756 * a ^ 13 + 64 * b ^ 13
          - 625 * a ^ 4 - 700 * a ^ 3 * b - 296 * a ^ 2 * b ^ 2
          - 56 * a * b ^ 3 - 4 * b ^ 4 - 100 := by
      rcases ha0 with ha0 | ha1
      · subst ha0
        have hb1 : 1 ≤ b := by omega
        have hb1z : (1 : ℤ) ≤ b := by exact_mod_cast hb1
        have hb3 : 3 ≤ b := by
          have hbb : 10 < b * b + b * b := by simpa using hN
          have hle2 : ¬ b ≤ 2 := by
            intro hle
            have : b * b ≤ 4 := Nat.mul_le_mul hle hle
            omega
          omega
        have hb3z : (3 : ℤ) ≤ b := by exact_mod_cast hb3
        have hb13 : (1 : ℤ) ≤ b ^ 13 := one_le_pow_of_one_le hb1z 13
        have hb4 : (1 : ℤ) ≤ b ^ 4 := one_le_pow_of_one_le hb1z 4
        have hb13min : (1594323 : ℤ) ≤ b ^ 13 := by
          have h3 : (3 : ℤ) ^ 13 ≤ b ^ 13 :=
            pow_le_pow_left (by norm_num) hb3z 13
          have hval : (3 : ℤ) ^ 13 = 1594323 := by norm_num
          rwa [hval] at h3
        have hb4bound : (b : ℤ) ^ 4 ≤ b ^ 13 :=
          pow_le_pow_right hb1z (by decide : (4 : ℕ) ≤ 13)
        have hmain : (0 : ℤ) < 64 * b ^ 13 - 4 * b ^ 4 - 100 := by
          have hle : (4 : ℤ) * b ^ 4 ≤ 4 * b ^ 13 :=
            mul_le_mul_of_nonneg_left hb4bound (by norm_num)
          have h60 : (64 : ℤ) * b ^ 13 - 4 * b ^ 4 - 100 ≥ 60 * b ^ 13 - 100 := by
            linarith
          have hmin : (60 : ℤ) * b ^ 13 - 100 ≥ 60 * 1594323 - 100 := by
            nlinarith [hb13min]
          linarith
        have heq : (597551756 : ℤ) * (0 : ℕ) ^ 13 + 64 * b ^ 13
            - 625 * (0 : ℕ) ^ 4 - 700 * (0 : ℕ) ^ 3 * b
            - 296 * (0 : ℕ) ^ 2 * b ^ 2 - 56 * (0 : ℕ) * b ^ 3
            - 4 * b ^ 4 - 100
            = 64 * b ^ 13 - 4 * b ^ 4 - 100 := by ring
        simpa [heq] using hmain
      · rcases hb0 with hb0 | hb1
        · subst hb0
          have ha1z : (1 : ℤ) ≤ a := by exact_mod_cast ha1
          have ha13 : (1 : ℤ) ≤ a ^ 13 := one_le_pow_of_one_le ha1z 13
          have ha4 : (1 : ℤ) ≤ a ^ 4 := one_le_pow_of_one_le ha1z 4
          have hapow : (a : ℤ) ^ 4 ≤ a ^ 13 :=
            pow_le_pow_right ha1z (by decide : (4 : ℕ) ≤ 13)
          have hpos := pow13_sub_pow4_const_pos a 597551756 625 100 ha1z
            (by norm_num) (by norm_num) (by norm_num)
          have heq : (597551756 : ℤ) * a ^ 13 + 64 * (0 : ℕ) ^ 13
              - 625 * a ^ 4 - 700 * a ^ 3 * (0 : ℕ)
              - 296 * a ^ 2 * (0 : ℕ) ^ 2 - 56 * a * (0 : ℕ) ^ 3
              - 4 * (0 : ℕ) ^ 4 - 100
              = 597551756 * a ^ 13 - 625 * a ^ 4 - 100 := by ring
          simpa [heq] using hpos
        · have ha1z : (1 : ℤ) ≤ a := by exact_mod_cast ha1
          have hb1z : (1 : ℤ) ≤ b := by exact_mod_cast hb1
          have ha13 : (1 : ℤ) ≤ a ^ 13 := one_le_pow_of_one_le ha1z 13
          have hb13 : (1 : ℤ) ≤ b ^ 13 := one_le_pow_of_one_le hb1z 13
          have ha4 : (1 : ℤ) ≤ a ^ 4 := one_le_pow_of_one_le ha1z 4
          have hb4 : (1 : ℤ) ≤ b ^ 4 := one_le_pow_of_one_le hb1z 4
          have hapow : (a : ℤ) ^ 4 ≤ a ^ 13 :=
            pow_le_pow_right ha1z (by decide : (4 : ℕ) ≤ 13)
          have hb12 : b = 1 ∨ 2 ≤ b := by omega
          rcases hb12 with hb1eq | hb2
          · subst hb1eq
            have h3le : (a : ℤ) ^ 3 ≤ a ^ 13 :=
              pow_le_pow_right ha1z (by decide : (3 : ℕ) ≤ 13)
            have h2le : (a : ℤ) ^ 2 ≤ a ^ 13 :=
              pow_le_pow_right ha1z (by decide : (2 : ℕ) ≤ 13)
            have h1le : (a : ℤ) ≤ a ^ 13 := by
              simpa using pow_le_pow_right ha1z (by decide : (1 : ℕ) ≤ 13)
            have h4 : (625 : ℤ) * a ^ 4 ≤ 625 * a ^ 13 :=
              mul_le_mul_of_nonneg_left hapow (by norm_num)
            have h3 : (700 : ℤ) * a ^ 3 ≤ 700 * a ^ 13 :=
              mul_le_mul_of_nonneg_left h3le (by norm_num)
            have h2 : (296 : ℤ) * a ^ 2 ≤ 296 * a ^ 13 :=
              mul_le_mul_of_nonneg_left h2le (by norm_num)
            have h1 : (56 : ℤ) * a ≤ 56 * a ^ 13 :=
              mul_le_mul_of_nonneg_left h1le (by norm_num)
            norm_num
            linarith [h4, h3, h2, h1, ha13]
          · have hb2z : (2 : ℤ) ≤ b := by exact_mod_cast hb2
            have h1b : (1 : ℤ) ≤ b := le_trans (by norm_num) hb2z
            have hpow : (b : ℤ) ^ 4 ≤ b ^ 13 :=
              pow_le_pow_right h1b (by decide : (4 : ℕ) ≤ 13)
            have hb9 : (512 : ℤ) ≤ b ^ 9 := by
              have h2 : (2 : ℤ) ^ 9 ≤ b ^ 9 :=
                pow_le_pow_left (by norm_num) hb2z 9
              have h512 : (2 : ℤ) ^ 9 = 512 := by norm_num
              rwa [h512] at h2
            have hsplit : (b : ℤ) ^ 13 = b ^ 4 * b ^ 9 := by ring
            have hbig : (369 : ℤ) * b ^ 4 ≤ 64 * b ^ 13 := by
              have : (369 : ℤ) * b ^ 4 ≤ 512 * b ^ 4 := by
                nlinarith [pow_nonneg h0b 4]
              nlinarith [this, hb9, hsplit, pow_nonneg h0b 4]
            have h3le : (a : ℤ) ^ 3 ≤ a ^ 13 :=
              pow_le_pow_right ha1z (by decide : (3 : ℕ) ≤ 13)
            have h2le : (a : ℤ) ^ 2 ≤ a ^ 13 :=
              pow_le_pow_right ha1z (by decide : (2 : ℕ) ≤ 13)
            have h1le : (a : ℤ) ≤ a ^ 13 := by
              simpa using pow_le_pow_right ha1z (by decide : (1 : ℕ) ≤ 13)
            have hb2le : (b : ℤ) ≤ b ^ 13 := by
              simpa using pow_le_pow_right h1b (by decide : (1 : ℕ) ≤ 13)
            have hb3le : (b : ℤ) ^ 3 ≤ b ^ 13 :=
              pow_le_pow_right h1b (by decide : (3 : ℕ) ≤ 13)
            have hb2sq : (b : ℤ) ^ 2 ≤ b ^ 13 :=
              pow_le_pow_right h1b (by decide : (2 : ℕ) ≤ 13)
            -- Bound mixed monomials by a^13 and b^13.
            have m1 : (700 : ℤ) * a ^ 3 * b ≤ 350 * a ^ 13 + 350 * b ^ 2 := by
              have h2 : (2 : ℤ) * (a ^ 3) * b ≤ (a ^ 3) ^ 2 + b ^ 2 :=
                two_mul_le_sq_add (a ^ 3) b
              have : (2 : ℤ) * a ^ 3 * b ≤ a ^ 6 + b ^ 2 := by
                convert h2 using 1 <;> ring
              have ha6 : (a : ℤ) ^ 6 ≤ a ^ 13 :=
                pow_le_pow_right ha1z (by decide : (6 : ℕ) ≤ 13)
              nlinarith [this, ha6]
            have m2 : (296 : ℤ) * a ^ 2 * b ^ 2 ≤ 148 * a ^ 13 + 148 * b ^ 4 := by
              have h2 : (2 : ℤ) * (a ^ 2) * (b ^ 2) ≤ (a ^ 2) ^ 2 + (b ^ 2) ^ 2 :=
                two_mul_le_sq_add (a ^ 2) (b ^ 2)
              have : (2 : ℤ) * a ^ 2 * b ^ 2 ≤ a ^ 4 + b ^ 4 := by
                convert h2 using 1 <;> ring
              nlinarith [this, hapow]
            have m3 : (56 : ℤ) * a * b ^ 3 ≤ 28 * a ^ 13 + 28 * b ^ 6 := by
              have h2 : (2 : ℤ) * a * (b ^ 3) ≤ a ^ 2 + (b ^ 3) ^ 2 :=
                two_mul_le_sq_add a (b ^ 3)
              have : (2 : ℤ) * a * b ^ 3 ≤ a ^ 2 + b ^ 6 := by
                convert h2 using 1 <;> ring
              have ha2 : (a : ℤ) ^ 2 ≤ a ^ 13 :=
                pow_le_pow_right ha1z (by decide : (2 : ℕ) ≤ 13)
              nlinarith [this, ha2]
            have m0 : (625 : ℤ) * a ^ 4 ≤ 625 * a ^ 13 :=
              mul_le_mul_of_nonneg_left hapow (by norm_num)
            have hb11 : (2048 : ℤ) ≤ b ^ 11 := by
              have h2 : (2 : ℤ) ^ 11 ≤ b ^ 11 :=
                pow_le_pow_left (by norm_num) hb2z 11
              have hval : (2 : ℤ) ^ 11 = 2048 := by norm_num
              rwa [hval] at h2
            have hb9 : (512 : ℤ) ≤ b ^ 9 := by
              have h2 : (2 : ℤ) ^ 9 ≤ b ^ 9 :=
                pow_le_pow_left (by norm_num) hb2z 9
              have hval : (2 : ℤ) ^ 9 = 512 := by norm_num
              rwa [hval] at h2
            have hb7 : (128 : ℤ) ≤ b ^ 7 := by
              have h2 : (2 : ℤ) ^ 7 ≤ b ^ 7 :=
                pow_le_pow_left (by norm_num) hb2z 7
              have hval : (2 : ℤ) ^ 7 = 128 := by norm_num
              rwa [hval] at h2
            have b2bound : (350 : ℤ) * b ^ 2 ≤ b ^ 13 := by
              have hsplit : (b : ℤ) ^ 13 = b ^ 2 * b ^ 11 := by ring
              have h350 : (350 : ℤ) * b ^ 2 ≤ 2048 * b ^ 2 :=
                mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg h0b 2)
              have h2048 : (2048 : ℤ) * b ^ 2 ≤ b ^ 11 * b ^ 2 :=
                mul_le_mul_of_nonneg_right hb11 (pow_nonneg h0b 2)
              calc (350 : ℤ) * b ^ 2
                  ≤ 2048 * b ^ 2 := h350
                _ ≤ b ^ 11 * b ^ 2 := h2048
                _ = b ^ 13 := by rw [hsplit, mul_comm]
            have b4bound : (152 : ℤ) * b ^ 4 ≤ b ^ 13 := by
              have hsplit : (b : ℤ) ^ 13 = b ^ 4 * b ^ 9 := by ring
              have h152 : (152 : ℤ) * b ^ 4 ≤ 512 * b ^ 4 :=
                mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg h0b 4)
              have h512 : (512 : ℤ) * b ^ 4 ≤ b ^ 9 * b ^ 4 :=
                mul_le_mul_of_nonneg_right hb9 (pow_nonneg h0b 4)
              calc (152 : ℤ) * b ^ 4
                  ≤ 512 * b ^ 4 := h152
                _ ≤ b ^ 9 * b ^ 4 := h512
                _ = b ^ 13 := by rw [hsplit, mul_comm]
            have b6bound : (28 : ℤ) * b ^ 6 ≤ b ^ 13 := by
              have hsplit : (b : ℤ) ^ 13 = b ^ 6 * b ^ 7 := by ring
              have h28 : (28 : ℤ) * b ^ 6 ≤ 128 * b ^ 6 :=
                mul_le_mul_of_nonneg_right (by norm_num) (pow_nonneg h0b 6)
              have h128 : (128 : ℤ) * b ^ 6 ≤ b ^ 7 * b ^ 6 :=
                mul_le_mul_of_nonneg_right hb7 (pow_nonneg h0b 6)
              calc (28 : ℤ) * b ^ 6
                  ≤ 128 * b ^ 6 := h28
                _ ≤ b ^ 7 * b ^ 6 := h128
                _ = b ^ 13 := by rw [hsplit, mul_comm]
            have hlower :
                (597551756 : ℤ) * a ^ 13 + 64 * b ^ 13
                  - 625 * a ^ 4 - 700 * a ^ 3 * b - 296 * a ^ 2 * b ^ 2
                  - 56 * a * b ^ 3 - 4 * b ^ 4 - 100
                ≥ 597550605 * a ^ 13 + 61 * b ^ 13 - 100 := by
              have hm :
                  (625 : ℤ) * a ^ 4 + 700 * a ^ 3 * b + 296 * a ^ 2 * b ^ 2
                    + 56 * a * b ^ 3 + 4 * b ^ 4
                  ≤ 1151 * a ^ 13 + 3 * b ^ 13 := by
                linarith [m0, m1, m2, m3, b2bound, b4bound, b6bound]
              linarith [hm, ha13, hb13]
            have hmin : (597550605 : ℤ) * a ^ 13 + 61 * b ^ 13 - 100 ≥
                597550605 + 61 * 8192 - 100 := by
              have hb13min : (8192 : ℤ) ≤ b ^ 13 := by
                have h2 : (2 : ℤ) ^ 13 ≤ b ^ 13 :=
                  pow_le_pow_left (by norm_num) hb2z 13
                have hval : (2 : ℤ) ^ 13 = 8192 := by norm_num
                rwa [hval] at h2
              nlinarith [ha13, hb13min]
            linarith [hlower, hmin]
    linarith [hA, hrest]
  linarith [hgt]


theorem re13_gt_of_three_four (d e : ℕ) (he : 1 ≤ e)
    (h34 : 3 * d ≤ 4 * e) (hle : e ≤ d) (hN : 10 < d * d + e * e) :
    -((13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13)
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set a := d - e
  set b := 4 * e - 3 * d
  have ha : 0 ≤ (a : ℤ) := by exact_mod_cast (Nat.zero_le a)
  have hb' : 3 * d ≤ 4 * e := h34
  have hk : d = 4 * a + b ∧ e = 3 * a + b := by
    simp only [a, b]
    constructor <;> omega
  have hsum : 1 ≤ a + b := by
    have : 1 ≤ e := he
    omega
  rw [hk.1, hk.2]
  have hN' : 10 < (4 * a + b) * (4 * a + b) + (3 * a + b) * (3 * a + b) := by
    simpa [hk.1, hk.2] using hN
  simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    re13_neg_gt_three_four a b hsum hN'

/-- Root-free leftover `t ∈ [1/2, 2/3]`. All degree-13 coefficients
    of the Farey form are positive. -/
lemma re13_pos_gt_half_two_thirds (a b : ℕ) (hsum : 1 ≤ a + b)
    (hN : 10 < (2 * a + 3 * b) * (2 * a + 3 * b) + (a + 2 * b) * (a + 2 * b)) :
    (13 : ℤ) * (2 * a + 3 * b) * (a + 2 * b) ^ 12
        - 286 * (2 * a + 3 * b) ^ 3 * (a + 2 * b) ^ 10
        + 1287 * (2 * a + 3 * b) ^ 5 * (a + 2 * b) ^ 8
        - 1716 * (2 * a + 3 * b) ^ 7 * (a + 2 * b) ^ 6
        + 715 * (2 * a + 3 * b) ^ 9 * (a + 2 * b) ^ 4
        - 78 * (2 * a + 3 * b) ^ 11 * (a + 2 * b) ^ 2
        + (2 * a + 3 * b) ^ 13
    > ((2 * a + 3 * b) ^ 2 + (a + 2 * b) ^ 2 - 10) ^ 2 := by
  have h0a : (0 : ℤ) ≤ a := by exact_mod_cast (Nat.zero_le a)
  have h0b : (0 : ℤ) ≤ b := by exact_mod_cast (Nat.zero_le b)
  have hexp :
      (13 : ℤ) * (2 * a + 3 * b) * (a + 2 * b) ^ 12
        - 286 * (2 * a + 3 * b) ^ 3 * (a + 2 * b) ^ 10
        + 1287 * (2 * a + 3 * b) ^ 5 * (a + 2 * b) ^ 8
        - 1716 * (2 * a + 3 * b) ^ 7 * (a + 2 * b) ^ 6
        + 715 * (2 * a + 3 * b) ^ 9 * (a + 2 * b) ^ 4
        - 78 * (2 * a + 3 * b) ^ 11 * (a + 2 * b) ^ 2
        + (2 * a + 3 * b) ^ 13
      - ((2 * a + 3 * b) ^ 2 + (a + 2 * b) ^ 2 - 10) ^ 2
      = 33802 * a ^ 13
        + 726063 * a ^ 12 * b
        + 7085364 * a ^ 11 * b ^ 2
        + 41604134 * a ^ 10 * b ^ 3
        + 163965230 * a ^ 9 * b ^ 4
        + 457671357 * a ^ 8 * b ^ 5
        + 929588088 * a ^ 7 * b ^ 6
        + 1388087844 * a ^ 6 * b ^ 7
        + 1518714054 * a ^ 5 * b ^ 8
        + 1196174265 * a ^ 4 * b ^ 9
        + 653623828 * a ^ 3 * b ^ 10
        + 231156822 * a ^ 2 * b ^ 11
        + 46037186 * a * b ^ 12
        + 3627003 * b ^ 13
        + (-25 : ℤ) * a ^ 4
        + (-160 : ℤ) * a ^ 3 * b
        + (-386 : ℤ) * a ^ 2 * b ^ 2
        + (-416 : ℤ) * a * b ^ 3
        + (-169 : ℤ) * b ^ 4
        + 100 * a ^ 2
        + 320 * a * b
        + 260 * b ^ 2
        + (-100 : ℤ) := by
    ring
  have hgt : (0 : ℤ) <
      (13 : ℤ) * (2 * a + 3 * b) * (a + 2 * b) ^ 12
        - 286 * (2 * a + 3 * b) ^ 3 * (a + 2 * b) ^ 10
        + 1287 * (2 * a + 3 * b) ^ 5 * (a + 2 * b) ^ 8
        - 1716 * (2 * a + 3 * b) ^ 7 * (a + 2 * b) ^ 6
        + 715 * (2 * a + 3 * b) ^ 9 * (a + 2 * b) ^ 4
        - 78 * (2 * a + 3 * b) ^ 11 * (a + 2 * b) ^ 2
        + (2 * a + 3 * b) ^ 13
      - ((2 * a + 3 * b) ^ 2 + (a + 2 * b) ^ 2 - 10) ^ 2 := by
    rw [hexp]
    have ha0 : a = 0 ∨ 1 ≤ a := by omega
    have hb0 : b = 0 ∨ 1 ≤ b := by omega
    have hrest : (0 : ℤ) ≤
        726063 * a ^ 12 * b
        + 7085364 * a ^ 11 * b ^ 2
        + 41604134 * a ^ 10 * b ^ 3
        + 163965230 * a ^ 9 * b ^ 4
        + 457671357 * a ^ 8 * b ^ 5
        + 929588088 * a ^ 7 * b ^ 6
        + 1388087844 * a ^ 6 * b ^ 7
        + 1518714054 * a ^ 5 * b ^ 8
        + 1196174265 * a ^ 4 * b ^ 9
        + 653623828 * a ^ 3 * b ^ 10
        + 231156822 * a ^ 2 * b ^ 11
        + 46037186 * a * b ^ 12
        + 100 * a ^ 2
        + 320 * a * b
        + 260 * b ^ 2 := by
      nlinarith [h0a, h0b, pow_nonneg h0a 2, pow_nonneg h0a 3, pow_nonneg h0a 4,
        pow_nonneg h0a 5, pow_nonneg h0a 6, pow_nonneg h0a 7, pow_nonneg h0a 8,
        pow_nonneg h0a 9, pow_nonneg h0a 10, pow_nonneg h0a 11, pow_nonneg h0a 12,
        pow_nonneg h0b 2, pow_nonneg h0b 3, pow_nonneg h0b 4, pow_nonneg h0b 5,
        pow_nonneg h0b 6, pow_nonneg h0b 7, pow_nonneg h0b 8, pow_nonneg h0b 9,
        pow_nonneg h0b 10, pow_nonneg h0b 11, pow_nonneg h0b 12]
    have hA : (0 : ℤ) <
        33802 * a ^ 13 + 3627003 * b ^ 13
          - 25 * a ^ 4 - 160 * a ^ 3 * b - 386 * a ^ 2 * b ^ 2
          - 416 * a * b ^ 3 - 169 * b ^ 4 - 100 := by
      rcases ha0 with ha0 | ha1
      · subst ha0
        have hb1 : 1 ≤ b := by omega
        have hb1z : (1 : ℤ) ≤ b := by exact_mod_cast hb1
        have hpos := pow13_sub_pow4_const_pos b 3627003 169 100 hb1z
          (by norm_num) (by norm_num) (by norm_num)
        have heq : (33802 : ℤ) * (0 : ℕ) ^ 13 + 3627003 * b ^ 13
            - 25 * (0 : ℕ) ^ 4 - 160 * (0 : ℕ) ^ 3 * b
            - 386 * (0 : ℕ) ^ 2 * b ^ 2 - 416 * (0 : ℕ) * b ^ 3
            - 169 * b ^ 4 - 100
            = 3627003 * b ^ 13 - 169 * b ^ 4 - 100 := by ring
        simpa [heq] using hpos
      · rcases hb0 with hb0 | hb1
        · subst hb0
          have ha1z : (1 : ℤ) ≤ a := by exact_mod_cast ha1
          have hpos := pow13_sub_pow4_const_pos a 33802 25 100 ha1z
            (by norm_num) (by norm_num) (by norm_num)
          have heq : (33802 : ℤ) * a ^ 13 + 3627003 * (0 : ℕ) ^ 13
              - 25 * a ^ 4 - 160 * a ^ 3 * (0 : ℕ)
              - 386 * a ^ 2 * (0 : ℕ) ^ 2 - 416 * a * (0 : ℕ) ^ 3
              - 169 * (0 : ℕ) ^ 4 - 100
              = 33802 * a ^ 13 - 25 * a ^ 4 - 100 := by ring
          simpa [heq] using hpos
        · have ha1z : (1 : ℤ) ≤ a := by exact_mod_cast ha1
          have hb1z : (1 : ℤ) ≤ b := by exact_mod_cast hb1
          have ha13 : (1 : ℤ) ≤ a ^ 13 := one_le_pow_of_one_le ha1z 13
          have hb13 : (1 : ℤ) ≤ b ^ 13 := one_le_pow_of_one_le hb1z 13
          have hapow : (a : ℤ) ^ 4 ≤ a ^ 13 :=
            pow_le_pow_right ha1z (by decide : (4 : ℕ) ≤ 13)
          have h1b : (1 : ℤ) ≤ b := hb1z
          have hpow : (b : ℤ) ^ 4 ≤ b ^ 13 :=
            pow_le_pow_right h1b (by decide : (4 : ℕ) ≤ 13)
          have ha6 : (a : ℤ) ^ 6 ≤ a ^ 13 :=
            pow_le_pow_right ha1z (by decide : (6 : ℕ) ≤ 13)
          have hb6 : (b : ℤ) ^ 6 ≤ b ^ 13 :=
            pow_le_pow_right h1b (by decide : (6 : ℕ) ≤ 13)
          have ha2 : (a : ℤ) ^ 2 ≤ a ^ 13 :=
            pow_le_pow_right ha1z (by decide : (2 : ℕ) ≤ 13)
          have hb2sq : (b : ℤ) ^ 2 ≤ b ^ 13 :=
            pow_le_pow_right h1b (by decide : (2 : ℕ) ≤ 13)
          have m0 : (25 : ℤ) * a ^ 4 ≤ 25 * a ^ 13 :=
            mul_le_mul_of_nonneg_left hapow (by norm_num)
          have m1 : (160 : ℤ) * a ^ 3 * b ≤ 80 * a ^ 13 + 80 * b ^ 13 := by
            have h2 : (2 : ℤ) * (a ^ 3) * b ≤ (a ^ 3) ^ 2 + b ^ 2 :=
              two_mul_le_sq_add (a ^ 3) b
            have : (2 : ℤ) * a ^ 3 * b ≤ a ^ 6 + b ^ 2 := by
              convert h2 using 1 <;> ring
            nlinarith [this, ha6, hb2sq]
          have m2 : (386 : ℤ) * a ^ 2 * b ^ 2 ≤ 193 * a ^ 13 + 193 * b ^ 13 := by
            have h2 : (2 : ℤ) * (a ^ 2) * (b ^ 2) ≤ (a ^ 2) ^ 2 + (b ^ 2) ^ 2 :=
              two_mul_le_sq_add (a ^ 2) (b ^ 2)
            have : (2 : ℤ) * a ^ 2 * b ^ 2 ≤ a ^ 4 + b ^ 4 := by
              convert h2 using 1 <;> ring
            nlinarith [this, hapow, hpow]
          have m3 : (416 : ℤ) * a * b ^ 3 ≤ 208 * a ^ 13 + 208 * b ^ 13 := by
            have h2 : (2 : ℤ) * a * (b ^ 3) ≤ a ^ 2 + (b ^ 3) ^ 2 :=
              two_mul_le_sq_add a (b ^ 3)
            have : (2 : ℤ) * a * b ^ 3 ≤ a ^ 2 + b ^ 6 := by
              convert h2 using 1 <;> ring
            nlinarith [this, ha2, hb6]
          have m4 : (169 : ℤ) * b ^ 4 ≤ 169 * b ^ 13 :=
            mul_le_mul_of_nonneg_left hpow (by norm_num)
          linarith [m0, m1, m2, m3, m4, ha13, hb13]
    linarith [hA, hrest]
  linarith [hgt]

theorem re13_gt_of_half_two_thirds (d e : ℕ) (he : 1 ≤ e)
    (hlo : d ≤ 2 * e) (hhi : 3 * e ≤ 2 * d) (hN : 10 < d * d + e * e) :
    (13 : ℤ) * d * (e : ℤ) ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13
    > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := by
  set a := 2 * d - 3 * e
  set b := 2 * e - d
  have hk : d = 2 * a + 3 * b ∧ e = a + 2 * b := by
    simp only [a, b]
    constructor <;> omega
  have hsum : 1 ≤ a + b := by
    have : 1 ≤ e := he
    omega
  rw [hk.1, hk.2]
  have hN' : 10 < (2 * a + 3 * b) * (2 * a + 3 * b) + (a + 2 * b) * (a + 2 * b) := by
    simpa [hk.1, hk.2] using hN
  simpa [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] using
    re13_pos_gt_half_two_thirds a b hsum hN'

def re13 (d e : ℤ) : ℤ :=
  d ^ 13 - 78 * d ^ 11 * e ^ 2 + 715 * d ^ 9 * e ^ 4 - 1716 * d ^ 7 * e ^ 6
    + 1287 * d ^ 5 * e ^ 8 - 286 * d ^ 3 * e ^ 10 + 13 * d * e ^ 12

def rhs10 (d e : ℤ) : ℤ := (d ^ 2 + e ^ 2 - 10) ^ 2

theorem re13_eq_poly (d e : ℤ) :
    re13 d e =
      (13 : ℤ) * d * e ^ 12 - 286 * d ^ 3 * e ^ 10 + 1287 * d ^ 5 * e ^ 8
        - 1716 * d ^ 7 * e ^ 6 + 715 * d ^ 9 * e ^ 4 - 78 * d ^ 11 * e ^ 2
        + d ^ 13 := by
  unfold re13; ring

theorem re13_eq_gaussian (d e : ℤ) :
    re13 d e = ((⟨d, e⟩ : GaussianInt) ^ 13).re := by
  rw [re13_eq_poly, gaussian_pow13_re]
  ring

/-- Homogeneous form of `13u⁶ - 286u⁵v + ⋯ + v⁶`. Rational-root
    candidates of `P₆` are `0, ±1, ±1/13`; none is a root. -/
def p6Hom (n m : ℤ) : ℤ :=
  13 * n ^ 6 - 286 * n ^ 5 * m + 1287 * n ^ 4 * m ^ 2 - 1716 * n ^ 3 * m ^ 3
    + 715 * n ^ 2 * m ^ 4 - 78 * n * m ^ 5 + m ^ 6

theorem p6Hom_zero_of_re13_zero {d e : ℤ} (hd : d ≠ 0) (h0 : re13 d e = 0) :
    p6Hom (e ^ 2) (d ^ 2) = 0 := by
  have hpoly := re13_eq_poly d e
  have hI :
      d *
          (d ^ 12 - 78 * d ^ 10 * e ^ 2 + 715 * d ^ 8 * e ^ 4
            - 1716 * d ^ 6 * e ^ 6 + 1287 * d ^ 4 * e ^ 8
            - 286 * d ^ 2 * e ^ 10 + 13 * e ^ 12) = 0 := by
    convert (show re13 d e = 0 from h0) using 1
    rw [hpoly]
    ring
  have hInner :
      d ^ 12 - 78 * d ^ 10 * e ^ 2 + 715 * d ^ 8 * e ^ 4
        - 1716 * d ^ 6 * e ^ 6 + 1287 * d ^ 4 * e ^ 8
        - 286 * d ^ 2 * e ^ 10 + 13 * e ^ 12 = 0 :=
    eq_zero_of_ne_zero_of_mul_left_eq_zero hd hI
  unfold p6Hom
  convert hInner using 1
  ring

theorem p6Hom_ne_zero_of_m_ne_zero (n m : ℕ) (hm : m ≠ 0) :
    p6Hom (n : ℤ) (m : ℤ) ≠ 0 := by
  intro hF
  set g := Nat.gcd n m
  have hgpos : 0 < g := Nat.gcd_pos_of_pos_right n (Nat.pos_of_ne_zero hm)
  set n' := n / g
  set m' := m / g
  have hn : n = g * n' := (Nat.mul_div_cancel' (Nat.gcd_dvd_left n m)).symm
  have hmdiv : m = g * m' := (Nat.mul_div_cancel' (Nat.gcd_dvd_right n m)).symm
  have hcop : Nat.Coprime n' m' := Nat.coprime_div_gcd_div_gcd hgpos
  have hmg : m' ≠ 0 := by
    intro hz
    exact hm (by rw [hmdiv, hz, mul_zero])
  have hscale : p6Hom (n' : ℤ) (m' : ℤ) = 0 := by
    have hmul : p6Hom ((g : ℤ) * n') ((g : ℤ) * m') = 0 := by
      convert hF
      · simp [hn]
      · simp [hmdiv]
    have hhom :
        p6Hom ((g : ℤ) * n') ((g : ℤ) * m') =
          (g : ℤ) ^ 6 * p6Hom (n' : ℤ) (m' : ℤ) := by
      unfold p6Hom; ring
    rw [hhom] at hmul
    exact eq_zero_of_ne_zero_of_mul_left_eq_zero
      (pow_ne_zero 6 (by exact_mod_cast hgpos.ne')) hmul
  have hn'm6 : (n' : ℤ) ∣ (m' : ℤ) ^ 6 := by
    unfold p6Hom at hscale
    refine
      ⟨-(13 * (n' : ℤ) ^ 5 - 286 * (n' : ℤ) ^ 4 * m' + 1287 * (n' : ℤ) ^ 3 * m' ^ 2
          - 1716 * (n' : ℤ) ^ 2 * m' ^ 3 + 715 * (n' : ℤ) * m' ^ 4 - 78 * m' ^ 5), ?_⟩
    linarith [hscale]
  have hcop' : IsCoprime (n' : ℤ) (m' : ℤ) := Nat.Coprime.isCoprime hcop
  have hn'1 : (n' : ℤ) ∣ (1 : ℤ) :=
    (hcop'.pow_right (n := 6)).dvd_of_dvd_mul_right (by simpa [one_mul] using hn'm6)
  have hn1 : n' ∣ 1 := by exact_mod_cast hn'1
  have hle : n' ≤ 1 := Nat.le_of_dvd (by decide : (0 : ℕ) < 1) hn1
  interval_cases n'
  · have : p6Hom (0 : ℤ) (m' : ℤ) = (m' : ℤ) ^ 6 := by unfold p6Hom; ring
    have hsc : p6Hom (0 : ℤ) (m' : ℤ) = 0 := hscale
    rw [this] at hsc
    exact pow_ne_zero 6 (by exact_mod_cast hmg) hsc
  · have hlead : p6Hom (1 : ℤ) (m' : ℤ) =
        13 - (m' : ℤ) *
          (286 - 1287 * m' + 1716 * m' ^ 2 - 715 * m' ^ 3 + 78 * m' ^ 4 - m' ^ 5) := by
      unfold p6Hom; ring
    have hm13z : (m' : ℤ) ∣ (13 : ℤ) := by
      have hsc : p6Hom (1 : ℤ) (m' : ℤ) = 0 := hscale
      rw [hlead] at hsc
      refine ⟨286 - 1287 * m' + 1716 * m' ^ 2 - 715 * m' ^ 3 + 78 * m' ^ 4 - m' ^ 5, ?_⟩
      linarith [hsc]
    have hmdvd : m' ∣ 13 := by exact_mod_cast hm13z
    have hprime : Nat.Prime 13 := by decide
    rcases (Nat.dvd_prime hprime).1 hmdvd with hm1 | hm13
    · rw [hm1] at hscale
      have hne : p6Hom (1 : ℤ) (1 : ℤ) ≠ 0 := by native_decide
      exact hne hscale
    · rw [hm13] at hscale
      have hne : p6Hom (1 : ℤ) (13 : ℤ) ≠ 0 := by native_decide
      exact hne hscale

theorem re13_ne_zero_of_int_ne_zero (d e : ℤ) (hd : d ≠ 0) : re13 d e ≠ 0 := by
  intro h0
  have hP := p6Hom_zero_of_re13_zero hd h0
  have hsq : e ^ 2 = ((e.natAbs : ℕ) : ℤ) ^ 2 := by
    have := int_sq_natAbs e
    simpa [pow_two] using this.symm
  have hsd : d ^ 2 = ((d.natAbs : ℕ) : ℤ) ^ 2 := by
    have := int_sq_natAbs d
    simpa [pow_two] using this.symm
  have : p6Hom ((e.natAbs ^ 2 : ℕ) : ℤ) ((d.natAbs ^ 2 : ℕ) : ℤ) = 0 := by
    have hform : p6Hom (e ^ 2) (d ^ 2) = p6Hom ((e.natAbs : ℤ) ^ 2) ((d.natAbs : ℤ) ^ 2) := by
      rw [hsq, hsd]
    have hcast : ((e.natAbs ^ 2 : ℕ) : ℤ) = (e.natAbs : ℤ) ^ 2 := by
      simp [Nat.cast_pow]
    have hcast' : ((d.natAbs ^ 2 : ℕ) : ℤ) = (d.natAbs : ℤ) ^ 2 := by
      simp [Nat.cast_pow]
    rw [hcast, hcast', ← hform]
    exact hP
  have hm : (d.natAbs ^ 2) ≠ 0 := by
    intro hz
    have := Nat.pow_eq_zero.mp hz
    exact hd (Int.natAbs_eq_zero.mp this.1)
  exact p6Hom_ne_zero_of_m_ne_zero (e.natAbs ^ 2) (d.natAbs ^ 2) hm this

theorem re13_poly_pos_gt_rhs {d e : ℕ}
    (h : (13 : ℤ) * d * e ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13
      > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2) :
    |re13 d e| > rhs10 d e := by
  have hpoly : re13 d e =
      (13 : ℤ) * d * e ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
        + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
        + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
        + (d : ℤ) ^ 13 := re13_eq_poly d e
  have hrhs : rhs10 d e = ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := rfl
  have hrhs0 : 0 ≤ rhs10 d e := sq_nonneg _
  rw [hpoly, hrhs]
  have hpos : 0 <
      (13 : ℤ) * d * e ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
        + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
        + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
        + (d : ℤ) ^ 13 :=
    lt_of_le_of_lt (by simpa [hrhs] using hrhs0) h
  rw [abs_of_pos hpos]
  exact h

theorem re13_poly_neg_gt_rhs {d e : ℕ}
    (h : -((13 : ℤ) * d * e ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
      + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
      + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
      + (d : ℤ) ^ 13)
      > ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2) :
    |re13 d e| > rhs10 d e := by
  have hpoly : re13 d e =
      (13 : ℤ) * d * e ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
        + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
        + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
        + (d : ℤ) ^ 13 := re13_eq_poly d e
  have hrhs : rhs10 d e = ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := rfl
  rw [hpoly, hrhs]
  have hneg :
      (13 : ℤ) * d * e ^ 12 - 286 * (d : ℤ) ^ 3 * e ^ 10
        + 1287 * (d : ℤ) ^ 5 * e ^ 8 - 1716 * (d : ℤ) ^ 7 * e ^ 6
        + 715 * (d : ℤ) ^ 9 * e ^ 4 - 78 * (d : ℤ) ^ 11 * e ^ 2
        + (d : ℤ) ^ 13 < 0 := by
    have hrhs0 : 0 ≤ ((d : ℤ) ^ 2 + (e : ℤ) ^ 2 - 10) ^ 2 := sq_nonneg _
    linarith
  rw [abs_of_neg hneg]
  simpa using h

/-- Outer cone `e ≥ 5d`. -/
theorem re13_gt_of_five_mul (d e : ℤ) (he : 5 * d ≤ e) (hd : 0 < d) :
    |re13 d e| > rhs10 d e := by
  have hd0 : 0 ≤ d := le_of_lt hd
  have he0 : 0 ≤ e := le_trans (mul_nonneg (by norm_num : (0 : ℤ) ≤ 5) hd0) he
  lift d to ℕ using hd0
  lift e to ℕ using he0
  have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Int.natCast_pos.mp hd)
  have he' : 5 * d ≤ e := by exact_mod_cast he
  exact re13_poly_pos_gt_rhs (re13_poly_gt_of_five_mul d e hd1 he')

/-- Outer cone `d ≥ 10e`. -/
theorem re13_gt_of_ten_mul (d e : ℤ) (hd : 10 * e ≤ d) (he : 0 < e) :
    |re13 d e| > rhs10 d e := by
  have he0 : 0 ≤ e := le_of_lt he
  have hd0 : 0 ≤ d := le_trans (mul_nonneg (by norm_num : (0 : ℤ) ≤ 10) he0) hd
  lift e to ℕ using he0
  lift d to ℕ using hd0
  have he1 : 1 ≤ e := Nat.succ_le_of_lt (Int.natCast_pos.mp he)
  have hd' : 10 * e ≤ d := by exact_mod_cast hd
  exact re13_poly_pos_gt_rhs (re13_poly_gt_of_ten_mul d e he1 hd')

theorem re13_gt_of_two_four_int (d e : ℤ) (hd : 0 < d)
    (h2 : 2 * d ≤ e) (h4 : e ≤ 4 * d) :
    |re13 d e| > rhs10 d e := by
  have hd0 : 0 ≤ d := le_of_lt hd
  have he0 : 0 ≤ e := le_trans (mul_nonneg (by norm_num : (0 : ℤ) ≤ 2) hd0) h2
  lift d to ℕ using hd0
  lift e to ℕ using he0
  have hd1 : 1 ≤ d := Nat.succ_le_of_lt (Int.natCast_pos.mp hd)
  have h2' : 2 * d ≤ e := by exact_mod_cast h2
  have h4' : e ≤ 4 * d := by exact_mod_cast h4
  exact re13_poly_neg_gt_rhs (re13_gt_of_two_four d e hd1 h2' h4')

theorem re13_gt_of_three_seven_int (d e : ℤ) (he : 0 < e)
    (h3 : 3 * e ≤ d) (h7 : d ≤ 7 * e) :
    |re13 d e| > rhs10 d e := by
  have he0 : 0 ≤ e := le_of_lt he
  have hd0 : 0 ≤ d := le_trans (mul_nonneg (by norm_num : (0 : ℤ) ≤ 3) he0) h3
  lift e to ℕ using he0
  lift d to ℕ using hd0
  have he1 : 1 ≤ e := Nat.succ_le_of_lt (Int.natCast_pos.mp he)
  have h3' : 3 * e ≤ d := by exact_mod_cast h3
  have h7' : d ≤ 7 * e := by exact_mod_cast h7
  exact re13_poly_neg_gt_rhs (re13_gt_of_three_seven d e he1 h3' h7')

theorem re13_gt_of_seven_int (d e : ℤ) (he : 0 < e)
    (h7 : 7 * e ≤ d) (h8 : d ≤ 8 * e) :
    |re13 d e| > rhs10 d e := by
  have he0 : 0 ≤ e := le_of_lt he
  have hd0 : 0 ≤ d := le_trans (mul_nonneg (by norm_num : (0 : ℤ) ≤ 7) he0) h7
  lift e to ℕ using he0
  lift d to ℕ using hd0
  have he1 : 1 ≤ e := Nat.succ_le_of_lt (Int.natCast_pos.mp he)
  exact re13_poly_neg_gt_rhs (re13_gt_of_seven d e he1
    (by exact_mod_cast h7) (by exact_mod_cast h8))

theorem re13_gt_of_nine_int (d e : ℤ) (he : 0 < e)
    (h9 : 9 * e ≤ d) (h10 : d ≤ 10 * e) :
    |re13 d e| > rhs10 d e := by
  have he0 : 0 ≤ e := le_of_lt he
  have hd0 : 0 ≤ d := le_trans (mul_nonneg (by norm_num : (0 : ℤ) ≤ 9) he0) h9
  lift e to ℕ using he0
  lift d to ℕ using hd0
  have he1 : 1 ≤ e := Nat.succ_le_of_lt (Int.natCast_pos.mp he)
  exact re13_poly_pos_gt_rhs (re13_gt_of_nine d e he1
    (by exact_mod_cast h9) (by exact_mod_cast h10))

theorem re13_gt_of_eight_collar_int (d e : ℤ) (he : 0 < e)
    (h8 : 8 * e ≤ d) (hk5 : 5 * (d - 8 * e) ≤ e) :
    |re13 d e| > rhs10 d e := by
  have he0 : 0 ≤ e := le_of_lt he
  have hd0 : 0 ≤ d := le_trans (mul_nonneg (by norm_num : (0 : ℤ) ≤ 8) he0) h8
  lift e to ℕ using he0
  lift d to ℕ using hd0
  have he1 : 1 ≤ e := Nat.succ_le_of_lt (Int.natCast_pos.mp he)
  have h8' : 8 * e ≤ d := by exact_mod_cast h8
  have hk5' : 5 * (d - 8 * e) ≤ e := by exact_mod_cast hk5
  exact re13_poly_neg_gt_rhs (re13_gt_of_eight_collar d e he1 h8' hk5')

theorem re13_gt_of_three_four_int (d e : ℤ) (he : 0 < e)
    (h34 : 3 * d ≤ 4 * e) (hle : e ≤ d) (hN : 10 < d ^ 2 + e ^ 2) :
    |re13 d e| > rhs10 d e := by
  have he0 : 0 ≤ e := le_of_lt he
  have hd0 : 0 ≤ d := le_trans he0 hle
  lift e to ℕ using he0
  lift d to ℕ using hd0
  have he1 : 1 ≤ e := Nat.succ_le_of_lt (Int.natCast_pos.mp he)
  have hN' : 10 < d * d + e * e := by
    have hz : (10 : ℤ) < (d : ℤ) * d + e * e := by
      simpa [pow_two] using hN
    exact Nat.cast_lt.mp hz
  exact re13_poly_neg_gt_rhs (re13_gt_of_three_four d e he1
    (by exact_mod_cast h34) (by exact_mod_cast hle) hN')

theorem re13_gt_of_half_two_thirds_int (d e : ℤ) (he : 0 < e)
    (hlo : d ≤ 2 * e) (hhi : 3 * e ≤ 2 * d) (hN : 10 < d ^ 2 + e ^ 2) :
    |re13 d e| > rhs10 d e := by
  have he0 : 0 ≤ e := le_of_lt he
  have hd0 : 0 ≤ d := by nlinarith [hhi, he0]
  lift e to ℕ using he0
  lift d to ℕ using hd0
  have he1 : 1 ≤ e := Nat.succ_le_of_lt (Int.natCast_pos.mp he)
  have hN' : 10 < d * d + e * e := by
    have hz : (10 : ℤ) < (d : ℤ) * d + e * e := by
      simpa [pow_two] using hN
    exact Nat.cast_lt.mp hz
  exact re13_poly_pos_gt_rhs (re13_gt_of_half_two_thirds d e he1
    (by exact_mod_cast hlo) (by exact_mod_cast hhi) hN')

def re13_middle_good (d e : ℕ) : Bool :=
  decide ((re13 (d : ℤ) (e : ℤ)).natAbs > (rhs10 (d : ℤ) (e : ℤ)).natAbs)

def re13_middle_skip (d e : ℕ) : Bool :=
  decide (d < 2 ∨ e < 2 ∨ d > 10 * e ∨ e > 5 * d ∨ d * d + e * e ≤ 10)

def re13_middle_check : ℕ → Bool
  | 0 => true
  | n + 1 =>
      (List.range (5 * (n + 1) + 1)).all (fun e =>
        re13_middle_skip (n + 1) e || re13_middle_good (n + 1) e) &&
        re13_middle_check n

theorem re13_middle_check_100 : re13_middle_check 100 = true := by
  native_decide

lemma re13_middle_check_spec :
    ∀ n d e : ℕ, re13_middle_check n = true → d ≤ n → 2 ≤ d → 2 ≤ e →
      d ≤ 10 * e → e ≤ 5 * d → 10 < d * d + e * e →
      (re13 (d : ℤ) (e : ℤ)).natAbs > (rhs10 (d : ℤ) (e : ℤ)).natAbs := by
  intro n
  induction n with
  | zero =>
      intro d e _hchk hd hd2 _he2 _hlow _hhigh _hN
      have : d = 0 := Nat.eq_zero_of_le_zero hd
      subst this
      exact absurd hd2 (by decide)
  | succ n ih =>
      intro d e hchk hd hd2 he2 hlow hhigh hN
      rw [re13_middle_check] at hchk
      have hand : ((List.range (5 * (n + 1) + 1)).all
          (fun e => re13_middle_skip (n + 1) e ||
            re13_middle_good (n + 1) e) = true) ∧
          re13_middle_check n = true := by
        simpa [Bool.and_eq_true] using hchk
      have hrow := hand.1
      have hprev := hand.2
      have hde : d ≤ n ∨ d = n + 1 := by omega
      rcases hde with hdn | hdEq
      · exact ih d e hprev hdn hd2 he2 hlow hhigh hN
      · subst hdEq
        have hel : e ∈ List.range (5 * (n + 1) + 1) := by
          rw [List.mem_range]
          exact Nat.lt_succ_of_le hhigh
        have hall := List.all_eq_true.mp hrow
        have hdisj := hall e hel
        have hskip_false : re13_middle_skip (n + 1) e = false := by
          have hnot : ¬ (n + 1 < 2 ∨ e < 2 ∨ n + 1 > 10 * e ∨
              e > 5 * (n + 1) ∨ (n + 1) * (n + 1) + e * e ≤ 10) := by
            push_neg
            exact ⟨hd2, he2, hlow, hhigh, hN⟩
          simpa [re13_middle_skip, decide_eq_false_iff_not] using hnot
        have hgood : re13_middle_good (n + 1) e = true := by
          have hor : re13_middle_skip (n + 1) e = true ∨
              re13_middle_good (n + 1) e = true := by
            simpa [Bool.or_eq_true] using hdisj
          cases hor with
          | inl hskip =>
              rw [hskip_false] at hskip
              cases hskip
          | inr hg => exact hg
        simpa [re13_middle_good, decide_eq_true_eq] using hgood

lemma abs_natAbs_gt {a b : ℤ} (h : a.natAbs > b.natAbs) (hb : 0 ≤ b) : |a| > b := by
  have hb' : (b.natAbs : ℤ) = b := Int.natAbs_of_nonneg hb
  have ha : |a| = (a.natAbs : ℤ) := (Int.natCast_natAbs a).symm
  have : (a.natAbs : ℤ) > (b.natAbs : ℤ) := Nat.cast_lt.mpr h
  rw [← ha, hb'] at this
  exact this

theorem re13_homog (k d e : ℤ) :
    re13 (k * d) (k * e) = k ^ 13 * re13 d e := by
  unfold re13; ring

theorem re13_eq_d_mul_p6Hom (d e : ℤ) :
    re13 d e = d * p6Hom (e ^ 2) (d ^ 2) := by
  unfold re13 p6Hom; ring

/-- Scaling along a ray: `k ≥ 2`, `N = u²+v² ≥ 13`. Then
    `k⁹ ≥ 512 > (13/3)² ≥ (N/(N-10))²`. -/
theorem re13_gt_of_scale {u v k : ℕ}
    (hN : 13 ≤ u * u + v * v) (hk : 2 ≤ k)
    (hprim : |re13 u v| > rhs10 u v) :
    |re13 (k * u) (k * v)| > rhs10 (k * u) (k * v) := by
  have hk0 : (0 : ℤ) ≤ k := Nat.cast_nonneg k
  have hu0 : (0 : ℤ) ≤ u := Nat.cast_nonneg u
  have hv0 : (0 : ℤ) ≤ v := Nat.cast_nonneg v
  have hk2 : (2 : ℤ) ≤ k := by exact_mod_cast hk
  have hNz : (13 : ℤ) ≤ (u : ℤ) ^ 2 + (v : ℤ) ^ 2 := by
    simpa [pow_two] using (by exact_mod_cast hN : (13 : ℤ) ≤ u * u + v * v)
  set N : ℤ := (u : ℤ) ^ 2 + (v : ℤ) ^ 2
  have hN10 : (3 : ℤ) ≤ N - 10 := by
    have : (13 : ℤ) ≤ N := by simpa [N] using hNz
    linarith
  have hk9 : (512 : ℤ) ≤ (k : ℤ) ^ 9 := by
    have h2 : (2 : ℤ) ^ 9 ≤ (k : ℤ) ^ 9 :=
      pow_le_pow_left (by norm_num) hk2 9
    have : (2 : ℤ) ^ 9 = 512 := by norm_num
    rwa [this] at h2
  have hhom : re13 (k * u : ℤ) (k * v) = (k : ℤ) ^ 13 * re13 u v := by
    simpa using re13_homog k u v
  have habs : |re13 (k * u : ℤ) (k * v)| = (k : ℤ) ^ 13 * |re13 u v| := by
    rw [hhom, abs_mul, abs_of_nonneg (pow_nonneg hk0 13)]
  have hrhs : rhs10 (k * u : ℤ) (k * v) =
      ((k : ℤ) ^ 2 * N - 10) ^ 2 := by
    unfold rhs10; simp [N]; ring
  have hrhsuv : rhs10 (u : ℤ) v = (N - 10) ^ 2 := by
    unfold rhs10; simp [N]
  have hk13pos : (0 : ℤ) < (k : ℤ) ^ 13 :=
    pow_pos (lt_of_lt_of_le (by norm_num) hk2) 13
  have hN2bound : N ^ 2 ≤ 19 * (N - 10) ^ 2 := by
    have hfrac : (3 : ℤ) * N ≤ 13 * (N - 10) := by
      have : (13 : ℤ) ≤ N := by simpa [N] using hNz
      linarith
    nlinarith [hfrac, hN10, sq_nonneg N, sq_nonneg (N - 10)]
  have hk4 : (0 : ℤ) ≤ (k : ℤ) ^ 4 := pow_nonneg hk0 4
  have hposN : (0 : ℤ) < (k : ℤ) ^ 2 * N - 10 := by
    have : (4 : ℤ) * 13 ≤ (k : ℤ) ^ 2 * N := by
      have hk2sq : (4 : ℤ) ≤ k ^ 2 := by
        have : (2 : ℤ) ^ 2 ≤ k ^ 2 := pow_le_pow_left (by norm_num) hk2 2
        simpa using this
      have hN13 : (13 : ℤ) ≤ N := by simpa [N] using hNz
      nlinarith [hk2sq, hN13, pow_nonneg hk0 2]
    linarith
  have hrhs_lt_k4N : ((k : ℤ) ^ 2 * N - 10) ^ 2 < (k : ℤ) ^ 4 * N ^ 2 := by
    have : (k : ℤ) ^ 2 * N - 10 < k ^ 2 * N := by linarith
    have hpos2 : (0 : ℤ) < k ^ 2 * N := lt_trans hposN (by linarith)
    nlinarith [hposN, hpos2, pow_nonneg hk0 2]
  have hcmp : (k : ℤ) ^ 4 * N ^ 2 ≤ (k : ℤ) ^ 4 * 19 * (N - 10) ^ 2 := by
    have h' : (k : ℤ) ^ 4 * N ^ 2 ≤ k ^ 4 * (19 * (N - 10) ^ 2) :=
      mul_le_mul_of_nonneg_left hN2bound hk4
    convert h' using 1
    ring
  have h19 : (19 : ℤ) * (k : ℤ) ^ 4 < (k : ℤ) ^ 13 := by
    have hsplit : (k : ℤ) ^ 13 = k ^ 4 * k ^ 9 := by ring
    have hk4pos : (0 : ℤ) < k ^ 4 :=
      pow_pos (lt_of_lt_of_le (by norm_num) hk2) 4
    have : (19 : ℤ) * k ^ 4 < 512 * k ^ 4 :=
      mul_lt_mul_of_pos_right (by norm_num) hk4pos
    have : (512 : ℤ) * k ^ 4 ≤ k ^ 4 * k ^ 9 := by
      nlinarith [hk9, hk4, pow_nonneg hk0 9]
    nlinarith [hsplit, this]
  have hdom : (k : ℤ) ^ 4 * 19 * (N - 10) ^ 2 < (k : ℤ) ^ 13 * (N - 10) ^ 2 := by
    have hpos : (0 : ℤ) < (N - 10) ^ 2 := sq_pos_of_pos (by linarith [hN10])
    nlinarith [h19, hpos, hk4]
  have hchain : ((k : ℤ) ^ 2 * N - 10) ^ 2 < (k : ℤ) ^ 13 * (N - 10) ^ 2 :=
    lt_trans hrhs_lt_k4N (lt_of_le_of_lt hcmp hdom)
  have : ((k : ℤ) ^ 2 * N - 10) ^ 2 < (k : ℤ) ^ 13 * |re13 u v| :=
    lt_trans hchain
      (mul_lt_mul_of_pos_left (hrhsuv ▸ hprim) hk13pos)
  rw [habs, hrhs]
  exact this

/-- Finite middle-cone check `2 ≤ d ≤ 100`. -/
lemma re13_gt_of_middle_cone_le_100 (d e : ℕ)
    (hd2 : 2 ≤ d) (he2 : 2 ≤ e) (hd100 : d ≤ 100)
    (hlow : d ≤ 10 * e) (hhigh : e ≤ 5 * d)
    (hN : 10 < d * d + e * e) :
    |re13 d e| > rhs10 d e := by
  have hgt :=
    re13_middle_check_spec 100 d e re13_middle_check_100 hd100 hd2 he2 hlow hhigh hN
  exact abs_natAbs_gt hgt (sq_nonneg _)

/-- Scale a composite pair from a primitive with `2 ≤ u,v` and `N≥13`. -/
lemma re13_gt_of_gcd_scale {d e : ℕ} {g : ℕ}
    (hdu : d = g * (d / g)) (hev : e = g * (e / g))
    (hk : 2 ≤ g) (hN : 13 ≤ (d / g) * (d / g) + (e / g) * (e / g))
    (hprim : |re13 (d / g) (e / g)| > rhs10 (d / g) (e / g)) :
    |re13 d e| > rhs10 d e := by
  have hcast : re13 (d : ℤ) (e : ℤ) =
      re13 ((g * (d / g) : ℕ) : ℤ) ((g * (e / g) : ℕ) : ℤ) :=
    congr_arg₂ re13 (congrArg Nat.cast hdu) (congrArg Nat.cast hev)
  have hcastr : rhs10 (d : ℤ) (e : ℤ) =
      rhs10 ((g * (d / g) : ℕ) : ℤ) ((g * (e / g) : ℕ) : ℤ) :=
    congr_arg₂ rhs10 (congrArg Nat.cast hdu) (congrArg Nat.cast hev)
  rw [hcast, hcastr]
  exact re13_gt_of_scale hN hk hprim

/-- Middle cone: leftover bands (any size), `d ≤ 100` enumeration,
    and composite pairs whose primitive has first coordinate `≤ 100`. -/
lemma re13_middle_nat (d e : ℕ)
    (hd2 : 2 ≤ d) (he2 : 2 ≤ e)
    (hlow : d ≤ 10 * e) (hhigh : e ≤ 5 * d)
    (hN : 10 < d * d + e * e)
    (hfin : d ≤ 100 ∨
        (1 < Nat.gcd d e ∧ d / Nat.gcd d e ≤ 100 ∧ 2 ≤ d / Nat.gcd d e ∧
          2 ≤ e / Nat.gcd d e)) :
    |re13 d e| > rhs10 d e := by
  have hdpos : 0 < (d : ℤ) := by
    have : (0 : ℕ) < d := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hd2
    exact_mod_cast this
  have hepos : 0 < (e : ℤ) := by
    have : (0 : ℕ) < e := lt_of_lt_of_le (by decide : (0 : ℕ) < 2) he2
    exact_mod_cast this
  by_cases h5 : 5 * d ≤ e
  · exact re13_gt_of_five_mul (d : ℤ) (e : ℤ) (by exact_mod_cast h5) hdpos
  · by_cases h10 : 10 * e ≤ d
    · exact re13_gt_of_ten_mul (d : ℤ) (e : ℤ) (by exact_mod_cast h10) hepos
    · by_cases h24 : 2 * d ≤ e ∧ e ≤ 4 * d
      · exact re13_gt_of_two_four_int (d : ℤ) (e : ℤ) hdpos
          (by exact_mod_cast h24.1) (by exact_mod_cast h24.2)
      · by_cases h37 : 3 * e ≤ d ∧ d ≤ 7 * e
        · exact re13_gt_of_three_seven_int (d : ℤ) (e : ℤ) hepos
            (by exact_mod_cast h37.1) (by exact_mod_cast h37.2)
        · by_cases h78 : 7 * e ≤ d ∧ d ≤ 8 * e
          · exact re13_gt_of_seven_int (d : ℤ) (e : ℤ) hepos
              (by exact_mod_cast h78.1) (by exact_mod_cast h78.2)
          · by_cases h910 : 9 * e ≤ d ∧ d ≤ 10 * e
            · exact re13_gt_of_nine_int (d : ℤ) (e : ℤ) hepos
                (by exact_mod_cast h910.1) (by exact_mod_cast h910.2)
            · by_cases h8c : 8 * e ≤ d ∧ 5 * ((d : ℤ) - 8 * e) ≤ e
              · exact re13_gt_of_eight_collar_int (d : ℤ) (e : ℤ) hepos
                  (by exact_mod_cast h8c.1) (by exact_mod_cast h8c.2)
              · by_cases h34 : 3 * d ≤ 4 * e ∧ e ≤ d
                · have hNz : 10 < (d : ℤ) ^ 2 + (e : ℤ) ^ 2 := by
                    simpa [pow_two] using
                      (by exact_mod_cast hN : (10 : ℤ) < d * d + e * e)
                  exact re13_gt_of_three_four_int (d : ℤ) (e : ℤ) hepos
                    (by exact_mod_cast h34.1) (by exact_mod_cast h34.2) hNz
                · by_cases h23 : d ≤ 2 * e ∧ 3 * e ≤ 2 * d
                  · have hNz : 10 < (d : ℤ) ^ 2 + (e : ℤ) ^ 2 := by
                      simpa [pow_two] using
                        (by exact_mod_cast hN : (10 : ℤ) < d * d + e * e)
                    exact re13_gt_of_half_two_thirds_int (d : ℤ) (e : ℤ) hepos
                      (by exact_mod_cast h23.1) (by exact_mod_cast h23.2) hNz
                  · rcases hfin with hd100 | ⟨hg, hu100, hu2, hv2⟩
                    · exact re13_gt_of_middle_cone_le_100 d e hd2 he2 hd100
                        hlow hhigh hN
                    · set g := Nat.gcd d e
                      have hgd : g ∣ d := Nat.gcd_dvd_left d e
                      have hge : g ∣ e := Nat.gcd_dvd_right d e
                      have hdu : d = g * (d / g) := (Nat.mul_div_cancel' hgd).symm
                      have hev : e = g * (e / g) := (Nat.mul_div_cancel' hge).symm
                      have hlowu : d / g ≤ 10 * (e / g) := by
                        have hmul : g * (d / g) ≤ 10 * (g * (e / g)) := by
                          rw [← hdu, ← hev]; exact hlow
                        have hassoc : 10 * (g * (e / g)) = g * (10 * (e / g)) := by
                          ring
                        rw [hassoc] at hmul
                        exact Nat.le_of_mul_le_mul_left hmul
                          (lt_trans (by decide : (0 : ℕ) < 1) hg)
                      have hhighu : e / g ≤ 5 * (d / g) := by
                        have hmul : g * (e / g) ≤ 5 * (g * (d / g)) := by
                          rw [← hdu, ← hev]; exact hhigh
                        have hassoc : 5 * (g * (d / g)) = g * (5 * (d / g)) := by
                          ring
                        rw [hassoc] at hmul
                        exact Nat.le_of_mul_le_mul_left hmul
                          (lt_trans (by decide : (0 : ℕ) < 1) hg)
                      have hun2 : ¬ (d / g = 2 ∧ e / g = 2) := by
                        intro ⟨hu0, hv0⟩
                        have : 3 * d ≤ 4 * e ∧ e ≤ d := by
                          have hd' : d = 2 * g := by
                            rw [hdu, hu0, mul_comm]
                          have he' : e = 2 * g := by
                            rw [hev, hv0, mul_comm]
                          omega
                        exact h34 this
                      have hN13 : 13 ≤ (d / g) * (d / g) + (e / g) * (e / g) := by
                        have hu2' : d / g = 2 ∨ 3 ≤ d / g := by omega
                        have hv2' : e / g = 2 ∨ 3 ≤ e / g := by omega
                        rcases hu2' with hu2eq | hu3
                        · rcases hv2' with hv2eq | hv3
                          · exact False.elim (hun2 ⟨hu2eq, hv2eq⟩)
                          · have : 4 + 9 ≤ (d / g) * (d / g) + (e / g) * (e / g) :=
                              Nat.add_le_add
                                (by simp [hu2eq])
                                (Nat.mul_le_mul hv3 hv3)
                            exact this
                        · have : 9 + 4 ≤ (d / g) * (d / g) + (e / g) * (e / g) :=
                            Nat.add_le_add
                              (Nat.mul_le_mul hu3 hu3)
                              (Nat.mul_le_mul hv2 hv2)
                          exact this
                      have hNu : 10 < (d / g) * (d / g) + (e / g) * (e / g) :=
                        lt_of_lt_of_le (by decide : (10 : ℕ) < 13) hN13
                      have hprim :=
                        re13_gt_of_middle_cone_le_100 (d / g) (e / g) hu2 hv2 hu100
                          hlowu hhighu hNu
                      exact re13_gt_of_gcd_scale hdu hev hg hN13 hprim

/-- Middle cone `1/10 ≤ e/d ≤ 5`, `N>10`. Leftover bands are
    identities. Remaining cells with `d ≤ 100` are enumerated.
    Composite remaining cells with primitive `u ≤ 100` scale. -/
theorem re13_gt_of_middle_cone (d e : ℤ) (hd : 2 ≤ d) (he : 2 ≤ e)
    (h_low : d ≤ 10 * e) (h_high : e ≤ 5 * d) (h_not_small : 10 < d ^ 2 + e ^ 2)
    (hfin : d ≤ 100 ∨
        (1 < Nat.gcd d.natAbs e.natAbs ∧
          d.natAbs / Nat.gcd d.natAbs e.natAbs ≤ 100 ∧
            2 ≤ d.natAbs / Nat.gcd d.natAbs e.natAbs ∧
              2 ≤ e.natAbs / Nat.gcd d.natAbs e.natAbs)) :
    |re13 d e| > rhs10 d e := by
  have hd0 : 0 ≤ d := le_trans (by norm_num : (0 : ℤ) ≤ 2) hd
  have he0 : 0 ≤ e := le_trans (by norm_num : (0 : ℤ) ≤ 2) he
  lift d to ℕ using hd0
  lift e to ℕ using he0
  have hd2 : 2 ≤ d := by exact_mod_cast hd
  have he2 : 2 ≤ e := by exact_mod_cast he
  have hlow : d ≤ 10 * e := by exact_mod_cast h_low
  have hhigh : e ≤ 5 * d := by exact_mod_cast h_high
  have hN : 10 < d * d + e * e := by
    have hz : (10 : ℤ) < (d : ℤ) * d + e * e := by
      simpa [pow_two] using h_not_small
    exact Nat.cast_lt.mp hz
  have hfin' : d ≤ 100 ∨
      (1 < Nat.gcd d e ∧ d / Nat.gcd d e ≤ 100 ∧ 2 ≤ d / Nat.gcd d e ∧
        2 ≤ e / Nat.gcd d e) := by
    have hdabs : (d : ℤ).natAbs = d := Int.natAbs_ofNat d
    have heabs : (e : ℤ).natAbs = e := Int.natAbs_ofNat e
    rcases hfin with h100 | hgcd
    · left; exact_mod_cast h100
    · right; simpa [hdabs, heabs] using hgcd
  exact re13_middle_nat d e hd2 he2 hlow hhigh hN hfin'

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
    rw [← hA, ← hB, ← hC]; exact h
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
      dvd_mul_of_dvd_left (Nat.dvd_mul_left 5 2) _
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


/-! ## Original 5-descent: `C₁ = B₁+2` -/

theorem pow13_mod5_eq_self (c : ℕ) : c ^ 13 % 5 = c % 5 :=
  pow13_mod5 c

/-- `C = B+10 ≡ 0 mod 5`, so `C¹³ ≡ 0` and `A⁴ ≡ 0`, hence `5 ∣ A`. -/
theorem five_dvd_B_forces_five_dvd_A_gap10 {A B : ℕ}
    (h : is_gap10_sol A B) (h5 : 5 ∣ B) : 5 ∣ A := by
  have hB4 : B ^ 4 % 5 = 0 :=
    Nat.mod_eq_zero_of_dvd (dvd_pow h5 (by decide))
  have hC : (B + 10) % 5 = 0 := by
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd h5
    rw [Nat.add_mod, this]
  have hC13 : (B + 10) ^ 13 % 5 = 0 := by
    rw [pow13_mod5, hC]
  have hsum : (A ^ 4 + B ^ 4) % 5 = (B + 10) ^ 13 % 5 := by rw [h]
  rw [Nat.add_mod, hB4, Nat.add_zero, Nat.mod_mod, hC13] at hsum
  exact five_dvd_of_fourth_pow_mod_zero hsum

/-- `5 ∣ B` is impossible: three extra divisions by `5` leave
    `125 (A₄⁴ + B₄⁴) = (125 B₄ + 2)¹³` with the right side
    `≡ 2` mod 5. -/
theorem no_sol_when_five_dvd_B_gap10 {A B : ℕ}
    (h : is_gap10_sol A B) (h5 : 5 ∣ B) : False := by
  have hA5 := five_dvd_B_forces_five_dvd_A_gap10 h h5
  obtain ⟨A1, hA⟩ := hA5
  obtain ⟨B1, hB⟩ := h5
  have hC : B + 10 = 5 * (B1 + 2) := by
    rw [hB]; ring
  have hsol1 : (5 * A1) ^ 4 + (5 * B1) ^ 4 = (5 * (B1 + 2)) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 625 * (A1 ^ 4 + B1 ^ 4) = 5 ^ 13 * (B1 + 2) ^ 13 := by
    rw [← sum_fourth_of_mul_five, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 5 ^ 9 * (B1 + 2) ^ 13 := by
    have hpow : (5 : ℕ) ^ 13 = 625 * 5 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 625)
    rw [heq1, hpow, mul_assoc]
  have hmod1 : (A1 ^ 4 + B1 ^ 4) % 5 = 0 := by
    have : 5 ∣ 5 ^ 9 * (B1 + 2) ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 5 (by decide : 9 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1, hB1⟩ := both_five_dvd_of_sum_fourth_mod5_zero hmod1
  obtain ⟨A2, hA2⟩ := hA1
  obtain ⟨B2, hB2⟩ := hB1
  have heq2src : (5 * A2) ^ 4 + (5 * B2) ^ 4 =
      5 ^ 9 * (5 * B2 + 2) ^ 13 := by
    rw [← hA2, ← hB2]
    exact h9
  have heq2 : 625 * (A2 ^ 4 + B2 ^ 4) =
      5 ^ 9 * (5 * B2 + 2) ^ 13 := by
    rw [← sum_fourth_of_mul_five]; exact heq2src
  have h5eq : A2 ^ 4 + B2 ^ 4 = 5 ^ 5 * (5 * B2 + 2) ^ 13 := by
    have hpow : (5 : ℕ) ^ 9 = 625 * 5 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 625)
    rw [heq2, hpow, mul_assoc]
  have hmod2 : (A2 ^ 4 + B2 ^ 4) % 5 = 0 := by
    have : 5 ∣ 5 ^ 5 * (5 * B2 + 2) ^ 13 :=
      dvd_mul_of_dvd_left (dvd_pow_self 5 (by decide : 5 ≠ 0)) _
    exact Nat.mod_eq_zero_of_dvd (h5eq ▸ this)
  obtain ⟨hA2e, hB2e⟩ := both_five_dvd_of_sum_fourth_mod5_zero hmod2
  obtain ⟨A3, hA3⟩ := hA2e
  obtain ⟨B3, hB3⟩ := hB2e
  have heq3src : (5 * A3) ^ 4 + (5 * B3) ^ 4 =
      5 ^ 5 * (25 * B3 + 2) ^ 13 := by
    have hB21 : 5 * B2 + 2 = 25 * B3 + 2 := by
      rw [hB3]
      have hmul : 5 * (5 * B3) = 25 * B3 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA3, ← hB3, ← hB21]; exact h5eq
  have heq3 : 625 * (A3 ^ 4 + B3 ^ 4) =
      5 ^ 5 * (25 * B3 + 2) ^ 13 := by
    rw [← sum_fourth_of_mul_five]; exact heq3src
  have h1eq : A3 ^ 4 + B3 ^ 4 = 5 * (25 * B3 + 2) ^ 13 := by
    have hpow : (5 : ℕ) ^ 5 = 625 * 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 625)
    rw [heq3, hpow, mul_assoc]
  have hmod3 : (A3 ^ 4 + B3 ^ 4) % 5 = 0 := by
    have : 5 ∣ 5 * (25 * B3 + 2) ^ 13 := dvd_mul_right _ _
    exact Nat.mod_eq_zero_of_dvd (h1eq ▸ this)
  obtain ⟨hA3e, hB3e⟩ := both_five_dvd_of_sum_fourth_mod5_zero hmod3
  obtain ⟨A4, hA4⟩ := hA3e
  obtain ⟨B4, hB4⟩ := hB3e
  have heq4src : (5 * A4) ^ 4 + (5 * B4) ^ 4 =
      5 * (125 * B4 + 2) ^ 13 := by
    have hB21 : 25 * B3 + 2 = 125 * B4 + 2 := by
      rw [hB4]
      have hmul : 25 * (5 * B4) = 125 * B4 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA4, ← hB4, ← hB21]; exact h1eq
  have heq4 : 625 * (A4 ^ 4 + B4 ^ 4) = 5 * (125 * B4 + 2) ^ 13 := by
    rw [← sum_fourth_of_mul_five]; exact heq4src
  have hlast : 125 * (A4 ^ 4 + B4 ^ 4) = (125 * B4 + 2) ^ 13 := by
    have hpow : (625 : ℕ) = 5 * 125 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 5)
    have hL : 5 * (125 * (A4 ^ 4 + B4 ^ 4)) =
        625 * (A4 ^ 4 + B4 ^ 4) := by
      rw [hpow, mul_assoc]
    rw [hL]
    exact heq4
  have hLmod : (125 * (A4 ^ 4 + B4 ^ 4)) % 5 = 0 := by
    have : 5 ∣ 125 * (A4 ^ 4 + B4 ^ 4) :=
      dvd_mul_of_dvd_left (by decide : 5 ∣ 125) _
    exact Nat.mod_eq_zero_of_dvd this
  have hRmod : (125 * B4 + 2) ^ 13 % 5 = 2 := by
    have hC : (125 * B4 + 2) % 5 = 2 := by
      rw [Nat.add_mod, Nat.mul_mod]
      norm_num
    rw [pow13_mod5, hC]
  have hmod : (125 * (A4 ^ 4 + B4 ^ 4)) % 5 =
      (125 * B4 + 2) ^ 13 % 5 := by rw [hlast]
  rw [hLmod, hRmod] at hmod
  exact (by decide : (0 : ℕ) ≠ 2) hmod

theorem five_not_dvd_B_of_sol {A B : ℕ}
    (h : is_gap10_sol A B) : ¬ 5 ∣ B :=
  fun h5 => no_sol_when_five_dvd_B_gap10 h h5

/-! ## Size: `A > B` for `B > 0`; `A ≠ 0` on every solution -/

theorem two_mul_B_pow_four_lt_add_ten_pow (B : ℕ) :
    2 * B ^ 4 < (B + 10) ^ 13 := by
  have h10 : 10 ≤ B + 10 := Nat.le_add_left 10 B
  have h2 : 2 ≤ B + 10 := le_trans (by decide : 2 ≤ 10) h10
  have h2pow : 2 ≤ 2 ^ 9 := by decide
  have h29 : 2 ^ 9 ≤ (B + 10) ^ 9 := Nat.pow_le_pow_left h2 9
  have h2le : 2 ≤ (B + 10) ^ 9 := le_trans h2pow h29
  have hBlt : B < B + 10 := Nat.lt_add_of_pos_right (by decide : 0 < (10 : ℕ))
  have hB4 : B ^ 4 < (B + 10) ^ 4 :=
    Nat.pow_lt_pow_left hBlt (by decide : 4 ≠ 0)
  have hle : 2 * B ^ 4 ≤ (B + 10) ^ 9 * B ^ 4 :=
    Nat.mul_le_mul_right (B ^ 4) h2le
  have hposC : 0 < B + 10 := Nat.add_pos_right B (by decide : 0 < 10)
  have hpos9 : 0 < (B + 10) ^ 9 := Nat.pos_pow_of_pos 9 hposC
  have hlt : (B + 10) ^ 9 * B ^ 4 < (B + 10) ^ 9 * (B + 10) ^ 4 :=
    Nat.mul_lt_mul_of_pos_left hB4 hpos9
  have hsum : (B + 10) ^ 9 * (B + 10) ^ 4 = (B + 10) ^ 13 := by
    rw [← pow_add]
  rw [← hsum]
  exact lt_of_le_of_lt hle hlt

theorem A_gt_B_of_sol {A B : ℕ}
    (h : is_gap10_sol A B) (_hB : 0 < B) : B < A := by
  by_contra hle
  have hAB : A ≤ B := Nat.not_lt.mp hle
  have hA4 : A ^ 4 ≤ B ^ 4 := Nat.pow_le_pow_left hAB 4
  have hsum : A ^ 4 + B ^ 4 ≤ 2 * B ^ 4 := by
    have := Nat.add_le_add hA4 (le_refl (B ^ 4))
    simpa [two_mul] using this
  have hlt := two_mul_B_pow_four_lt_add_ten_pow B
  have : A ^ 4 + B ^ 4 < (B + 10) ^ 13 := lt_of_le_of_lt hsum hlt
  exact (ne_of_lt this) h

theorem A_ne_zero_of_sol {A B : ℕ} (h : is_gap10_sol A B) : A ≠ 0 := by
  intro hA
  subst hA
  have heq : B ^ 4 = (B + 10) ^ 13 := by
    simpa [is_gap10_sol] using h
  by_cases hB : B = 0
  · subst hB
    exact (by decide : (0 : ℕ) ≠ 10000000000000) heq
  · have hpos : 0 < B := Nat.pos_of_ne_zero hB
    have hB4pos : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hpos
    have hlt1 : B ^ 4 < 2 * B ^ 4 := by
      have : 1 * B ^ 4 < 2 * B ^ 4 :=
        Nat.mul_lt_mul_of_pos_right (by decide : 1 < 2) hB4pos
      simpa using this
    have hlt2 := two_mul_B_pow_four_lt_add_ten_pow B
    exact (ne_of_lt (lt_trans hlt1 hlt2)) heq

theorem A_gt_one_of_sol_pos {A B : ℕ}
    (h : is_gap10_sol A B) (hB : 0 < B) : 1 < A :=
  Nat.lt_of_le_of_lt (Nat.succ_le_of_lt hB) (A_gt_B_of_sol h hB)


/-! ## Even `B`: three `/2` leave last-step `A₃⁴+B₃⁴=2(4B₃+5)¹³`.
    Even `B₃` dies as residue `10` mod 16. Last-step `B ≡ 1,3 mod 5`
    die. `5 ∣ B₃` dies by last-step 5-descent. Remaining last-step
    both-odd 5-free `B ≡ 2 ∨ 4` is not killed here. Do **not**
    prove `no_sol_when_even_B` / `B_odd_of_sol_gap10`. -/

def last_step_eq (A B : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = 2 * (4 * B + 5) ^ 13

theorem no_sol_last_when_even_B3 {A B : ℕ}
    (h : A ^ 4 + B ^ 4 = 2 * (4 * B + 5) ^ 13) (hBeven : Even B) :
    False := by
  obtain ⟨k, hk'⟩ := hBeven
  have hk : B = 2 * k := by rw [hk', two_mul]
  have hC : 4 * B + 5 = 8 * k + 5 := by
    rw [hk]
    have hmul : 4 * (2 * k) = 8 * k := by
      rw [← mul_assoc]; rfl
    rw [hmul]
  have hC8 : (4 * B + 5) % 8 = 5 := by
    rw [hC, Nat.add_mod, Nat.mul_mod]
    norm_num
  have hR : (2 * (4 * B + 5) ^ 13) % 16 = 10 :=
    BealMatveevBeal.BealGap2.two_mul_pow13_mod16_of_mod8_five hC8
  have hmod : (A ^ 4 + B ^ 4) % 16 =
      (2 * (4 * B + 5) ^ 13) % 16 := by rw [h]
  obtain h0 | h1 | h2 := BealMatveevBeal.BealGap2.sum_fourth_mod16 A B
  · rw [h0, hR] at hmod
    exact (by decide : (0 : ℕ) ≠ 10) hmod
  · rw [h1, hR] at hmod
    exact (by decide : (1 : ℕ) ≠ 10) hmod
  · rw [h2, hR] at hmod
    exact (by decide : (2 : ℕ) ≠ 10) hmod

theorem fourth_pow_mod5_eq_one_of_not_dvd {n : ℕ} (h : ¬ 5 ∣ n) :
    n ^ 4 % 5 = 1 := by
  obtain h0 | h1 := fourth_pow_mod5 n
  · exact absurd (five_dvd_of_fourth_pow_mod_zero h0) h
  · exact h1

theorem no_sol_last_when_B_mod5_eq_one {A B : ℕ}
    (h : A ^ 4 + B ^ 4 = 2 * (4 * B + 5) ^ 13) (h1 : B % 5 = 1) :
    False := by
  have h5n : ¬ 5 ∣ B := by
    intro hd
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [h1] at this
    exact (by decide : (1 : ℕ) ≠ 0) this
  have hB4 : B ^ 4 % 5 = 1 := fourth_pow_mod5_eq_one_of_not_dvd h5n
  have hC : (4 * B + 5) % 5 = 4 := by
    calc (4 * B + 5) % 5
        = ((4 * B) % 5 + 5 % 5) % 5 := Nat.add_mod _ _ _
      _ = ((4 * B) % 5 + 0) % 5 := by rw [Nat.mod_self]
      _ = (4 * B) % 5 := by rw [Nat.add_zero, Nat.mod_mod]
      _ = (4 % 5 * (B % 5)) % 5 := Nat.mul_mod _ _ _
      _ = (4 * 1) % 5 := by rw [h1]
      _ = 4 := rfl
  have hC13 : (4 * B + 5) ^ 13 % 5 = 4 := by
    rw [pow13_mod5, hC]
  have hR : (2 * (4 * B + 5) ^ 13) % 5 = 3 := by
    calc (2 * (4 * B + 5) ^ 13) % 5
        = (2 % 5 * ((4 * B + 5) ^ 13 % 5)) % 5 := Nat.mul_mod _ _ _
      _ = (2 * 4) % 5 := by rw [hC13]
      _ = 3 := rfl
  have hsum : (A ^ 4 + B ^ 4) % 5 = (2 * (4 * B + 5) ^ 13) % 5 := by rw [h]
  obtain hA0 | hA1 := fourth_pow_mod5 A
  · have hL : (A ^ 4 + B ^ 4) % 5 = 1 := by
      rw [Nat.add_mod, hA0, hB4]
    rw [hL, hR] at hsum
    exact (by decide : (1 : ℕ) ≠ 3) hsum
  · have hL : (A ^ 4 + B ^ 4) % 5 = 2 := by
      rw [Nat.add_mod, hA1, hB4]
    rw [hL, hR] at hsum
    exact (by decide : (2 : ℕ) ≠ 3) hsum

theorem no_sol_last_when_B_mod5_eq_three {A B : ℕ}
    (h : A ^ 4 + B ^ 4 = 2 * (4 * B + 5) ^ 13) (h3 : B % 5 = 3) :
    False := by
  have h5n : ¬ 5 ∣ B := by
    intro hd
    have : B % 5 = 0 := Nat.mod_eq_zero_of_dvd hd
    rw [h3] at this
    exact (by decide : (3 : ℕ) ≠ 0) this
  have hB4 : B ^ 4 % 5 = 1 := fourth_pow_mod5_eq_one_of_not_dvd h5n
  have hC : (4 * B + 5) % 5 = 2 := by
    calc (4 * B + 5) % 5
        = ((4 * B) % 5 + 5 % 5) % 5 := Nat.add_mod _ _ _
      _ = ((4 * B) % 5 + 0) % 5 := by rw [Nat.mod_self]
      _ = (4 * B) % 5 := by rw [Nat.add_zero, Nat.mod_mod]
      _ = (4 % 5 * (B % 5)) % 5 := Nat.mul_mod _ _ _
      _ = (4 * 3) % 5 := by rw [h3]
      _ = 2 := rfl
  have hC13 : (4 * B + 5) ^ 13 % 5 = 2 := by
    rw [pow13_mod5, hC]
  have hR : (2 * (4 * B + 5) ^ 13) % 5 = 4 := by
    calc (2 * (4 * B + 5) ^ 13) % 5
        = (2 % 5 * ((4 * B + 5) ^ 13 % 5)) % 5 := Nat.mul_mod _ _ _
      _ = (2 * 2) % 5 := by rw [hC13]
      _ = 4 := rfl
  have hsum : (A ^ 4 + B ^ 4) % 5 = (2 * (4 * B + 5) ^ 13) % 5 := by rw [h]
  obtain hA0 | hA1 := fourth_pow_mod5 A
  · have hL : (A ^ 4 + B ^ 4) % 5 = 1 := by
      rw [Nat.add_mod, hA0, hB4]
    rw [hL, hR] at hsum
    exact (by decide : (1 : ℕ) ≠ 4) hsum
  · have hL : (A ^ 4 + B ^ 4) % 5 = 2 := by
      rw [Nat.add_mod, hA1, hB4]
    rw [hL, hR] at hsum
    exact (by decide : (2 : ℕ) ≠ 4) hsum

/-- Even original `B` reduces to a last-step pair after three `/2`. -/
theorem even_B_three_div2_last {A B : ℕ}
    (h : is_gap10_sol A B) (hBeven : Even B) :
    ∃ A3 B3 : ℕ, A3 ^ 4 + B3 ^ 4 = 2 * (4 * B3 + 5) ^ 13 := by
  have hAeven := A_even_of_sol_gap10 h
  obtain ⟨A1, hA'⟩ := hAeven
  obtain ⟨B1, hB'⟩ := hBeven
  have hA : A = 2 * A1 := by rw [hA', two_mul]
  have hB : B = 2 * B1 := by rw [hB', two_mul]
  have hC : B + 10 = 2 * (B1 + 5) := by
    rw [hB]; ring
  have hsol1 : (2 * A1) ^ 4 + (2 * B1) ^ 4 = (2 * (B1 + 5)) ^ 13 := by
    rw [← hA, ← hB, ← hC]; exact h
  have heq1 : 16 * (A1 ^ 4 + B1 ^ 4) = 2 ^ 13 * (B1 + 5) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two, hsol1, mul_pow]
  have h9 : A1 ^ 4 + B1 ^ 4 = 2 ^ 9 * (B1 + 5) ^ 13 := by
    have hpow : (2 : ℕ) ^ 13 = 16 * 2 ^ 9 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq1, hpow, mul_assoc]
  have h16 : (A1 ^ 4 + B1 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 9 * (B1 + 5) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 9) _
    exact Nat.mod_eq_zero_of_dvd (h9 ▸ this)
  obtain ⟨hA1e, hB1e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16
  obtain ⟨A2, hA2'⟩ := hA1e
  obtain ⟨B2, hB2'⟩ := hB1e
  have hA2 : A1 = 2 * A2 := by rw [hA2', two_mul]
  have hB2 : B1 = 2 * B2 := by rw [hB2', two_mul]
  have heq2src : (2 * A2) ^ 4 + (2 * B2) ^ 4 =
      2 ^ 9 * (2 * B2 + 5) ^ 13 := by
    rw [← hA2, ← hB2]; exact h9
  have heq2 : 16 * (A2 ^ 4 + B2 ^ 4) = 2 ^ 9 * (2 * B2 + 5) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq2src
  have h5p : A2 ^ 4 + B2 ^ 4 = 2 ^ 5 * (2 * B2 + 5) ^ 13 := by
    have hpow : (2 : ℕ) ^ 9 = 16 * 2 ^ 5 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq2, hpow, mul_assoc]
  have h16' : (A2 ^ 4 + B2 ^ 4) % 16 = 0 := by
    have : 16 ∣ 2 ^ 5 * (2 * B2 + 5) ^ 13 :=
      dvd_mul_of_dvd_left (by decide : 16 ∣ 2 ^ 5) _
    exact Nat.mod_eq_zero_of_dvd (h5p ▸ this)
  obtain ⟨hA2e, hB2e⟩ :=
    BealMatveevBeal.BealGap2.both_even_of_sum_fourth_mod16_zero h16'
  obtain ⟨A3, hA3'⟩ := hA2e
  obtain ⟨B3, hB3'⟩ := hB2e
  have hA3 : A2 = 2 * A3 := by rw [hA3', two_mul]
  have hB3 : B2 = 2 * B3 := by rw [hB3', two_mul]
  have heq3src : (2 * A3) ^ 4 + (2 * B3) ^ 4 =
      2 ^ 5 * (4 * B3 + 5) ^ 13 := by
    have hB21 : 2 * B2 + 5 = 4 * B3 + 5 := by
      rw [hB3]
      have hmul : 2 * (2 * B3) = 4 * B3 := by
        rw [← mul_assoc]; rfl
      rw [hmul]
    rw [← hA3, ← hB3, ← hB21]
    exact h5p
  have heq3 : 16 * (A3 ^ 4 + B3 ^ 4) = 2 ^ 5 * (4 * B3 + 5) ^ 13 := by
    rw [← BealMatveevBeal.BealGap2.sum_fourth_of_mul_two]; exact heq3src
  have hlast : A3 ^ 4 + B3 ^ 4 = 2 * (4 * B3 + 5) ^ 13 := by
    have hpow : (2 : ℕ) ^ 5 = 16 * 2 := by norm_num
    apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 16)
    rw [heq3, hpow, mul_assoc]
  exact ⟨A3, B3, hlast⟩

/-- Last-step leftover after even-`B₃`, `5 ∣ B₃`, and residues `1,3`. -/
theorem even_B_last_step_remaining {A B : ℕ}
    (h : is_gap10_sol A B) (hBeven : Even B) :
    ∃ A3 B3 : ℕ,
      A3 ^ 4 + B3 ^ 4 = 2 * (4 * B3 + 5) ^ 13 ∧
        Odd B3 ∧ ¬ 5 ∣ B3 ∧ (B3 % 5 = 2 ∨ B3 % 5 = 4) := by
  obtain ⟨A3, B3, hlast⟩ := even_B_three_div2_last h hBeven
  have hodd : Odd B3 := by
    rw [← Nat.not_even_iff_odd]
    intro he
    exact no_sol_last_when_even_B3 hlast he
  have h5n : ¬ 5 ∣ B3 := fun h5 => no_sol_when_five_dvd_last hlast h5
  have hmod : B3 % 5 = 1 ∨ B3 % 5 = 2 ∨ B3 % 5 = 3 ∨ B3 % 5 = 4 := by
    have hlt : B3 % 5 < 5 := Nat.mod_lt B3 (by decide : 0 < 5)
    have hne0 : B3 % 5 ≠ 0 := by
      intro hz
      exact h5n (Nat.dvd_of_mod_eq_zero hz)
    omega
  rcases hmod with h1 | h2 | h3 | h4
  · exact (no_sol_last_when_B_mod5_eq_one hlast h1).elim
  · exact ⟨A3, B3, hlast, hodd, h5n, Or.inl h2⟩
  · exact (no_sol_last_when_B_mod5_eq_three hlast h3).elim
  · exact ⟨A3, B3, hlast, hodd, h5n, Or.inr h4⟩

/-! ## Coprimeness on odd `B` -/

theorem gcd_A_B_eq_one_of_odd_B {A B : ℕ}
    (h : is_gap10_sol A B) (hBodd : Odd B) : Nat.gcd A B = 1 := by
  have h5n := five_not_dvd_B_of_sol h
  set d := Nat.gcd A B
  have hdA : d ∣ A := Nat.gcd_dvd_left A B
  have hdB : d ∣ B := Nat.gcd_dvd_right A B
  have hdC13 : d ∣ (B + 10) ^ 13 := by
    have hA4 : d ∣ A ^ 4 := dvd_pow hdA (by decide)
    have hB4 : d ∣ B ^ 4 := dvd_pow hdB (by decide)
    have hsum : d ∣ A ^ 4 + B ^ 4 := Nat.dvd_add hA4 hB4
    simpa [is_gap10_sol] using (h ▸ hsum)
  have hgcd10 : Nat.gcd d (B + 10) ∣ 10 := by
    have h1 : Nat.gcd d (B + 10) ∣ B :=
      dvd_trans (Nat.gcd_dvd_left d (B + 10)) hdB
    have h2 : Nat.gcd d (B + 10) ∣ (B + 10) := Nat.gcd_dvd_right d (B + 10)
    exact dvd_trans (Nat.dvd_gcd h1 h2) (gcd_B_C_dvd_ten B)
  have hgcd1 : Nat.gcd d (B + 10) = 1 := by
    by_contra hne
    have hpos : 1 < Nat.gcd d (B + 10) :=
      Nat.lt_of_le_of_ne (Nat.succ_le_of_lt
        (Nat.gcd_pos_of_pos_right d (Nat.add_pos_right B (by decide : 0 < 10))))
        (Ne.symm hne)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (ne_of_gt hpos)
    have hp10 : p ∣ 10 := dvd_trans hpd hgcd10
    have hp25 : p = 2 ∨ p = 5 := by
      have hmul : p ∣ 2 * 5 := by simpa using hp10
      rcases (Nat.Prime.dvd_mul hp).1 hmul with hp2 | hp5
      · have : p = 1 ∨ p = 2 := (Nat.dvd_prime Nat.prime_two).1 hp2
        exact Or.inl (this.resolve_left hp.ne_one)
      · have : p = 1 ∨ p = 5 := (Nat.dvd_prime Nat.prime_five).1 hp5
        exact Or.inr (this.resolve_left hp.ne_one)
    have hdP : p ∣ d := dvd_trans hpd (Nat.gcd_dvd_left d (B + 10))
    rcases hp25 with hp2 | hp5
    · have hd2 : 2 ∣ d := by rwa [← hp2]
      have h2B : 2 ∣ B := dvd_trans hd2 hdB
      exact absurd (even_iff_two_dvd.2 h2B) (Nat.not_even_iff_odd.2 hBodd)
    · have hd5 : 5 ∣ d := by rwa [← hp5]
      have h5B : 5 ∣ B := dvd_trans hd5 hdB
      exact h5n h5B
  have hcop : Nat.Coprime d (B + 10) := hgcd1
  have hcop13 : Nat.Coprime d ((B + 10) ^ 13) := hcop.pow_right 13
  have hd1 : d ∣ 1 := by
    have := Nat.dvd_gcd (dvd_refl d) hdC13
    rwa [show Nat.gcd d ((B + 10) ^ 13) = 1 from hcop13] at this
  exact Nat.eq_one_of_dvd_one hd1

theorem gcd_A_B_eq_one_of_sol {A B : ℕ}
    (h : is_gap10_sol A B) (hBodd : Odd B) : Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_odd_B h hBodd

theorem coprime_of_sol_gap10 {A B : ℕ}
    (h : is_gap10_sol A B) (hBodd : Odd B) : Nat.Coprime A B :=
  gcd_A_B_eq_one_of_odd_B h hBodd

theorem gcd_A_B_eq_one_of_remaining_gap10 {A B : ℕ}
    (h : is_gap10_sol A B) (hBodd : Odd B) (_h5 : ¬ 5 ∣ B) :
    Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_odd_B h hBodd

theorem coprime_of_remaining_gap10 {A B : ℕ}
    (h : is_gap10_sol A B) (hBodd : Odd B) (h5 : ¬ 5 ∣ B) :
    Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_remaining_gap10 h hBodd h5

/-! ## Linear form `Λ = 4 log A − 13 log(B+10)` -/

noncomputable def Lambda_gap10 (A B : ℕ) : ℝ :=
  4 * log (A : ℝ) - 13 * log ((B + 10 : ℕ) : ℝ)

theorem A_pow_four_eq_sub {A B : ℕ} (h : is_gap10_sol A B) :
    A ^ 4 = (B + 10) ^ 13 - B ^ 4 := by
  rw [← h, add_comm, Nat.add_sub_cancel_left]

theorem A_pow_real_add {A B : ℕ} (h : is_gap10_sol A B) :
    (A : ℝ) ^ 4 + (B : ℝ) ^ 4 = ((B + 10 : ℕ) : ℝ) ^ 13 := by
  have h' : ((A ^ 4 + B ^ 4 : ℕ) : ℝ) = (((B + 10) ^ 13 : ℕ) : ℝ) :=
    congrArg (fun n : ℕ => (n : ℝ)) h
  simpa [Nat.cast_add, Nat.cast_pow] using h'

theorem A_pow_pos_of_sol {A B : ℕ} (h : is_gap10_sol A B) :
    (0 : ℝ) < (A : ℝ) ^ 4 := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  exact pow_pos hApos 4

theorem Lambda_gap10_eq_log_div {A B : ℕ}
    (h : is_gap10_sol A B) :
    Lambda_gap10 A B =
      log ((A : ℝ) ^ 4 / ((B + 10 : ℕ) : ℝ) ^ 13) := by
  have hA : 0 < A := Nat.pos_of_ne_zero (A_ne_zero_of_sol h)
  have hApos : (0 : ℝ) < (A : ℝ) := by exact_mod_cast hA
  have hCpos : (0 : ℝ) < ((B + 10 : ℕ) : ℝ) := by
    have : 0 < B + 10 := Nat.add_pos_right B (by decide : 0 < 10)
    exact_mod_cast this
  unfold Lambda_gap10
  have h4 : (4 : ℝ) * log (A : ℝ) = log ((A : ℝ) ^ 4) :=
    (Real.log_pow (A : ℝ) 4).symm
  have h13 : (13 : ℝ) * log ((B + 10 : ℕ) : ℝ) =
      log (((B + 10 : ℕ) : ℝ) ^ 13) :=
    (Real.log_pow ((B + 10 : ℕ) : ℝ) 13).symm
  rw [h4, h13, Real.log_div (pow_pos hApos 4).ne' (pow_pos hCpos 13).ne']

theorem abs_Lambda_gap10_eq_log_one_plus {A B : ℕ}
    (h : is_gap10_sol A B) (hB : 0 < B) :
    |Lambda_gap10 A B| = log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hu : (0 : ℝ) < (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    div_pos (pow_pos hBpos 4) hA4pos
  have hsum := A_pow_real_add h
  have hratio :
      (A : ℝ) ^ 4 / ((B + 10 : ℕ) : ℝ) ^ 13 =
        1 / (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    have hne : (A : ℝ) ^ 4 ≠ 0 := hA4pos.ne'
    have hden :
        (1 : ℝ) + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 =
          ((A : ℝ) ^ 4 + (B : ℝ) ^ 4) / (A : ℝ) ^ 4 := by
      field_simp [hne]
    rw [hden, one_div_div, hsum]
  have hΛ := Lambda_gap10_eq_log_div h
  have h1u : (0 : ℝ) < 1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
    add_pos_of_nonneg_of_pos zero_le_one hu
  have hlog :
      Lambda_gap10 A B = -log (1 + (B : ℝ) ^ 4 / (A : ℝ) ^ 4) := by
    rw [hΛ, hratio, Real.log_div one_ne_zero h1u.ne', log_one, zero_sub]
  rw [hlog, abs_neg, abs_of_nonneg (log_nonneg (le_of_lt (lt_add_of_pos_right 1 hu)))]

theorem abs_Lambda_gap10_le_ratio {A B : ℕ}
    (h : is_gap10_sol A B) (hB : 0 < B) :
    |Lambda_gap10 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
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
  rwa [abs_Lambda_gap10_eq_log_one_plus h hB]

theorem B_pow_five_add_B_pow_four_lt_add_ten_pow {B : ℕ} (_hB : 0 < B) :
    (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 10 : ℕ) : ℝ) ^ 13 := by
  have hx : (0 : ℝ) ≤ (B : ℝ) := Nat.cast_nonneg B
  have hC : ((B + 10 : ℕ) : ℝ) = (B : ℝ) + 10 := by
    rw [Nat.cast_add]
    norm_num
  have h5 : (B : ℝ) ^ 5 + (B : ℝ) ^ 4 < ((B + 10 : ℕ) : ℝ) ^ 5 := by
    rw [hC]
    have hexp : ((B : ℝ) + 10) ^ 5 =
        (B : ℝ) ^ 5 + 50 * (B : ℝ) ^ 4 + 1000 * (B : ℝ) ^ 3 +
          10000 * (B : ℝ) ^ 2 + 50000 * (B : ℝ) + 100000 := by
      ring
    have h3 : (0 : ℝ) ≤ (B : ℝ) ^ 3 := pow_nonneg hx 3
    have h2 : (0 : ℝ) ≤ (B : ℝ) ^ 2 := sq_nonneg _
    nlinarith [hexp, h3, h2, hx]
  have hC1 : (1 : ℝ) ≤ ((B + 10 : ℕ) : ℝ) := by
    have : 1 ≤ B + 10 := le_trans (by decide : 1 ≤ 10) (Nat.le_add_left 10 B)
    exact_mod_cast this
  have h513 : ((B + 10 : ℕ) : ℝ) ^ 5 ≤ ((B + 10 : ℕ) : ℝ) ^ 13 :=
    pow_le_pow_right hC1 (by decide : (5 : ℕ) ≤ 13)
  exact lt_of_lt_of_le h5 h513

theorem A_pow_gt_B_pow_five {A B : ℕ}
    (h : is_gap10_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 5 < (A : ℝ) ^ 4 := by
  have hA4 : (A : ℝ) ^ 4 =
      ((B + 10 : ℕ) : ℝ) ^ 13 - (B : ℝ) ^ 4 := by
    linarith [A_pow_real_add h]
  have hsum := B_pow_five_add_B_pow_four_lt_add_ten_pow hB
  linarith [hA4, hsum]

theorem ratio_lt_inv_B {A B : ℕ}
    (h : is_gap10_sol A B) (hB : 0 < B) :
    (B : ℝ) ^ 4 / (A : ℝ) ^ 4 < 1 / (B : ℝ) := by
  have hA4pos := A_pow_pos_of_sol h
  have hBpos : (0 : ℝ) < (B : ℝ) := by exact_mod_cast hB
  have hgt := A_pow_gt_B_pow_five h hB
  have : (B : ℝ) ^ 4 * (B : ℝ) < (A : ℝ) ^ 4 := by
    have : (B : ℝ) ^ 5 = (B : ℝ) ^ 4 * (B : ℝ) := by ring
    rwa [this] at hgt
  rw [div_lt_div_iff hA4pos hBpos, one_mul]
  exact this

theorem abs_Lambda_gap10_lt_inv_B {A B : ℕ}
    (h : is_gap10_sol A B) (hB : 0 < B) :
    |Lambda_gap10 A B| < 1 / (B : ℝ) :=
  lt_of_le_of_lt (abs_Lambda_gap10_le_ratio h hB) (ratio_lt_inv_B h hB)

theorem A_pow_lt_C_pow {A B : ℕ}
    (h : is_gap10_sol A B) (hB : 0 < B) :
    (A : ℝ) ^ 4 < ((B + 10 : ℕ) : ℝ) ^ 13 := by
  have hB4 : 0 < B ^ 4 := Nat.pos_pow_of_pos 4 hB
  have hlt : A ^ 4 < (B + 10) ^ 13 :=
    calc
      A ^ 4 < A ^ 4 + B ^ 4 := Nat.lt_add_of_pos_right hB4
      _ = (B + 10) ^ 13 := h
  exact_mod_cast hlt

/-! ## Log-method no-go (`C1 ≥ 1` loses to `B⁴/A⁴`) -/

theorem logA_gt_thirteen_of_B_ge_B0 {A B : ℕ}
    (h : is_gap10_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
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
    a gap-10 solution with `B ≥ B0`. Same cutoff as `62383af`:
    `C1 < 1` would be needed. -/
theorem hGen_exp_lt_ratio_gap10
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {A B : ℕ} (hsol : is_gap10_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + 10 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  set a : ℝ := log (A : ℝ)
  set c : ℝ := log ((B + 10 : ℕ) : ℝ)
  set C : ℝ := ((B + 10 : ℕ) : ℝ)
  have hAgt1 : 1 < A := A_gt_one_of_sol_pos hsol hB
  have hCgt1 : 1 < B + 10 :=
    lt_of_lt_of_le (by decide : 1 < 10) (Nat.le_add_left 10 B)
  have hApos : (0 : ℝ) < (A : ℝ) := by
    have : (0 : ℕ) < A := lt_trans Nat.zero_lt_one hAgt1
    exact_mod_cast this
  have hCpos : (0 : ℝ) < C := by
    have : 0 < B + 10 := Nat.add_pos_right B (by decide : 0 < 10)
    have : (0 : ℝ) < ((B + 10 : ℕ) : ℝ) := by exact_mod_cast this
    simpa [C] using this
  have hCgt : (1 : ℝ) < C := by
    have : (1 : ℝ) < ((B + 10 : ℕ) : ℝ) := by exact_mod_cast hCgt1
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

theorem C1_floor_hGen_loses_gap10 {A B : ℕ}
    (hsol : is_gap10_sol A B) (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + 10 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio_gap10
    (le_of_lt (by
      simpa [C1_floor_eq_logs] using
        BealMatveevBeal.MatveevThreeLogs.C1_floor_gt_one))
    hsol hB hB0

/-! ## Floor form / LLL no-go (`B+8`) -/

noncomputable def floorFormThird_gap10 (C : ℝ) (A B : ℕ) : ℝ :=
  (4 : ℝ) * ⌊C * log (A : ℝ)⌋ - 13 * ⌊C * log ((B + 10 : ℕ) : ℝ)⌋

/-- `|4⌊C log A⌋ − 13⌊C log(B+8)⌋ − C Λ| < 17` for every real `C`. -/
theorem floor_form_approx_of_C_gap10 (C : ℝ) (A B : ℕ) :
    |floorFormThird_gap10 C A B - C * Lambda_gap10 A B| < 17 := by
  set a : ℝ := C * log (A : ℝ)
  set cval : ℝ := C * log ((B + 10 : ℕ) : ℝ)
  have hΛ : C * Lambda_gap10 A B = 4 * a - 13 * cval := by
    simp only [Lambda_gap10, a, cval]
    ring
  have hft : floorFormThird_gap10 C A B = (4 : ℝ) * ⌊a⌋ - 13 * ⌊cval⌋ := rfl
  have hform :
      floorFormThird_gap10 C A B - C * Lambda_gap10 A B =
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

theorem floor_form_third_abs_lt_gap10 {C : ℝ} (hC : 0 < C) (A B : ℕ) :
    |floorFormThird_gap10 C A B| < 17 + C * |Lambda_gap10 A B| := by
  have happ := floor_form_approx_of_C_gap10 C A B
  have hmul : |C * Lambda_gap10 A B| = C * |Lambda_gap10 A B| := by
    rw [abs_mul, abs_of_pos hC]
  have := abs_sub_abs_le_abs_sub
    (floorFormThird_gap10 C A B) (C * Lambda_gap10 A B)
  linarith [happ, this, hmul]

/-- No scaling `C > 0` yields a Baker–Davenport witness
    `r > 17 + C/B0` on a gap-10 solution with `B ≥ B0`. -/
theorem hLLL_method_fails_gap10 :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        is_gap10_sol A B →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |floorFormThird_gap10 C A B| := by
  intro C hC A B hsol hB hB0
  rintro ⟨r, hgt, hle⟩
  have htri := floor_form_third_abs_lt_gap10 hC A B
  have hLam := abs_Lambda_gap10_lt_inv_B hsol hB
  have hB0pos : (0 : ℝ) < (B0_nat : ℝ) := by
    have : (0 : ℕ) < B0_nat := by decide
    exact_mod_cast this
  have hBle : (B0_nat : ℝ) ≤ (B : ℝ) := Nat.cast_le.mpr hB0
  have hCΛ : C * |Lambda_gap10 A B| < C / (B0_nat : ℝ) := by
    have hmid : C * |Lambda_gap10 A B| < C * (1 / (B : ℝ)) :=
      mul_lt_mul_of_pos_left hLam hC
    have hrew : C * (1 / (B : ℝ)) = C / (B : ℝ) := mul_one_div _ _
    have hCB : C / (B : ℝ) ≤ C / (B0_nat : ℝ) :=
      div_le_div_of_nonneg_left (le_of_lt hC) hB0pos hBle
    linarith [hmid, hrew, hCB]
  have hthird : |floorFormThird_gap10 C A B| < 17 + C / (B0_nat : ℝ) := by
    linarith [htri, hCΛ]
  linarith [hgt, hle, hthird]

theorem no_uniform_c_cubic_in_N_gap10 :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (BealMatveevBeal.MatveevThreeLogs.coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) :=
  BealMatveevBeal.MatveevThreeLogs.no_uniform_c_cubic_in_N

theorem coeffCount3_zero_ten_ten_ten_gap10 :
    BealMatveevBeal.MatveevThreeLogs.coeffCount3 0 10 10 10 = 1331 :=
  BealMatveevBeal.MatveevThreeLogs.coeffCount3_zero_ten_ten_ten

theorem no_uniform_c_easy_half_gap10 :
    (1 / 2 : ℝ) * 1 * 1 < 242 := by
  norm_num

/-! ## `hGen_gap10` / `hLLL_gap10` stay `def Prop` -/

/-- Matveev 2000 Theorem 1.4, n=2, displayed `C1_floor` exponential
    on a gap-10 solution. Not in Mathlib 4.12. Instantiating it at
    `B ≥ B0` does not beat `B⁴/A⁴`. -/
def hGen_gap10 : Prop :=
  ∀ A B : ℕ,
    is_gap10_sol A B →
      0 < B →
        |Lambda_gap10 A B| >
          exp (-(C1_floor : ℝ) * log (A : ℝ) *
            log ((B + 10 : ℕ) : ℝ))

/-- Bugeaud / LLL close for gap-10: ratio upper bound ⇒ `B ≤ B0`.
    The displayed lattice does not inhabit it. -/
def hLLL_gap10 : Prop :=
  (∀ A B : ℕ, is_gap10_sol A B → 0 < B →
      |Lambda_gap10 A B| ≤ (B : ℝ) ^ 4 / (A : ℝ) ^ 4) →
    baker_bound_gap10

def baker_bound_gap10_of_hGen_hLLL : Prop :=
  hGen_gap10 → hLLL_gap10 → baker_bound_gap10

def baker_bound_gap10_of_hGen_hLLL_gap10 : Prop :=
  baker_bound_gap10_of_hGen_hLLL


/-! ## Combined unconditional no-go (no Darmon–Merel axiom) -/

/-- Log and LLL methods lose on `B ≥ B0`. `A` is even. `5 ∣ B`
    and `7 ∣ B` are impossible. `3 ∣ B` is compatible (`A⁴ ≡ 1`).
    On odd `B` the pair is coprime and Darmon–Merel `(4,4,13)`
    would be refuted. Even `B` reduces to last-step both-odd
    5-free `B₃ ≡ 2 ∨ 4`, which is not killed here.
    `baker_bound_gap10` stays uninhabited as a named theorem. -/
theorem baker_bound_gap10_unconditional_nogo {A B : ℕ}
    (hsol : is_gap10_sol A B)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + 10 : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (∀ C : ℝ, 0 < C →
      ¬ ∃ r : ℝ,
        17 + C / (B0_nat : ℝ) < r ∧
          r ≤ |floorFormThird_gap10 C A B|) ∧
    B0_nat < A ∧
    Even A ∧
    ¬ 5 ∣ B ∧
    ¬ 7 ∣ B ∧
    (Odd B → Nat.Coprime A B) ∧
    (Odd B → A ^ 4 % 3 = 1 ∨ ¬ 3 ∣ B) ∧
    (Odd B → darmon_merel_44_13_no_coprime → False) := by
  refine ⟨?_, ?_, ?_, A_even_of_sol_gap10 hsol,
    five_not_dvd_B_of_sol hsol, seven_not_dvd_B_of_sol hsol, ?_, ?_, ?_⟩
  · intro C1 hC1
    exact hGen_exp_lt_ratio_gap10 hC1 hsol hB hB0
  · intro C hC
    exact hLLL_method_fails_gap10 C hC A B hsol hB hB0
  · exact Nat.lt_of_le_of_lt hB0 (A_gt_B_of_sol hsol hB)
  · intro hOdd
    exact coprime_of_sol_gap10 hsol hOdd
  · intro _hOdd
    by_cases h3 : 3 ∣ B
    · exact Or.inl (A_pow_four_mod3_eq_one_of_three_dvd_B hsol h3)
    · exact Or.inr h3
  · intro hOdd hDM
    have hA0 : A = 0 ∨ B = 0 :=
      hDM A B (B + 10) (coprime_of_sol_gap10 hsol hOdd) hsol
    cases hA0 with
    | inl hA => exact A_ne_zero_of_sol hsol hA
    | inr hB0' => exact (ne_of_gt hB) hB0'

/-! ## Axiom-relative close on odd `B` (reuses `BealTrueV25`) -/

/-- Every gap-10 solution with odd `B` is impossible relative to
    `darmon_merel_4413_axiom`. Even `B` is not claimed. -/
theorem no_gap10_of_odd_B_of_axiom {A B : ℕ}
    (hsol : is_gap10_sol A B) (hOdd : Odd B) : False := by
  have hDM := BealMatveevBeal.BealTrueV25.darmon_merel_4413_axiom
  have hA0 : A = 0 ∨ B = 0 :=
    hDM A B (B + 10) (coprime_of_sol_gap10 hsol hOdd) hsol
  cases hA0 with
  | inl hA => exact A_ne_zero_of_sol hsol hA
  | inr hB0 =>
      subst hB0
      exact Nat.not_even_iff_odd.2 hOdd (by decide : Even 0)

theorem no_gap10_of_axiom {A B : ℕ}
    (hsol : is_gap10_sol A B) (hOdd : Odd B) : False :=
  no_gap10_of_odd_B_of_axiom hsol hOdd

/-- Vacuous `B ≤ B0` for every odd-`B` gap-10 solution, relative
    to the existing Darmon–Merel axiom. Not named `baker_bound_gap10`. -/
theorem baker_bound_gap10_true {A B : ℕ}
    (hsol : is_gap10_sol A B) (hOdd : Odd B) : B ≤ B0_nat :=
  (no_gap10_of_axiom hsol hOdd).elim

theorem baker_bound_gap10_true_of_axiom {A B : ℕ}
    (hsol : is_gap10_sol A B) (hOdd : Odd B) : B ≤ B0_nat :=
  baker_bound_gap10_true hsol hOdd

#check C1_floor_eq
#check B0_nat_eq
#check not_gap10_one_zero
#check gcd_B_C_eq_gcd_ten
#check gcd_B_C_dvd_ten
#check gcd_A_B_eq_one_of_sol
#check gcd_A_B_eq_one_of_odd_B
#check coprime_of_sol_gap10
#check A_even_of_sol_gap10
#check A_gt_B_of_sol
#check A_pow_four_mod3_eq_one_of_three_dvd_B
#check no_sol_when_five_dvd_B_gap10
#check five_dvd_B_forces_five_dvd_A_gap10
#check no_sol_when_seven_dvd_B_gap10
#check even_B_three_div2_last
#check even_B_last_step_remaining
#check no_sol_last_when_even_B3
#check no_sol_when_five_dvd_last
#check re13_gt_of_middle_cone
#check re13_ne_zero_of_int_ne_zero
#check hGen_exp_lt_ratio_gap10
#check C1_floor_hGen_loses_gap10
#check floor_form_approx_of_C_gap10
#check hLLL_method_fails_gap10
#check no_uniform_c_cubic_in_N_gap10
#check no_uniform_c_easy_half_gap10
#check hGen_gap10
#check hLLL_gap10
#check baker_bound_gap10_of_hGen_hLLL
#check baker_bound_gap10_unconditional_nogo
#check baker_bound_gap10
#check no_gap10_of_axiom
#check baker_bound_gap10_true
#check baker_bound_gap10_true_of_axiom
#print axioms gcd_A_B_eq_one_of_odd_B
#print axioms no_sol_when_five_dvd_B_gap10
#print axioms no_sol_when_seven_dvd_B_gap10
#print axioms even_B_three_div2_last
#print axioms BealMatveevBeal.BealGap1.fourth_pow_mod5
#print axioms even_B_last_step_remaining
#print axioms no_sol_last_when_even_B3
#print axioms no_sol_when_five_dvd_last
#print axioms no_sol_last_when_B_mod5_eq_one
#print axioms no_sol_last_when_B_mod5_eq_three
#print axioms hGen_exp_lt_ratio_gap10
#print axioms C1_floor_hGen_loses_gap10
#print axioms hLLL_method_fails_gap10
#print axioms baker_bound_gap10_unconditional_nogo
#print axioms no_gap10_of_axiom
#print axioms baker_bound_gap10_true

end BealMatveevBeal.BealGap10
