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
import MatveevThreeLogs
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

/-!
# Displayed Frey curve / Kraus no-go (not a `B ≤ 10⁶` close)

Successor of `62383af` (`v24-v24x-final-logs-nogo`).
The displayed model `y² = x(x − A⁴)(x + B⁴)` has discriminant
`16 A⁸ B⁸ (A⁴+B⁴)²`, hence `16 A⁸ B⁸ (B+3)²⁶` on a gap-3
solution. Ribet at `p = 13` would remove primes `ℓ` with
`13 ∣ v_ℓ(Δ)`. Here `v_C(Δ) = 26 v_C(C)` (when `C` is coprime
to `2AB`) and `13 ∣ 26`, so `C = B+3` **is** a lowering
candidate — the residual level is **not** forced to grow with
`C`. By contrast `v_A(Δ) = 8 v_A(A)` and `13 ∤ 8`, so a prime
`p ∤ 6` dividing `A` is removed only if `13 ∣ v_p(A)`. That is
the opposite of Fermat, where every prime in `ABC` has
`p ∣ v_ℓ(Δ)`. This curve does not produce a uniform level-`32`
newform check, and Mathlib 4.12 has no Ribet / Darmon–Merel /
Kraus newform table.

`baker_bound_gap3` stays uninhabited `def Prop`. Not v25.
`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

open Nat

namespace BealMatveevBeal.BealKraus

open BealMatveevBeal.MatveevThreeLogs
open BealLevel26Foundations.BealGap3BakerUpperBound

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_threeLogs :
    C1_floor = BealMatveevBeal.MatveevThreeLogs.C1_floor := rfl

theorem B0_nat_eq_threeLogs :
    B0_nat = BealMatveevBeal.MatveevThreeLogs.B0_nat := rfl

/-! ## Gap-3 gcd and parity -/

theorem gcd_B_C_eq_gcd_B_three (B : ℕ) :
    Nat.gcd B (B + 3) = Nat.gcd B 3 :=
  Nat.gcd_self_add_right B 3

theorem gcd_B_C_dvd_three (B : ℕ) :
    Nat.gcd B (B + 3) ∣ 3 := by
  rw [gcd_B_C_eq_gcd_B_three]
  exact Nat.gcd_dvd_right B 3

theorem prime_dvd_A_B_eq_three {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hpA : p ∣ A) (hpB : p ∣ B) : p = 3 := by
  have hpL : p ∣ A ^ 4 + B ^ 4 :=
    dvd_add (dvd_pow hpA (by decide)) (dvd_pow hpB (by decide))
  have hpC : p ∣ B + 3 :=
    hp.dvd_of_dvd_pow (hsol ▸ hpL)
  have hp3 : p ∣ 3 := by
    have hsub : p ∣ (B + 3) - B :=
      Nat.dvd_sub (Nat.le_add_right B 3) hpC hpB
    simpa [Nat.add_sub_cancel_left] using hsub
  exact (prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 hp3

theorem prime_dvd_A_C_eq_three {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hpA : p ∣ A) (hpC : p ∣ B + 3) : p = 3 := by
  have hpR : p ∣ (B + 3) ^ 13 := dvd_pow hpC (by decide)
  have hpA4 : p ∣ A ^ 4 := dvd_pow hpA (by decide)
  have hpB4 : p ∣ B ^ 4 := by
    have hsum : p ∣ A ^ 4 + B ^ 4 := hsol ▸ hpR
    have hsub : p ∣ (A ^ 4 + B ^ 4) - A ^ 4 :=
      Nat.dvd_sub (Nat.le_add_right _ _) hsum hpA4
    simpa [Nat.add_sub_cancel_left] using hsub
  have hpB : p ∣ B := hp.dvd_of_dvd_pow hpB4
  exact prime_dvd_A_B_eq_three hp hsol hpA hpB

theorem prime_dvd_six_iff {p : ℕ} (hp : p.Prime) :
    p ∣ 6 ↔ p = 2 ∨ p = 3 := by
  constructor
  · intro h
    have hmul : p ∣ 2 * 3 := by simpa using h
    rcases (Nat.Prime.dvd_mul hp).1 hmul with h2 | h3
    · exact Or.inl ((prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · exact Or.inr ((prime_dvd_prime_iff_eq hp (by decide : Nat.Prime 3)).1 h3)
  · rintro (rfl | rfl) <;> decide

theorem not_dvd_six_of_dvd_A {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hpA : p ∣ A) (hp6 : ¬ p ∣ 6) :
    ¬ p ∣ B ∧ ¬ p ∣ (B + 3) ∧ p ≠ 2 := by
  have hpne : ¬ (p = 2 ∨ p = 3) := by
    intro h
    exact hp6 ((prime_dvd_six_iff hp).2 h)
  have hpne2 : p ≠ 2 := fun h => hpne (Or.inl h)
  have hpne3 : p ≠ 3 := fun h => hpne (Or.inr h)
  refine ⟨fun hpB => hpne3 (prime_dvd_A_B_eq_three hp hsol hpA hpB),
    fun hpC => hpne3 (prime_dvd_A_C_eq_three hp hsol hpA hpC), hpne2⟩

theorem A_odd_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    Odd A := by
  rw [← Nat.not_even_iff_odd]
  intro hAeven
  have hA4 : Even (A ^ 4) := (even_pow' (by decide : 4 ≠ 0)).2 hAeven
  have h3 : Odd (3 : ℕ) := ⟨1, by decide⟩
  by_cases hBeven : Even B
  · have hB4 : Even (B ^ 4) := (even_pow' (by decide : 4 ≠ 0)).2 hBeven
    have hC : Odd (B + 3) := hBeven.add_odd h3
    have hC13 : Odd ((B + 3) ^ 13) := hC.pow
    have hL : Even (A ^ 4 + B ^ 4) := hA4.add hB4
    exact (Nat.not_even_iff_odd.2 (hsol ▸ hC13)) hL
  · have hBodd : Odd B := Nat.not_even_iff_odd.1 hBeven
    have hB4 : Odd (B ^ 4) := hBodd.pow
    have hC : Even (B + 3) := hBodd.add_odd h3
    have hC13 : Even ((B + 3) ^ 13) :=
      (even_pow' (by decide : 13 ≠ 0)).2 hC
    have hL : Odd (A ^ 4 + B ^ 4) := hA4.add_odd hB4
    exact (Nat.not_even_iff_odd.2 (hsol ▸ hL)) hC13

/-! ## Displayed Frey model -/

/-- `y² = x³ + (B⁴ − A⁴) x² − A⁴ B⁴ x`. -/
def freyWeierstrass (A B : ℕ) : WeierstrassCurve ℤ where
  a₁ := 0
  a₂ := (B : ℤ) ^ 4 - (A : ℤ) ^ 4
  a₃ := 0
  a₄ := -((A : ℤ) ^ 4 * (B : ℤ) ^ 4)
  a₆ := 0

/-- Natural-number discriminant of the displayed model
    `y² = x(x − A⁴)(x + B⁴)`. -/
def freyDiscNat (A B : ℕ) : ℕ :=
  16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2

structure FreyCurve where
  A : ℕ
  B : ℕ

def FreyCurve.C (E : FreyCurve) : ℕ := E.B + 3

def FreyCurve.discNat (E : FreyCurve) : ℕ :=
  freyDiscNat E.A E.B

theorem freyWeierstrass_Δ (A B : ℕ) :
    (freyWeierstrass A B).Δ =
      (16 : ℤ) * (A : ℤ) ^ 8 * (B : ℤ) ^ 8 *
        ((A : ℤ) ^ 4 + (B : ℤ) ^ 4) ^ 2 := by
  simp [freyWeierstrass, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  ring

theorem freyDiscNat_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    freyDiscNat A B = 16 * A ^ 8 * B ^ 8 * (B + 3) ^ 26 := by
  have hpow : ((B + 3) ^ 13) ^ 2 = (B + 3) ^ 26 := by
    rw [← pow_mul]
  rw [freyDiscNat, hsol, hpow]

/-! ## `13 ∣ 26` and `13 ∤ 8` -/

theorem thirteen_dvd_twenty_six : 13 ∣ 26 := by decide

theorem not_thirteen_dvd_eight : ¬ 13 ∣ 8 := by decide

theorem thirteen_dvd_eight_mul {k : ℕ} : 13 ∣ 8 * k ↔ 13 ∣ k := by
  constructor
  · intro h
    have hc : Coprime 13 8 := by decide
    exact hc.dvd_of_dvd_mul_left h
  · intro h
    exact Dvd.dvd.mul_left h 8

/-! ## `p`-adic valuations of `freyDiscNat` -/

theorem padicValNat_freyDiscNat {p A B : ℕ} (hp : p.Prime)
    (hA : A ≠ 0) (hB : B ≠ 0) :
    padicValNat p (freyDiscNat A B) =
      padicValNat p 16 + 8 * padicValNat p A + 8 * padicValNat p B +
        2 * padicValNat p (A ^ 4 + B ^ 4) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h16 : (16 : ℕ) ≠ 0 := by decide
  have hA8 : A ^ 8 ≠ 0 := pow_ne_zero 8 hA
  have hB8 : B ^ 8 ≠ 0 := pow_ne_zero 8 hB
  have hS : A ^ 4 + B ^ 4 ≠ 0 :=
    (Nat.add_pos_left (pos_pow_of_pos 4 (Nat.pos_of_ne_zero hA)) (B ^ 4)).ne'
  have hS2 : (A ^ 4 + B ^ 4) ^ 2 ≠ 0 := pow_ne_zero 2 hS
  have hassoc :
      16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2 =
        16 * (A ^ 8 * (B ^ 8 * (A ^ 4 + B ^ 4) ^ 2)) := by ring
  unfold freyDiscNat
  rw [hassoc, padicValNat.mul h16 (mul_ne_zero hA8 (mul_ne_zero hB8 hS2)),
    padicValNat.mul hA8 (mul_ne_zero hB8 hS2),
    padicValNat.mul hB8 hS2,
    padicValNat.pow 8 hA, padicValNat.pow 8 hB, padicValNat.pow 2 hS]
  ring

theorem padicValNat_sixteen_of_ne_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    padicValNat p 16 = 0 := by
  rw [padicValNat.eq_zero_iff]
  refine Or.inr (Or.inr ?_)
  intro h
  have hpow : p ∣ 2 ^ 4 := by
    simpa [show (16 : ℕ) = 2 ^ 4 from rfl] using h
  have : p ∣ 2 := hp.dvd_of_dvd_pow hpow
  exact hp2 ((prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

theorem padicValNat_freyDiscNat_at_A {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hp2 : p ≠ 2) (hpB : ¬ p ∣ B) (hpC : ¬ p ∣ (B + 3)) :
    padicValNat p (freyDiscNat A B) = 8 * padicValNat p A := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hvalB : padicValNat p B = 0 := by
    rw [padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr hpB)
  have hvalC : padicValNat p (B + 3) = 0 := by
    rw [padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr hpC)
  have hCne : B + 3 ≠ 0 := Nat.succ_ne_zero _
  have hvalS : padicValNat p (A ^ 4 + B ^ 4) = 0 := by
    rw [hsol, padicValNat.pow 13 hCne, hvalC]
  rw [padicValNat_freyDiscNat hp hA hB,
    padicValNat_sixteen_of_ne_two hp hp2, hvalB, hvalS]
  ring

theorem padicValNat_freyDiscNat_at_C {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hp2 : p ≠ 2) (hpA : ¬ p ∣ A) (hpB : ¬ p ∣ B) :
    padicValNat p (freyDiscNat A B) =
      26 * padicValNat p (B + 3) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hvalA : padicValNat p A = 0 := by
    rw [padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr hpA)
  have hvalB : padicValNat p B = 0 := by
    rw [padicValNat.eq_zero_iff]
    exact Or.inr (Or.inr hpB)
  have hCne : B + 3 ≠ 0 := Nat.succ_ne_zero _
  have hvalS : padicValNat p (A ^ 4 + B ^ 4) =
      13 * padicValNat p (B + 3) := by
    rw [hsol, padicValNat.pow 13 hCne]
  rw [padicValNat_freyDiscNat hp hA hB,
    padicValNat_sixteen_of_ne_two hp hp2, hvalA, hvalB, hvalS]
  ring

/-- A prime `p ∤ 6` dividing `A` is a Ribet-lowering candidate at `13`
    iff `13 ∣ v_p(A)`. In particular `13 ∤ 8` blocks the Fermat-style
    removal when `v_p(A)` is not a multiple of `13`. -/
theorem frey_A_not_ribet_lowered {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : A ≠ 0) (hB : 0 < B)
    (hp6 : ¬ p ∣ 6) (hpA : p ∣ A)
    (hnot13 : ¬ 13 ∣ padicValNat p A) :
    ¬ 13 ∣ padicValNat p (freyDiscNat A B) := by
  have hcop := not_dvd_six_of_dvd_A hp hsol hpA hp6
  have hBne : B ≠ 0 := Nat.pos_iff_ne_zero.mp hB
  have hval :=
    padicValNat_freyDiscNat_at_A hp hsol hA hBne hcop.2.2 hcop.1 hcop.2.1
  rw [hval, thirteen_dvd_eight_mul]
  exact hnot13

/-- `C = B+3` **is** a lowering candidate: `13 ∣ 26 v_p(C)` and
    the valuation is at least `26` when `p ∣ C`. -/
theorem frey_C_ribet_lowered_candidate {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hp2 : p ≠ 2) (hpA : ¬ p ∣ A) (hpB : ¬ p ∣ B)
    (hpC : p ∣ (B + 3)) :
    13 ∣ padicValNat p (freyDiscNat A B) ∧
      26 ≤ padicValNat p (freyDiscNat A B) := by
  have hval := padicValNat_freyDiscNat_at_C hp hsol hA hB hp2 hpA hpB
  have hCpos : padicValNat p (B + 3) ≠ 0 := by
    intro h0
    rw [padicValNat.eq_zero_iff] at h0
    rcases h0 with h1 | hn | hd
    · exact hp.ne_one h1
    · exact (Nat.succ_ne_zero _) hn
    · exact hd hpC
  have hge : 1 ≤ padicValNat p (B + 3) := Nat.succ_le_of_lt (Nat.pos_of_ne_zero hCpos)
  refine ⟨?_, ?_⟩
  · rw [hval]
    exact Dvd.dvd.mul_right thirteen_dvd_twenty_six _
  · rw [hval]
    exact Nat.mul_le_mul_left 26 hge

/-! ## Residual-level estimate (not the Néron conductor) -/

def natRadical (n : ℕ) : ℕ := ∏ p ∈ n.primeFactors, p

/-- Estimate after removing primes with `13 ∣ v_ℓ(Δ)` that divide `C`
    but not `A B`. This is **not** claimed to equal `N_E`. -/
def residualLevelEstimate (A B : ℕ) : ℕ :=
  32 * natRadical (A * B)

theorem unlowered_prime_dvd_residual {p A B : ℕ}
    (hp : p.Prime) (hA : A ≠ 0) (hB : B ≠ 0) (hpA : p ∣ A) :
    p ∣ residualLevelEstimate A B := by
  have hmem : p ∈ (A * B).primeFactors := by
    rw [mem_primeFactors]
    exact ⟨hp, dvd_mul_of_dvd_left hpA B, mul_ne_zero hA hB⟩
  have hrad : p ∣ natRadical (A * B) :=
    Finset.dvd_prod_of_mem (fun q => q) hmem
  exact dvd_mul_of_dvd_right hrad 32

/-! ## Kraus no-go: this Frey curve does not Fermat-lower `A` -/

theorem A_gt_B0_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    B0_nat < A := by
  have hAgt := A_gt_B_of_sol hsol hB
  exact Nat.lt_of_le_of_lt (by simpa [B0_nat_eq_threeLogs] using hB0) hAgt

/-- On a gap-3 solution with `B ≥ B0`, a prime `p ∤ 6` dividing `A`
    with `13 ∤ v_p(A)` survives Ribet at `13`. The displayed Frey
    curve therefore does not produce a Fermat-style uniform level
    independent of `A`. This is not a `B ≤ 10⁶` close. -/
theorem baker_bound_gap3_kraus_nogo {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B)
    (hp6 : ¬ p ∣ 6) (hpA : p ∣ A)
    (hnot13 : ¬ 13 ∣ padicValNat p A) :
    ¬ 13 ∣ padicValNat p (freyDiscNat A B) ∧ B0_nat < A := by
  have hApos : A ≠ 0 :=
    (Nat.pos_iff_ne_zero.mp (lt_trans hB (A_gt_B_of_sol hsol hB)))
  exact ⟨frey_A_not_ribet_lowered hp hsol hApos hB hp6 hpA hnot13,
    A_gt_B0_of_sol hsol hB hB0⟩

theorem baker_bound_gap3_kraus_nogo_val :
    ¬ 13 ∣ 8 ∧ 13 ∣ 26 :=
  ⟨not_thirteen_dvd_eight, thirteen_dvd_twenty_six⟩

/-! ## Locked uninhabited Props -/

def baker_bound_gap3 : Prop :=
  BealLevel26Foundations.BealGap3BakerUpperBound.baker_bound_gap3

def wuestholz_product_theorem_exp : Prop :=
  BealMatveevBeal.MatveevThreeLogs.wuestholz_product_theorem_exp

def wuestholz_product_theorem_exp_Gm3 : Prop :=
  BealMatveevBeal.MatveevThreeLogs.wuestholz_product_theorem_exp_Gm3

def baker_davenport_reduction : Prop :=
  BealMatveevBeal.MatveevThreeLogs.baker_davenport_reduction

def bugeaud_LLL_reduction_proof : Prop :=
  BealMatveevBeal.MatveevThreeLogs.bugeaud_LLL_reduction_proof

/-- Darmon–Merel for signature `(4,4,n)`, `n ≥ 4`. Not in Mathlib 4.12. -/
def darmon_merel_signature_44p : Prop :=
  ∀ A B C n : ℕ, 4 ≤ n → Nat.Coprime A B → A ^ 4 + B ^ 4 = C ^ n →
    A = 0 ∨ B = 0

/-- Uniform residual level `≤ 64` after Ribet at `13` for every gap-3
    Frey curve. Not a theorem of the displayed valuations: primes in
    `A` need not be lowered. Not in Mathlib 4.12. -/
def kraus_uniform_residual_level : Prop :=
  ∃ N : ℕ, N ≤ 64 ∧
    ∀ A B : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13 → 0 < B →
      residualLevelEstimate A B ∣ N

/-- Ribet lowering as a modularity theorem. Not in Mathlib 4.12. -/
def ribet_level_lowering : Prop :=
  darmon_merel_signature_44p

#check C1_floor_eq
#check B0_nat_eq
#check gcd_B_C_dvd_three
#check A_odd_of_sol
#check freyWeierstrass_Δ
#check freyDiscNat_of_sol
#check thirteen_dvd_twenty_six
#check not_thirteen_dvd_eight
#check padicValNat_freyDiscNat_at_A
#check padicValNat_freyDiscNat_at_C
#check frey_A_not_ribet_lowered
#check frey_C_ribet_lowered_candidate
#check baker_bound_gap3_kraus_nogo
#check baker_bound_gap3_kraus_nogo_val
#check baker_bound_gap3
#check darmon_merel_signature_44p
#print axioms gcd_B_C_dvd_three
#print axioms A_odd_of_sol
#print axioms freyWeierstrass_Δ
#print axioms freyDiscNat_of_sol
#print axioms baker_bound_gap3_kraus_nogo
#print axioms baker_bound_gap3_kraus_nogo_val

end BealMatveevBeal.BealKraus
