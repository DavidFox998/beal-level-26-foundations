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
import BealCatalanZsig
import BealKraus

/-!
# Darmon–Merel / Ribet residual-level no-go (not a `B ≤ 10⁶` close)

Successor of `752f7af` (`v24-v24x-final-Mihailescu-Zsigmondy-nogo`).
Darmon–Merel for `x⁴ + y⁴ = zⁿ` (`n ≥ 4`) needs `gcd(x,y) = 1`.
On gap-3, `3 ∣ B` forces `3 ∣ A`, so `gcd(A,B) ≠ 1` and the
coprime hypothesis fails. When `3 ∤ B` one does have
`gcd(A,B) = 1`, but Darmon–Merel is not in Mathlib 4.12, and
the displayed Frey curve still does not give uniform level 32:
`13 ∣ 26` so primes in `C = B+3` lower, while `13 ∤ 8` so a
prime `p ∤ 6` in `A` with `13 ∤ v_p(A)` survives. That prime
divides `residualLevelEstimate = 32 rad(AB)`, which therefore
does not divide 32. `A > B0` on `B ≥ B0`, so a residual level
that still depends on `A` is not a `B ≤ 10⁶` close.

Darmon–Merel, Ribet, and uniform residual level stay `def Prop`.
`baker_bound_gap3` stays uninhabited. Not v25.
`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

namespace BealMatveevBeal.BealDarmonMerel

open BealMatveevBeal.BealKraus
open BealMatveevBeal.BealCatalanZsig

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_catalan :
    C1_floor = BealMatveevBeal.BealCatalanZsig.C1_floor := rfl

theorem B0_nat_eq_catalan :
    B0_nat = BealMatveevBeal.BealCatalanZsig.B0_nat := rfl

theorem C1_floor_eq_kraus :
    C1_floor = BealMatveevBeal.BealKraus.C1_floor := rfl

theorem B0_nat_eq_kraus :
    B0_nat = BealMatveevBeal.BealKraus.B0_nat := rfl

/-! ## `3 ∣ B` ⇒ `3 ∣ A` ⇒ Darmon–Merel coprime hypothesis fails -/

theorem three_dvd_C_of_three_dvd_B {B : ℕ} (h3 : 3 ∣ B) :
    3 ∣ B + 3 :=
  dvd_add h3 (by decide : 3 ∣ 3)

theorem three_dvd_A_of_three_dvd_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : 3 ∣ B) : 3 ∣ A := by
  have hB4 : 3 ∣ B ^ 4 := dvd_pow h3 (by decide)
  have hC13 : 3 ∣ (B + 3) ^ 13 :=
    dvd_pow (three_dvd_C_of_three_dvd_B h3) (by decide)
  have hsum : 3 ∣ A ^ 4 + B ^ 4 := hsol ▸ hC13
  have hle : B ^ 4 ≤ A ^ 4 + B ^ 4 := Nat.le_add_left _ _
  have hA4 : 3 ∣ A ^ 4 := by
    have hsub : 3 ∣ (A ^ 4 + B ^ 4) - B ^ 4 :=
      Nat.dvd_sub hle hsum hB4
    simpa [Nat.add_sub_cancel] using hsub
  exact Nat.prime_three.dvd_of_dvd_pow hA4

theorem gcd_A_B_ne_one_of_three_dvd_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : 3 ∣ B) :
    Nat.gcd A B ≠ 1 := by
  have h3A : 3 ∣ A := three_dvd_A_of_three_dvd_B hsol h3
  have hgcd : 3 ∣ Nat.gcd A B := Nat.dvd_gcd h3A h3
  intro h1
  rw [h1] at hgcd
  exact (by decide : ¬ (3 ∣ 1)) hgcd

/-- Darmon–Merel for `x⁴ + y⁴ = zⁿ` needs `gcd(x,y) = 1`.
    That hypothesis fails on gap-3 whenever `3 ∣ B`. -/
theorem darmon_merel_hypothesis_fails_when_three_dvd_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : 3 ∣ B) :
    ¬ Nat.Coprime A B :=
  gcd_A_B_ne_one_of_three_dvd_B hsol h3

theorem gcd_A_B_eq_one_of_not_three_dvd_B_reexport {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : ¬ 3 ∣ B) :
    Nat.gcd A B = 1 :=
  gcd_A_B_eq_one_of_not_three_dvd_B hsol h3

theorem A_ne_zero_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) : A ≠ 0 := by
  intro hA0
  have hB4 : B ^ 4 = (B + 3) ^ 13 := by
    simpa [hA0] using hsol
  have hlt : B ^ 4 + 1 < (B + 3) ^ 13 :=
    C_pow_thirteen_gt_B_pow_four_add_one hB
  have : B ^ 4 + 1 < B ^ 4 := by simpa [hB4] using hlt
  exact Nat.not_lt.2 (Nat.le_add_right _ 1) this

/-! ## Displayed Frey: `C` lowers, `A` and `B` need not -/

theorem not_thirteen_dvd_eight_reexport : ¬ 13 ∣ 8 :=
  not_thirteen_dvd_eight

theorem thirteen_dvd_twenty_six_reexport : 13 ∣ 26 :=
  thirteen_dvd_twenty_six

theorem frey_C_ribet_lowered {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : A ≠ 0) (hB : B ≠ 0)
    (hp2 : p ≠ 2) (hpA : ¬ p ∣ A) (hpB : ¬ p ∣ B)
    (hpC : p ∣ (B + 3)) :
    13 ∣ padicValNat p (freyDiscNat A B) :=
  (frey_C_ribet_lowered_candidate hp hsol hA hB hp2 hpA hpB hpC).1

theorem frey_B_not_ribet_lowered_reexport {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : A ≠ 0) (hB : 0 < B)
    (hp6 : ¬ p ∣ 6) (hpB : p ∣ B)
    (hnot13 : ¬ 13 ∣ padicValNat p B) :
    ¬ 13 ∣ padicValNat p (freyDiscNat A B) :=
  frey_B_not_ribet_lowered hp hsol hA hB hp6 hpB hnot13

/-- When `3 ∤ B` the coprime hypothesis of Darmon–Merel holds,
    but an unlowered prime in `A` still survives Ribet at `13`. -/
theorem frey_A_prime_survives_when_three_not_dvd_B {p A B : ℕ}
    (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : ¬ 3 ∣ B) (hB : 0 < B)
    (hp6 : ¬ p ∣ 6) (hpA : p ∣ A)
    (hnot13 : ¬ 13 ∣ padicValNat p A) :
    ¬ 13 ∣ padicValNat p (freyDiscNat A B) ∧ Nat.Coprime A B := by
  have hApos : A ≠ 0 := A_ne_zero_of_sol hsol hB
  exact ⟨frey_A_not_ribet_lowered hp hsol hApos hB hp6 hpA hnot13,
    gcd_A_B_eq_one_of_not_three_dvd_B hsol h3⟩

/-! ## Residual estimate is not level 32 when an `A`-prime survives -/

theorem not_prime_dvd_thirty_two {p : ℕ} (hp : p.Prime)
    (hp6 : ¬ p ∣ 6) : ¬ p ∣ 32 := by
  have hpne : ¬ (p = 2 ∨ p = 3) := fun h =>
    hp6 ((prime_dvd_six_iff hp).2 h)
  have hp2 : p ≠ 2 := fun h => hpne (Or.inl h)
  intro h32
  have hpow : p ∣ 2 ^ 5 := by
    simpa [show (32 : ℕ) = 2 ^ 5 from rfl] using h32
  have : p ∣ 2 := hp.dvd_of_dvd_pow hpow
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)

/-- If a prime `p ∤ 6` divides `A` and `13 ∤ v_p(A)`, then `p`
    divides the displayed residual estimate, so that estimate
    does not divide 32. This is not a Néron conductor, and it
    is not a uniform level-32 newform check. -/
theorem kraus_uniform_residual_level_32_nogo {p A B : ℕ} (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B)
    (hp6 : ¬ p ∣ 6) (hpA : p ∣ A)
    (hnot13 : ¬ 13 ∣ padicValNat p A) :
    p ∣ residualLevelEstimate A B ∧
      ¬ 13 ∣ padicValNat p (freyDiscNat A B) ∧
      B0_nat < A ∧
      ¬ residualLevelEstimate A B ∣ 32 := by
  have hApos : A ≠ 0 := A_ne_zero_of_sol hsol hB
  have hBne : B ≠ 0 := Nat.pos_iff_ne_zero.mp hB
  have hres := unlowered_prime_dvd_residual hp hApos hBne hpA
  have hB0k : BealMatveevBeal.BealKraus.B0_nat ≤ B := by
    simpa [B0_nat_eq_kraus] using hB0
  have hkraus :=
    baker_bound_gap3_kraus_nogo hp hsol hB hB0k hp6 hpA hnot13
  refine ⟨hres, hkraus.1, ?_, ?_⟩
  · simpa [B0_nat_eq_kraus] using hkraus.2
  · intro hdiv
    exact not_prime_dvd_thirty_two hp hp6 (Nat.dvd_trans hres hdiv)

/-- Even assuming Darmon–Merel (uninhabited `def Prop`), gap-3
    with `3 ∣ B` is not coprime, so the theorem does not apply;
    `A > B0` and `13 ∤ 8` so the displayed Frey curve is not a
    uniform level-32 check independent of `A`. -/
theorem baker_bound_gap3_darmon_merel_nogo {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (3 ∣ B → ¬ Nat.Coprime A B) ∧
      B0_nat < A ∧
      ¬ 13 ∣ 8 ∧ 13 ∣ 26 := by
  refine ⟨fun h3 => darmon_merel_hypothesis_fails_when_three_dvd_B hsol h3,
    ?_, not_thirteen_dvd_eight, thirteen_dvd_twenty_six⟩
  have hB0k : BealMatveevBeal.BealKraus.B0_nat ≤ B := by
    simpa [B0_nat_eq_kraus] using hB0
  simpa [B0_nat_eq_kraus] using A_gt_B0_of_sol hsol hB hB0k

theorem baker_bound_gap3_darmon_merel_nogo_val :
    ¬ 13 ∣ 8 ∧ 13 ∣ 26 :=
  ⟨not_thirteen_dvd_eight, thirteen_dvd_twenty_six⟩

/-! ## Locked uninhabited Props -/

/-- Darmon–Merel: no coprime solutions of `x⁴ + y⁴ = zⁿ` for
    `n ≥ 4`. Not in Mathlib 4.12. -/
def darmon_merel_x4_y4_zp_no_coprime_solutions : Prop :=
  BealMatveevBeal.BealKraus.darmon_merel_signature_44p

def darmon_merel_signature_44p : Prop :=
  BealMatveevBeal.BealKraus.darmon_merel_signature_44p

def kraus_uniform_residual_level : Prop :=
  BealMatveevBeal.BealKraus.kraus_uniform_residual_level

def ribet_level_lowering : Prop :=
  BealMatveevBeal.BealKraus.ribet_level_lowering

def baker_bound_gap3 : Prop :=
  BealMatveevBeal.BealCatalanZsig.baker_bound_gap3

def gaussian_associate_thirteenth_power : Prop :=
  BealMatveevBeal.BealCatalanZsig.gaussian_associate_thirteenth_power

def zsigmondy_gaussian_primitive_divisor : Prop :=
  BealMatveevBeal.BealCatalanZsig.zsigmondy_gaussian_primitive_divisor

def mihailescu_catalan : Prop :=
  BealMatveevBeal.BealCatalanZsig.mihailescu_catalan

#check C1_floor_eq
#check B0_nat_eq
#check three_dvd_A_of_three_dvd_B
#check gcd_A_B_ne_one_of_three_dvd_B
#check darmon_merel_hypothesis_fails_when_three_dvd_B
#check gcd_A_B_eq_one_of_not_three_dvd_B_reexport
#check frey_C_ribet_lowered
#check frey_A_prime_survives_when_three_not_dvd_B
#check kraus_uniform_residual_level_32_nogo
#check baker_bound_gap3_darmon_merel_nogo
#check baker_bound_gap3
#check darmon_merel_x4_y4_zp_no_coprime_solutions
#check darmon_merel_signature_44p
#check kraus_uniform_residual_level
#check ribet_level_lowering
#print axioms three_dvd_A_of_three_dvd_B
#print axioms darmon_merel_hypothesis_fails_when_three_dvd_B
#print axioms kraus_uniform_residual_level_32_nogo
#print axioms baker_bound_gap3_darmon_merel_nogo
#print axioms frey_C_ribet_lowered

end BealMatveevBeal.BealDarmonMerel
