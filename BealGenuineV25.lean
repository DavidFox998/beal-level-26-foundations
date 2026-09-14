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
import BealFLT13
import BealDarmonMerel
import BealDarmonMerel44p
import BealKraus

/-!
# Darmon–Merel (4,4,13) + 3-adic descent no-go
(not a `B ≤ 10⁶` close)

Successor of `f1cb039` (`v24-v24x-final-FLT13-nogo`).
3-adic descent already rules out `3 ∣ B`. Every remaining
solution is coprime, which is Darmon–Merel's hypothesis for
signature `(4,4,13)`. If that statement were a theorem there
would be no gap-3 solutions at all, and `baker_bound_gap3`
would hold vacuously. It is not a theorem in Mathlib 4.12,
nor are FLT 13 and Ribet-to-32. A putative solution with
`B ≥ B0` would refute Darmon–Merel `(4,4,13)`; without that
theorem the displayed residual is still not 32 and `A > B0`.

`baker_bound_gap3` stays uninhabited as a named theorem. Not v25.
The axiom-relative inhabitant is `BealTrueV25.baker_bound_gap3_true`.
`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

namespace BealMatveevBeal.BealGenuineV25

open BealMatveevBeal.BealFLT13
open BealMatveevBeal.BealDarmonMerel
open BealMatveevBeal.BealDarmonMerel44p
open BealMatveevBeal.BealKraus

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem B0_nat_eq_pow10 : B0_nat = 10 ^ 6 := rfl

theorem C1_floor_eq_flt13 :
    C1_floor = BealMatveevBeal.BealFLT13.C1_floor := rfl

theorem B0_nat_eq_flt13 :
    B0_nat = BealMatveevBeal.BealFLT13.B0_nat := rfl

/-! ## Re-export of the 3-adic descent (`f1cb039`) -/

theorem no_sol_when_three_dvd_B_of_f1cb039 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : 3 ∣ B) : False :=
  no_sol_when_three_dvd_B hsol h3

theorem coprime_of_remaining_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    ¬ 3 ∣ B ∧ Nat.gcd A B = 1 :=
  ⟨three_not_dvd_B_of_sol hsol,
    gcd_one_when_three_not_dvd_B hsol (three_not_dvd_B_of_sol hsol)⟩

/-! ## Locked uninhabited Props (needed below as hypotheses) -/

/-- Darmon–Merel signature `(4,4,13)`: no coprime solutions of
    `x⁴ + y⁴ = z¹³`. Not in Mathlib 4.12. -/
def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealFLT13.darmon_merel_44_13_no_coprime

def darmon_merel_signature_44p : Prop :=
  BealMatveevBeal.BealFLT13.darmon_merel_signature_44p

def fermat_last_theorem_thirteen : Prop :=
  BealMatveevBeal.BealFLT13.fermat_last_theorem_thirteen

def ribet_level_lowering_to_32 : Prop :=
  BealMatveevBeal.BealFLT13.ribet_level_lowering_to_32

def ribet_level_lowering : Prop :=
  BealMatveevBeal.BealFLT13.ribet_level_lowering

def baker_bound_gap3 : Prop :=
  BealMatveevBeal.BealFLT13.baker_bound_gap3

/-! ## Conditional close: Darmon–Merel `(4,4,13)` ⇒ no gap-3 at all -/

/-- If Darmon–Merel `(4,4,13)` held, 3-adic descent plus coprimeness
    would rule out every gap-3 solution. -/
theorem no_gap3_of_darmon_merel_4413
    (hDM : darmon_merel_44_13_no_coprime) (A B : ℕ) :
    ¬ (A ^ 4 + B ^ 4 = (B + 3) ^ 13) := by
  intro hsol
  by_cases h3 : 3 ∣ B
  · exact no_sol_when_three_dvd_B_of_f1cb039 hsol h3
  · have hcop : Nat.Coprime A B := coprime_of_sol hsol
    have hDM' : A = 0 ∨ B = 0 := hDM A B (B + 3) hcop hsol
    have hBne : B ≠ 0 := by
      intro hB0
      rw [hB0] at h3
      exact h3 (dvd_zero 3)
    have hBpos : 0 < B := Nat.pos_of_ne_zero hBne
    have hAne : A ≠ 0 := A_ne_zero_of_sol hsol hBpos
    rcases hDM' with hA0 | hB0
    · exact hAne hA0
    · exact hBne hB0

/-- Absence of gap-3 solutions makes `baker_bound_gap3` hold
    vacuously. Does **not** inhabit Darmon–Merel. -/
theorem baker_bound_gap3_of_no_gap3
    (h : ∀ A B : ℕ, ¬ (A ^ 4 + B ^ 4 = (B + 3) ^ 13)) :
    baker_bound_gap3 :=
  ⟨10 ^ 6, rfl, fun _B _hgt ⟨A, hsol⟩ => h A _B hsol⟩

/-- If Darmon–Merel `(4,4,13)` were a theorem, `baker_bound_gap3`
    would hold vacuously. The hypothesis is not available in
    Mathlib 4.12. -/
theorem baker_bound_gap3_of_darmon_merel_4413
    (hDM : darmon_merel_44_13_no_coprime) :
    baker_bound_gap3 :=
  baker_bound_gap3_of_no_gap3 (no_gap3_of_darmon_merel_4413 hDM)

/-! ## Unconditional no-go on a `B ≥ B0` solution -/

/-- Even with 3-adic descent and coprimeness, a solution at
    `B ≥ B0` still has residual ≠ 32 and `A > B0`, and would
    refute Darmon–Merel `(4,4,13)`. That statement, FLT 13, and
    Ribet-to-32 stay `def Prop`. -/
theorem baker_bound_gap3_darmon_merel_4413_3adic_nogo {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    ¬ 3 ∣ B ∧
      Nat.Coprime A B ∧
      residualLevelEstimate A B ≠ 32 ∧
      B0_nat < A ∧
      ¬ 13 ∣ 8 ∧ 13 ∣ 26 ∧
      (darmon_merel_44_13_no_coprime → False) := by
  have hB0f : BealMatveevBeal.BealFLT13.B0_nat ≤ B := by
    simpa [B0_nat_eq_flt13] using hB0
  have hnogo := baker_bound_gap3_flt13_darmon_merel_nogo hsol hB hB0f
  obtain ⟨hnot3, hcop, hres, hA, h13⟩ := hnogo
  obtain ⟨h138, h1326⟩ := h13
  refine ⟨hnot3, hcop, hres, ?_, h138, h1326, ?_⟩
  · simpa [B0_nat_eq_flt13] using hA
  · intro hDM
    exact no_gap3_of_darmon_merel_4413 hDM A B hsol

#check C1_floor_eq
#check B0_nat_eq
#check no_sol_when_three_dvd_B_of_f1cb039
#check coprime_of_remaining_sol
#check no_gap3_of_darmon_merel_4413
#check baker_bound_gap3_of_no_gap3
#check baker_bound_gap3_of_darmon_merel_4413
#check baker_bound_gap3_darmon_merel_4413_3adic_nogo
#check baker_bound_gap3
#check darmon_merel_44_13_no_coprime
#check fermat_last_theorem_thirteen
#print axioms no_sol_when_three_dvd_B_of_f1cb039
#print axioms coprime_of_remaining_sol
#print axioms no_gap3_of_darmon_merel_4413
#print axioms baker_bound_gap3_of_no_gap3
#print axioms baker_bound_gap3_of_darmon_merel_4413
#print axioms baker_bound_gap3_darmon_merel_4413_3adic_nogo

end BealMatveevBeal.BealGenuineV25
