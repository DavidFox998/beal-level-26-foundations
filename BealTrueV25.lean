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
import BealGenuineV25

/-!
# Axiom-relative `baker_bound_gap3` (not a Mathlib-only v25 mint)

Successor of `2b4ee3b` (`v24-v24x-final-genuine-v25-nogo`).
`BealGenuineV25.baker_bound_gap3_of_darmon_merel_4413` already
shows that Darmon–Merel signature `(4,4,13)` implies the kernel
`baker_bound_gap3` vacuously via 3-adic descent. Mathlib 4.12
does not prove that signature, so this module takes it as an
`axiom`. The inhabitant `baker_bound_gap3_true` therefore
depends on `darmon_merel_4413_axiom` in addition to
`[propext, Classical.choice, Quot.sound]`. That is **not**
the unconditional minted tag
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`
(`hGen` / `hLLL` remain open; see `BealUnconditionalV25`). 0 sorry.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

namespace BealMatveevBeal.BealTrueV25

open BealMatveevBeal.BealGenuineV25

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_gv25 :
    C1_floor = BealMatveevBeal.BealGenuineV25.C1_floor := rfl

theorem B0_nat_eq_gv25 :
    B0_nat = BealMatveevBeal.BealGenuineV25.B0_nat := rfl

/-! ## Kernel `baker_bound_gap3` (same Prop as GenuineV25) -/

def baker_bound_gap3 : Prop :=
  BealMatveevBeal.BealGenuineV25.baker_bound_gap3

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealGenuineV25.darmon_merel_44_13_no_coprime

def fermat_last_theorem_thirteen : Prop :=
  BealMatveevBeal.BealGenuineV25.fermat_last_theorem_thirteen

def ribet_level_lowering_to_32 : Prop :=
  BealMatveevBeal.BealGenuineV25.ribet_level_lowering_to_32

def ribet_level_lowering : Prop :=
  BealMatveevBeal.BealGenuineV25.ribet_level_lowering

/-! ## External axiom: Darmon–Merel signature `(4,4,13)` -/

/-- Not in Mathlib 4.12. Coprime solutions of `x⁴ + y⁴ = z¹³`
    have a vanishing factor. -/
axiom darmon_merel_4413_axiom : darmon_merel_44_13_no_coprime

/-! ## 3-adic descent re-exports (`f1cb039` / `2b4ee3b`) -/

theorem no_sol_when_three_dvd_B {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : 3 ∣ B) : False :=
  no_sol_when_three_dvd_B_of_f1cb039 hsol h3

theorem coprime_of_remaining {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (_h3 : ¬ 3 ∣ B) : Nat.gcd A B = 1 :=
  (coprime_of_remaining_sol hsol).2

/-! ## Vacuous close relative to the axiom -/

theorem no_gap3_of_axiom (A B : ℕ) :
    ¬ (A ^ 4 + B ^ 4 = (B + 3) ^ 13) :=
  no_gap3_of_darmon_merel_4413 darmon_merel_4413_axiom A B

/-- Kernel `baker_bound_gap3`: no gap-3 solutions with `B > 10⁶`.
    Depends on `darmon_merel_4413_axiom`. -/
theorem baker_bound_gap3_true : baker_bound_gap3 :=
  baker_bound_gap3_of_darmon_merel_4413 darmon_merel_4413_axiom

/-- Stronger vacuous form: any solution would satisfy `B ≤ B0`,
    because there are no solutions. -/
theorem baker_bound_gap3_le_B0 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) : B ≤ B0_nat :=
  (no_gap3_of_axiom A B hsol).elim

#check C1_floor_eq
#check B0_nat_eq
#check darmon_merel_4413_axiom
#check no_sol_when_three_dvd_B
#check coprime_of_remaining
#check no_gap3_of_axiom
#check baker_bound_gap3_true
#check baker_bound_gap3_le_B0
#check baker_bound_gap3
#print axioms no_sol_when_three_dvd_B
#print axioms no_gap3_of_axiom
#print axioms baker_bound_gap3_true
#print axioms baker_bound_gap3_le_B0

end BealMatveevBeal.BealTrueV25
