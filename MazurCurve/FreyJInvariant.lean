/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import MazurCurve.X0_13_Moduli
import MazurIrreducibility13

/-!
# Frey `j`-invariant and `X₀(13)` image blockers

The displayed Frey `j`-invariant is already defined as `c₄³/Δ`. What is
missing is the modular interpretation:

* reducibility of `ρ̄_{E,13}` iff the Frey `j` lies in the Fricke image; and
* a global exclusion of every rational Fricke parameter compatible with the
  gap-3 equation and `29 ∣ B+3`.

The local valuation split for a possible parameter does not prove the
global exclusion.
-/

namespace BealMatveevBeal.MazurCurve

/-- Existing exact rational `j = c₄³/Δ` for the displayed Frey model. -/
def frey_j (A B : ℕ) : ℚ :=
  BealMatveevBeal.MazurIrreducibility13.frey_j A B

/-- Missing modular-curve theorem, re-exposed without adding an axiom. -/
def reducible_13_iff_j_in_image : Prop :=
  BealMatveevBeal.Mazur_X0_13_RationalPoints.reducible_13_iff_j_in_image

/-- Missing Frey-specific global parameter exclusion, re-exposed without
turning the local `29`-adic alternatives into a false global conclusion. -/
def no_t_gives_Frey_j_when_29_dvd_C : Prop :=
  BealMatveevBeal.Mazur_X0_13_RationalPoints.no_t_gives_Frey_j_when_29_dvd_C

#check frey_j
#check reducible_13_iff_j_in_image
#check no_t_gives_Frey_j_when_29_dvd_C

end BealMatveevBeal.MazurCurve