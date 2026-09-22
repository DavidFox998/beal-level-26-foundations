/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import MazurCurve.FreyJInvariant
import Mathlib.RepresentationTheory.Basic
import Serre_Large_vs_CM_Small

/-!
# Mod-`13` Galois-representation scaffold

Mathlib at the pinned revision has general representation theory, but no
elliptic-curve representation

`ρ̄_{E,13} : G_ℚ → GL₂(𝔽₁₃)`.

Consequently the project cannot yet express, as a theorem about that map,
that its image is contained in a Borel or is non-Borel. The numerical facts
`48 < 2184` and `288 / 48 = 6` do not identify the Frey image and cannot
prove irreducibility by cardinality alone.
-/

namespace BealMatveevBeal.MazurCurve

/-- Vocabulary for the missing image-containment predicate. -/
inductive BorelOrNot where
  | Borel
  | NonBorel
  deriving DecidableEq, Repr

/-- Boundary for constructing the Frey mod-`13` representation.

The only available project proposition is the existing uninhabited
irreducibility boundary; this alias does not manufacture a representation
object. -/
def rho_Frey_mod13 : Prop :=
  BealMatveevBeal.MazurIrreducibility13.rho_Frey_mod13_irreducible

/-- Existing uninhabited non-Borel/irreducibility boundary. -/
def rho_Frey_mod13_irreducible : Prop :=
  BealMatveevBeal.MazurIrreducibility13.rho_Frey_mod13_irreducible

/-- Forward implication requiring both missing `X₀(13)` results. -/
def mazur_irreducible_13_via_X0_13 : Prop :=
  reducible_13_iff_j_in_image →
    no_t_gives_Frey_j_when_29_dvd_C →
      rho_Frey_mod13_irreducible

/-- No rational cyclic `13`-isogeny for the relevant Frey curve. -/
def frey_no_rational_13_isogeny : Prop :=
  mazur_irreducible_13_via_X0_13

/-- Final irreducibility target; still uninhabited. -/
def mazur_irreducible_13_theorem : Prop :=
  rho_Frey_mod13_irreducible

/-- Alias used by later level-lowering stages; still uninhabited. -/
def mazur_no_Frey_13_isogeny : Prop :=
  mazur_irreducible_13_theorem

#check BorelOrNot
#check rho_Frey_mod13
#check rho_Frey_mod13_irreducible
#check mazur_irreducible_13_via_X0_13
#check frey_no_rational_13_isogeny
#check mazur_irreducible_13_theorem
#check mazur_no_Frey_13_isogeny

end BealMatveevBeal.MazurCurve