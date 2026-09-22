/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.Modularity
import Mazur_X0_13_No_Isogeny
import Tate_Frey_Conductor_29
import Mathlib.RepresentationTheory.Basic

/-!
# Residual Galois-representation boundaries

The pinned Mathlib revision has general representation theory but no
elliptic-curve representation

`ρ̄_{E,13} : G_ℚ → GL₂(𝔽₁₃)`.

The definitions below therefore re-expose the existing uninhabited Mazur
and Tate boundaries. They do not construct a representation object.
-/

namespace BealMatveevBeal.RibetCurve

/-- Boundary for constructing the Frey residual representation mod `13`.
The available project proposition is irreducibility of that missing
representation, not a representation object. -/
def residual_Galois_representation_mod13 : Prop :=
  BealMatveevBeal.MazurIrreducibility13.rho_Frey_mod13_irreducible

/-- Absolute irreducibility needed by Ribet. This is the baseline
equivalent of the Mazur scaffold's `frey_no_rational_13_isogeny`; it
remains uninhabited. -/
def residual_Galois_representation_mod13_absolutely_irreducible : Prop :=
  BealMatveevBeal.Mazur_X0_13_No_Isogeny.frey_no_rational_13_isogeny

/-- Unramifiedness at `29` needed for lowering. The baseline Tate boundary
asserts that the displayed conductor split agrees with the Néron
conductor; it remains uninhabited. -/
def residual_Galois_representation_mod13_unramified_at_29 : Prop :=
  BealMatveevBeal.Tate_Frey_Conductor_29.Frey_conductor_29_is_Neron

#check residual_Galois_representation_mod13
#check residual_Galois_representation_mod13_absolutely_irreducible
#check residual_Galois_representation_mod13_unramified_at_29

end BealMatveevBeal.RibetCurve