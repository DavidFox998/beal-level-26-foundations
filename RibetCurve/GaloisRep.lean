/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.Modularity
import MazurCurve.GaloisRepresentation
import TateCurve.InertiaRepresentation

/-!
# Residual mod-`13` representation data

This module constructs the type of representation data needed by Ribet from
Mathlib's general representation theory.  It does not claim that an absolute
Galois group, its inertia subgroup, or its action on geometric Frey
`13`-torsion is available in Mathlib.
-/

namespace BealMatveevBeal.RibetCurve

/-- An abstract mod-`13` representation paired with the displayed Frey curve
and a designated inertia subgroup at `29`. -/
structure FreyResidualRepresentation13
    (G : Type*) [Group G] (A B : ℕ)
    extends BealMatveevBeal.MazurCurve.FreyMod13Representation G A B where
  inertia29 : Subgroup G

/-- Absolute irreducibility, expressed by the invariant-line criterion from
the Mazur library. -/
def FreyResidualRepresentation13.IsAbsolutelyIrreducible
    {G : Type*} [Group G] {A B : ℕ}
    (r : FreyResidualRepresentation13 G A B) : Prop :=
  r.toFreyMod13Representation.toMod13GaloisRepresentation.IsIrreducible

/-- Triviality on the designated inertia group at `29`. -/
def FreyResidualRepresentation13.IsUnramifiedAt29
    {G : Type*} [Group G] {A B : ℕ}
    (r : FreyResidualRepresentation13 G A B) : Prop :=
  ∀ g : G, g ∈ r.inertia29 → r.rho g = 1

/-- Forward attachment needed to transfer the Frey-specific `X₀(13)`
exclusion to the concrete representation.  No converse is claimed. -/
def FreyResidualRepresentation13.MazurReducibilityCompatible
    {G : Type*} [Group G] {A B : ℕ}
    (r : FreyResidualRepresentation13 G A B) : Prop :=
  (¬ BealMatveevBeal.MazurCurve.FreyReducibleMod13 A B) →
    r.IsAbsolutelyIrreducible

/-- The Mazur inputs imply irreducibility of a representation after its
reducibility predicate has been identified with the concrete representation.
Only the forward direction is used. -/
theorem absolutely_irreducible_of_Mazur_inputs
    {G : Type*} [Group G] {A B : ℕ}
    (r : FreyResidualRepresentation13 G A B)
    (hcompat : r.MazurReducibilityCompatible)
    (himage : BealMatveevBeal.MazurCurve.reducible_13_iff_j_in_image)
    (hexclude : BealMatveevBeal.MazurCurve.no_t_gives_Frey_j_when_29_dvd_C)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    r.IsAbsolutelyIrreducible := by
  apply hcompat
  exact BealMatveevBeal.MazurCurve.mazur_irreducible_13_via_X0_13
    himage hexclude A B hsol hBpos hA hB hC

/-- Construction target for the residual representation. -/
def residual_Galois_representation_mod13 : Prop :=
  ∀ A B : ℕ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
    0 < B →
      ∃ (G : Type) (_ : Group G),
        Nonempty (FreyResidualRepresentation13 G A B)

/-- Absolute irreducibility target after constructing the representation. -/
def residual_Galois_representation_mod13_absolutely_irreducible : Prop :=
  ∀ (G : Type) (_ : Group G) (A B : ℕ)
    (r : FreyResidualRepresentation13 G A B),
      r.IsAbsolutelyIrreducible

/-- Mod-`13` unramifiedness at `29`, to be supplied by the Tate cyclotomic
inertia formula when `13 ∣ v₂₉(Δ)`. -/
def residual_Galois_representation_mod13_unramified_at_29 : Prop :=
  ∀ (G : Type) (_ : Group G) (A B : ℕ)
    (r : FreyResidualRepresentation13 G A B),
    29 ∣ B + 3 →
      r.IsUnramifiedAt29

#check FreyResidualRepresentation13
#check FreyResidualRepresentation13.IsAbsolutelyIrreducible
#check FreyResidualRepresentation13.IsUnramifiedAt29
#check absolutely_irreducible_of_Mazur_inputs
#check residual_Galois_representation_mod13
#check residual_Galois_representation_mod13_absolutely_irreducible
#check residual_Galois_representation_mod13_unramified_at_29

end BealMatveevBeal.RibetCurve