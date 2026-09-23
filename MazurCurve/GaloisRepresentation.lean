/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import MazurCurve.FreyJInvariant
import Mathlib.RepresentationTheory.Basic
import Serre_Large_vs_CM_Small

/-!
# Mod-`13` representation and Borel-containment interfaces

Mathlib has general representations but no canonical
`ρ̄_{E,13} : G_ℚ → GL₂(𝔽₁₃)`.  This module defines the representation data
and expresses Borel containment invariantly as preservation of a nonzero
proper line.  Attachment to the Frey curve remains an explicit boundary.
-/

namespace BealMatveevBeal.MazurCurve

/-- An abstract two-dimensional mod-`13` Galois representation. -/
structure Mod13GaloisRepresentation (G : Type*) [Group G] where
  rho : Representation (ZMod 13) G (Fin 2 → ZMod 13)

/-- Image containment in a Borel, expressed by an invariant nonzero proper
submodule.  Over `𝔽₁₃²` such a submodule is a line. -/
def Mod13GaloisRepresentation.IsBorelContained
    {G : Type*} [Group G] (r : Mod13GaloisRepresentation G) : Prop :=
  ∃ L : Submodule (ZMod 13) (Fin 2 → ZMod 13),
    L ≠ ⊥ ∧ L ≠ ⊤ ∧
      ∀ g : G, ∀ v : Fin 2 → ZMod 13, v ∈ L → r.rho g v ∈ L

/-- Irreducibility/non-Borel image for the abstract representation. -/
def Mod13GaloisRepresentation.IsIrreducible
    {G : Type*} [Group G] (r : Mod13GaloisRepresentation G) : Prop :=
  ¬ r.IsBorelContained

/-- Candidate representation data paired with an elliptic curve having the
displayed Frey `j`-invariant.  The pinned library still lacks the theorem that
`rho` is the action on that curve's geometric `13`-torsion. -/
structure FreyMod13Representation (G : Type*) [Group G] (A B : ℕ)
    extends Mod13GaloisRepresentation G where
  E : EllipticCurve ℚ
  frey_j_eq : E.j = frey_j A B

/-- Concrete irreducibility predicate once a representation object exists. -/
def rho_Frey_mod13_irreducible
    {G : Type*} [Group G] {A B : ℕ}
    (r : FreyMod13Representation G A B) : Prop :=
  r.toMod13GaloisRepresentation.IsIrreducible

/-- The two exact missing `X₀(13)` inputs imply Frey-specific exclusion of
reducibility.  This theorem is proved logically; it does not inhabit either
antecedent or construct the representation. -/
theorem mazur_irreducible_13_via_X0_13
    (himage : reducible_13_iff_j_in_image)
    (hexclude : no_t_gives_Frey_j_when_29_dvd_C) :
    ∀ A B : ℕ,
      A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
      1 ≤ B →
      ¬ 29 ∣ A →
      ¬ 29 ∣ B →
      29 ∣ B + 3 →
        ¬ FreyReducibleMod13 A B := by
  unfold reducible_13_iff_j_in_image at himage
  unfold no_t_gives_Frey_j_when_29_dvd_C at hexclude
  intro A B hsol hBpos hA hB hC hred
  rcases (himage A B hsol).mp hred with ⟨t, ht, hj⟩
  exact hexclude A B t hsol hBpos hA hB hC ht hj

/-- Final quantified theorem target.  It remains uninhabited until the two
antecedents above are constructed. -/
def mazur_irreducible_13_theorem : Prop :=
  ∀ A B : ℕ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
    1 ≤ B →
    ¬ 29 ∣ A →
    ¬ 29 ∣ B →
    29 ∣ B + 3 →
      ¬ FreyReducibleMod13 A B

theorem mazur_inputs_imply_irreducible
    (himage : reducible_13_iff_j_in_image)
    (hexclude : no_t_gives_Frey_j_when_29_dvd_C) :
    mazur_irreducible_13_theorem :=
  mazur_irreducible_13_via_X0_13 himage hexclude

#check Mod13GaloisRepresentation
#check Mod13GaloisRepresentation.IsBorelContained
#check Mod13GaloisRepresentation.IsIrreducible
#check FreyMod13Representation
#check rho_Frey_mod13_irreducible
#check mazur_irreducible_13_via_X0_13
#check mazur_irreducible_13_theorem
#check mazur_inputs_imply_irreducible

end BealMatveevBeal.MazurCurve