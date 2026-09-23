/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import MazurCurve.FreyJInvariant
import SerreImageFull
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Modularity data for the Frey curve

The displayed curve can be represented concretely by an elliptic curve with
the proved rational `j`-invariant.  Mathlib 4.12 has modular-form spaces, but
not Wiles/BCDT or a modular parametrization for this curve.  The structure
below therefore separates concrete curve data from the missing theorem.
-/

namespace BealMatveevBeal.RibetCurve

/-- Data delivered by a modularity theorem for the Frey curve.  The last
field is the existing Wiles/BCDT boundary, not a truth-valued default. -/
structure FreyModularityData (A B : ℕ) where
  E : EllipticCurve ℚ
  frey_j_eq : E.j = BealMatveevBeal.MazurCurve.frey_j A B
  level : ℕ
  modularityTheorem :
    BealMatveevBeal.SerreImageFull.modularity_Frey_semistable

/-- Wiles/BCDT specialized to every positive displayed gap-3 Frey curve.
No inhabitant is constructed at the pinned revision. -/
def modular_Frey : Prop :=
  ∀ A B : ℕ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
    0 < B →
      Nonempty (FreyModularityData A B)

#check FreyModularityData
#check modular_Frey

end BealMatveevBeal.RibetCurve