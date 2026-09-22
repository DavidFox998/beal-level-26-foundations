/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.Conductor
import Ribet_Level_Lowering_29_to_32

/-!
# Ribet level-lowering boundary

The identity `928 / 29 = 32` is necessary arithmetic.  A genuine theorem must
start from a modular, absolutely irreducible residual representation with the
required local behavior and produce residual eigenform data at level `32`.
-/

namespace BealMatveevBeal.RibetCurve

/-- Coefficient data for the residual eigenform that Ribet's theorem should
produce.  This is not called a Mathlib modular form because the required
residual-eigenform construction is absent from the pinned library. -/
structure ResidualEigenformAtLevel32 where
  level : ℕ
  level_eq : level = 32
  coefficientMod13 : ℕ → Option (ZMod 13)

/-- Ribet lowering specialized to the Frey branch.  All mathematical inputs
are explicit and the conclusion constructs residual level-`32` data. -/
def ribet_level_lowering_29_to_32 : Prop :=
  modular_Frey →
  residual_Galois_representation_mod13 →
  residual_Galois_representation_mod13_absolutely_irreducible →
  residual_Galois_representation_mod13_unramified_at_29 →
    ∀ A B : ℕ,
      A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
      0 < B →
      ¬ 29 ∣ A →
      ¬ 29 ∣ B →
      29 ∣ B + 3 →
        Nonempty ResidualEigenformAtLevel32

/-- Library-facing alias for the specialization `928 → 32`. -/
def Ribet_928_to_32 : Prop :=
  ribet_level_lowering_29_to_32

/-- Abstract-facing alias.  No converse or general Ribet theorem is claimed. -/
def Ribet_level_lowering_abstract : Prop :=
  ribet_level_lowering_29_to_32

#check ResidualEigenformAtLevel32
#check ribet_level_lowering_29_to_32
#check Ribet_928_to_32
#check Ribet_level_lowering_abstract

end BealMatveevBeal.RibetCurve