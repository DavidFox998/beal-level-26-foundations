/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import BSD_MordellWeil

/-!
# Mordell–Weil finite-generation boundary

The pinned Mathlib revision supplies the group law on affine nonsingular
points but not the Mordell–Weil finite-generation theorem for that group.
-/

namespace BealMatveevBeal.KolyvaginCurve

open BealMatveevBeal.BSD_MordellWeil

/-- A direct finite-generation statement for the project's
`MordellWeilGroup E`. Uninhabited in the current environment. -/
def MordellWeil_finitely_generated {K : Type*} [Field K]
    (E : WeierstrassCurve K) : Prop :=
  ∃ generators : Finset (MordellWeilGroup E),
    AddSubgroup.closure (↑generators : Set (MordellWeilGroup E)) = ⊤

def MordellWeil_26a1_finitely_generated : Prop :=
  MordellWeil_finitely_generated curve26a1_Q

def MordellWeil_26b1_finitely_generated : Prop :=
  MordellWeil_finitely_generated curve26b1_Q

#check MordellWeil_finitely_generated
#check MordellWeil_26a1_finitely_generated
#check MordellWeil_26b1_finitely_generated

end BealMatveevBeal.KolyvaginCurve