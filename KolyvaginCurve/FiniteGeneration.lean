/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import BSD_MordellWeil

/-!
# Mordell--Weil finite-generation boundary

The rational-point group used here is exactly the project's affine
nonsingular point group.  The pinned Mathlib revision supplies its
commutative group law but not the Mordell--Weil finite-generation theorem.
-/

namespace BealMatveevBeal.KolyvaginCurve

open BealMatveevBeal.BSD_MordellWeil

/-- The project's formal Mordell--Weil group. -/
abbrev ProjectMordellWeilGroup {K : Type*} [Field K]
    (E : WeierstrassCurve K) :=
  MordellWeilGroup E

/-- Direct finite generation by a finite set of rational points. -/
def MordellWeil_finitely_generated {K : Type*} [Field K]
    (E : WeierstrassCurve K) : Prop :=
  ∃ generators : Finset (ProjectMordellWeilGroup E),
    AddSubgroup.closure
      (↑generators : Set (ProjectMordellWeilGroup E)) = ⊤

def MordellWeil_26a1_finitely_generated : Prop :=
  MordellWeil_finitely_generated curve26a1_Q

def MordellWeil_26b1_finitely_generated : Prop :=
  MordellWeil_finitely_generated curve26b1_Q

#check ProjectMordellWeilGroup
#check MordellWeil_finitely_generated
#check MordellWeil_26a1_finitely_generated
#check MordellWeil_26b1_finitely_generated

end BealMatveevBeal.KolyvaginCurve