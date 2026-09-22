/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.Conductor
import Ribet_Level_Lowering_29_to_32

/-!
# Ribet level-lowering boundary

The identity `928 / 29 = 32` is necessary arithmetic for the displayed
branch. It does not prove modularity, identify a Néron conductor, establish
unramifiedness, or produce a residual eigenform of level `32`.
-/

namespace BealMatveevBeal.RibetCurve

/-- Ribet lowering specialized to the existing unramifiedness and
residual-level boundaries. Both sides remain uninhabited. -/
def ribet_level_lowering_29_to_32 : Prop :=
  BealMatveevBeal.Tate_I29_Inertia.inertia_trivial_mod13_when_13_dvd_v →
    BealMatveevBeal.DarmonMerelFrey4413.ribet_lowers_Frey_to_level_32

/-- Library-facing alias for the specialization `928 → 32`. -/
def Ribet_928_to_32 : Prop :=
  ribet_level_lowering_29_to_32

/-- Abstract-facing alias. No general Ribet theorem is claimed. -/
def Ribet_level_lowering_abstract : Prop :=
  ribet_level_lowering_29_to_32

#check ribet_level_lowering_29_to_32
#check Ribet_928_to_32
#check Ribet_level_lowering_abstract

end BealMatveevBeal.RibetCurve