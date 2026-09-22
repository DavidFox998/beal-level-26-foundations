/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import SerreImageFull
import Mathlib.NumberTheory.ModularForms.Basic

/-!
# Modularity boundary for the Frey curve

Mathlib 4.12 has modular-form spaces but does not supply the modularity
theorem for the displayed Frey elliptic curve. This module gives the
existing uninhabited project boundary a library-facing name. It does not
replace modularity by `True`.
-/

namespace BealMatveevBeal.RibetCurve

/-- Wiles/BCDT modularity specialized to the displayed semistable Frey
curve. This remains an uninhabited proposition boundary. -/
def modular_Frey : Prop :=
  BealMatveevBeal.SerreImageFull.modularity_Frey_semistable

#check modular_Frey

end BealMatveevBeal.RibetCurve