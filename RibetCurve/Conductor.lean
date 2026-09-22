/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.GaloisRep
import Ribet_928_to_32_Numerical
import Tate_Frey_Conductor_29

/-!
# Néron-conductor scaffold

The values `32` and `928` in the current project are values of a displayed
selector. They are not yet identified with the Néron conductor of the Frey
curve. A precise local conductor exponent at `29` requires Tate's
algorithm, Kodaira data, and the associated Galois representation.
-/

namespace BealMatveevBeal.RibetCurve

open BealMatveevBeal.Ribet_928_to_32_Numerical

/-- Missing local Néron conductor exponent at `29`. -/
def Frey_local_conductor_exponent_at_29 : Prop :=
  BealMatveevBeal.Tate_Frey_Conductor_29.Tate_algorithm_at_29

/-- Missing identification of the displayed `32`/`928` split with the
actual Néron conductor. -/
def Frey_Neron_conductor_is_32_or_928 : Prop :=
  BealMatveevBeal.Tate_Frey_Conductor_29.Frey_Neron_conductor

/-- Displayed selector value `32`; this is not a conductor theorem. -/
theorem displayed_level_eq_32 {A B : ℕ}
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 32 :=
  displayed_residual_selector_eq_32 hA hB

/-- Displayed selector value `928`; this is not a conductor theorem. -/
theorem displayed_level_eq_928 {A B : ℕ}
    (h : 29 ∣ A ∨ 29 ∣ B) :
    BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 928 :=
  displayed_residual_selector_eq_928 h

#check Frey_local_conductor_exponent_at_29
#check Frey_Neron_conductor_is_32_or_928
#check displayed_level_eq_32
#check displayed_level_eq_928

end BealMatveevBeal.RibetCurve