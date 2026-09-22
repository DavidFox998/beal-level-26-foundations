/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import TateCurve.TateUniformization
import Mathlib.Data.Nat.Prime.Basic
import Tate_Frey_Conductor_29_Numerical

/-!
# Kodaira and Néron-conductor scaffold

The constructors below name the expected Kodaira symbols. No Tate algorithm
or Néron model is present in the pinned library. In particular, the displayed
`32`/`928` selector is not reinterpreted as a proved Néron conductor.
-/

namespace BealMatveevBeal.TateCurve

/-- Minimal Kodaira-symbol vocabulary needed by the planned local argument. -/
inductive KodairaType where
  | I0
  | In : ℕ → KodairaType
  | I0star
  | In_star : ℕ → KodairaType
  deriving DecidableEq, Repr

/-- Expected numerical symbol at `29`. This is a definition of the target
symbol, not a theorem that Tate's algorithm returns it. -/
def Frey_Kodaira_at_29 (_A B : ℕ) : KodairaType :=
  .In (26 * padicValNat 29 (B + 3))

/-- Forward boundary: a curve-attached Tate parameter is required before a
formal Néron-conductor identification can be constructed. -/
def Frey_Neron_conductor : Prop :=
  Tate_q

/-- Forward implication still missing from the pinned library.

This direction is intentional: one must construct `Tate_q`, then the Néron
conductor, and only then identify the displayed `29`-split. The existing
conductor placeholder cannot be used backwards to derive uniformization. -/
def Frey_conductor_29_is_Neron : Prop :=
  Frey_Neron_conductor →
    BealMatveevBeal.Tate_Frey_Conductor_29.Frey_conductor_29_is_Neron

#check KodairaType
#check Frey_Kodaira_at_29
#check Frey_Neron_conductor
#check Frey_conductor_29_is_Neron

end BealMatveevBeal.TateCurve