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

/-- Evidence that Tate's algorithm has actually identified the displayed
Kodaira symbol. The last two fields are the missing mathematical steps, not
computed defaults. -/
structure TateAlgorithmAt29 (A B : ℕ) where
  symbol : KodairaType
  symbol_eq : symbol = Frey_Kodaira_at_29 A B
  c4_is_a_29_adic_unit :
    ¬ 29 ∣ A → ¬ 29 ∣ B →
      padicValInt 29
        (BealMatveevBeal.DarmonMerelFrey4413.frey_c4 A B) = 0
  algorithm_returns_symbol :
    BealMatveevBeal.Tate_Frey_Conductor_29.Tate_algorithm_at_29

/-- Data needed to identify the formal Néron conductor with the displayed
`32`/`928` selector. -/
structure FreyNeronConductorData (A B : ℕ) where
  tateAlgorithm : TateAlgorithmAt29 A B
  localExponentAt29 : ℕ
  neronModelConstructed :
    BealMatveevBeal.Tate_Frey_Conductor_29.Frey_Neron_conductor
  conductorIdentified :
    BealMatveevBeal.Tate_Frey_Conductor_29.Frey_conductor_29_is_Neron
  level32_when_29_coprime :
    ¬ 29 ∣ A → ¬ 29 ∣ B →
      BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 32
  level928_when_29_divides :
    29 ∣ A ∨ 29 ∣ B →
      BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 928

/-- Forward boundary: construct Tate-algorithm and Néron-model evidence for
each curve after constructing its Tate parameter. -/
def Frey_Neron_conductor : Prop :=
  Tate_q →
    ∀ A B : ℕ, Nonempty (FreyNeronConductorData A B)

/-- Forward implication still missing from the pinned library.

This direction is intentional: one must construct `Tate_q`, then the Néron
conductor, and only then identify the displayed `29`-split. The existing
conductor placeholder cannot be used backwards to derive uniformization. -/
def Frey_conductor_29_is_Neron : Prop :=
  Tate_uniformization → Frey_Neron_conductor

#check KodairaType
#check Frey_Kodaira_at_29
#check TateAlgorithmAt29
#check FreyNeronConductorData
#check Frey_Neron_conductor
#check Frey_conductor_29_is_Neron

end BealMatveevBeal.TateCurve