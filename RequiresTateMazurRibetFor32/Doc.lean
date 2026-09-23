/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Conditional32Newform.Bridge
import TateCurve.BlockerDoc
import MazurCurve.BlockerDoc
import RibetCurve.BlockerDoc
import KolyvaginCurve.BlockerDoc

/-!
# Why level `32` remains conditional at baseline `43735b3`

The pinned library proves the displayed Frey discriminant

`Δ = 16 A⁸ B⁸ (A⁴ + B⁴)²`,

the valuation identity `v₂₉(Δ) = 26 v₂₉(B+3)`, the divisibility
`13 ∣ v₂₉(Δ)`, and the arithmetic `928 / 29 = 32` and `32 * 29 = 928`.
These are necessary numerical inputs.  They do not construct an unconditional
level-`32` newform.

A genuine unconditional theorem still requires actual terms for four
semantically closed, library-scale foundations:

1. Wiles/BCDT modularity specialized to the displayed Frey curve;
2. Frey-specific mod-`13` irreducibility, obtained from the Mazur/Fricke
   analysis rather than from the bare inequality `48 < 2184`;
3. Tate uniformization, the local Néron model and conductor, and the inertia
   theorem at `29`; and
4. Ribet level lowering that produces residual eigenform data at level `32`.

The bridge theorem takes the exposed Mazur, Tate, and Ribet boundaries as
hypotheses.  Its conclusion is therefore a conditional evidence record, not a
Mathlib modular-form object.  No converse is used and none of these obligations
is inhabited here.

Formal `L`-functions and Kolyvagin rank-zero theory are not inputs to the
level-lowering argument.  Their blocker module is imported only to make this
separation explicit: analytic rank and Mordell--Weil finiteness cannot replace
modularity, local conductor theory, irreducibility, or Ribet lowering.
-/

namespace BealMatveevBeal.RequiresTateMazurRibetFor32

open BealMatveevBeal.Conditional32Newform

/-- The four principal foundations required for a genuinely unconditional
level-`32` newform construction at this pin.  No inhabitant is supplied. -/
structure PrincipalFoundations : Prop where
  freyModularity : BealMatveevBeal.RibetCurve.modular_Frey
  freySpecificIrreducibility :
    BealMatveevBeal.Mazur_X0_13_No_Isogeny.frey_no_rational_13_isogeny
  localNeronAndInertia :
    BealMatveevBeal.Tate_Frey_Conductor_29.Frey_conductor_29_is_Neron
  ribetLevelLowering :
    BealMatveevBeal.Ribet_Level_Lowering_29_to_32.Ribet_928_to_32

/-- The unconditional statement whose proof is unavailable at the pinned
revision.  It is deliberately a proposition with no default inhabitant. -/
def UnconditionalHasNewformAtLevel32 : Prop :=
  ∀ {A B : ℕ},
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
    1 ≤ B →
    ¬ 29 ∣ A →
    ¬ 29 ∣ B →
    29 ∣ B + 3 →
      HasNewformAtLevel32 A B

#check PrincipalFoundations
#check UnconditionalHasNewformAtLevel32

end BealMatveevBeal.RequiresTateMazurRibetFor32