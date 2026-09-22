/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Mathlib.Data.Int.Defs
import Mathlib.RingTheory.Valuation.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Tate_Frey_Conductor_29_Numerical

/-!
# Tate-parameter scaffold at `29`

Mathlib at the pinned Lean 4.12 revision has the field `ℚ_[29]` and its
valuation, but not a Tate curve attached to an elliptic curve. This module
records the data a future construction must produce. It proves no
uniformization theorem.
-/

namespace BealMatveevBeal.TateCurve

/-- The local field used throughout the Tate-at-`29` development. -/
abbrev ℚ_29 := ℚ_[29]

/-- The integer-valued `29`-adic valuation supplied by Mathlib.

`Valuation` is a bundled map with an explicit value monoid, not a typeclass,
so the Tate-parameter structure below takes its integer-valued valuation as an
explicit argument. -/
noncomputable def v_29 : ℚ_29 → ℤ :=
  Padic.valuation

/-- A nonzero field element with positive value for a specified
integer-valued valuation. The valuation is an explicit argument because
`Valuation` is a bundled map, not a typeclass. -/
structure TateParameter (K : Type*) [Field K] (v : K → ℤ) where
  q : K
  h_q_nonzero : q ≠ 0
  h_q_valuation_pos : 0 < v q

/-- The numerical valuation target for a Tate parameter is already proved for
the displayed Frey discriminant. This theorem does not construct a parameter
or identify the discriminant as minimal. -/
theorem frey_discriminant_valuation_target {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    v_29 (BealMatveevBeal.Tate_I29_Inertia.freyDisc_in_Qp29 A B) =
      26 * (padicValNat 29 (B + 3) : ℤ) :=
  BealMatveevBeal.Tate_Frey_Conductor_29_Numerical.valuation_discriminant_at_29
    hsol hBpos hA hB

/-- Missing construction of a Tate parameter for the displayed Frey curve.

The equation records the proved target value. It does not assert that an
arbitrary element of this valuation is attached to the Frey curve by the
full Tate `j`-series. -/
def Frey_Tate_q_at_29 (A B : ℕ)
    (_hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) : Prop :=
  ∃ tq : TateParameter ℚ_29 v_29,
    v_29 tq.q = 26 * (padicValNat 29 (B + 3) : ℤ)

#check ℚ_29
#check v_29
#check TateParameter
#check frey_discriminant_valuation_target
#check Frey_Tate_q_at_29

end BealMatveevBeal.TateCurve