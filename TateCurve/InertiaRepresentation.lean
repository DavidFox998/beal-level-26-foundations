/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import TateCurve.NeronConductor
import Mathlib.RepresentationTheory.Basic
import Level928Table
import Ribet29C_Lowering

/-!
# Inertia-representation scaffold

The pinned library has general representation and valuation infrastructure,
but no elliptic-curve representation `ρ̄_{E,13}`, no action of inertia on
`E[13]`, and no Tate-curve cyclotomic inertia formula.
-/

namespace BealMatveevBeal.TateCurve

/-- Missing full statement `ρ̄_{E,13}(I₂₉) = 1` under the Tate-parameter
divisibility criterion. It remains the existing uninhabited boundary. -/
def inertia_at_29_trivial_mod13_full : Prop :=
  BealMatveevBeal.TateGalois.inertia_at_29_trivial_mod13_full

/-- Forward alias for the intended consequence of
`13 ∣ v₂₉(q)`: inertia acts trivially mod `13`. -/
def inertia_trivial_mod13_when_13_dvd_v : Prop :=
  inertia_at_29_trivial_mod13_full

/-- Existing global odd residual estimate. It contains all odd prime
divisors of `A * B`; it is not a local conductor at `29`. -/
def residualOddEstimate (A B : ℕ) : ℕ :=
  BealMatveevBeal.Level928Table.residualOddEstimate A B

/-- Global residual-level target.

Local Tate theory at `29` cannot prove this by itself: every odd prime
dividing `A * B` must also disappear, requiring global level lowering at
those primes or a proof that no relevant solution exists. -/
def ribet_unramified_at_29_of_dvd_C : Prop :=
  ∀ A B : ℕ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
    29 ∣ B + 3 →
    ¬ 29 ∣ A →
    ¬ 29 ∣ B →
    residualOddEstimate A B ∣ 32

#check inertia_at_29_trivial_mod13_full
#check inertia_trivial_mod13_when_13_dvd_v
#check residualOddEstimate
#check ribet_unramified_at_29_of_dvd_C

end BealMatveevBeal.TateCurve