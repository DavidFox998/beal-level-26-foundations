/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import TateCurve.TateParameter
import TateGalois
import Mathlib.GroupTheory.QuotientGroup.Basic
import Mathlib.AlgebraicGeometry.EllipticCurve.Weierstrass

/-!
# Tate-uniformization scaffold at `29`

The missing theorem must construct `E_q = 𝔾ₘ / q^ℤ`, identify it with the
base change of the displayed Frey curve to `ℚ_[29]`, and prove
`j(E_q) = j(q)` for the full Tate series

`j(q) = q⁻¹ + 744 + 196884q + ⋯`.

The project currently has only a truncated expression and valuation facts.
Those do not construct the curve or the isomorphism.
-/

namespace BealMatveevBeal.TateCurve

/-- The cyclic subgroup `q^ℤ ⊆ Kˣ`. -/
def TatePowerSubgroup {K : Type*} [Field K] (v : K → ℤ)
    (tq : TateParameter K v) : Subgroup Kˣ :=
  Subgroup.zpowers (Units.mk0 tq.q tq.h_q_nonzero)

/-- The multiplicative quotient underlying a Tate curve.

This is the honest group quotient `Kˣ / q^ℤ`; it is not yet equipped with the
analytic functions or Weierstrass model required for a Tate elliptic curve. -/
abbrev TateMultiplicativeQuotient {K : Type*} [Field K] (v : K → ℤ)
    (tq : TateParameter K v) :=
  Kˣ ⧸ TatePowerSubgroup v tq

/-- The finite expression currently available in the project. It is only the
displayed beginning of the Tate `j`-expansion. -/
def tateJTruncation {K : Type*} [Field K] (q : K) : K :=
  q⁻¹ + 744 + 196884 * q

/-- Data required from the full Tate `j`-series.

The remainder field prevents the first three displayed terms from being
misrepresented as the full series. Constructing this data over `ℚ_29` requires
the convergent infinite expansion and its inversion on the open unit disc. -/
structure FullTateJSeries (K : Type*) [Field K] where
  j : K → K
  remainder : K → K
  expansion :
    ∀ q : K, q ≠ 0 →
      j q = tateJTruncation q + q ^ 2 * remainder q

set_option genInjectivity false

/-- Complete forward data needed to identify a Tate curve with the displayed
Frey curve over `ℚ_29`.

The proposition-valued fields are obligations, not defaults. No value of this
structure is constructed in the pinned library. -/
structure TateUniformizationData (A B : ℕ)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) where
  parameter : TateParameter ℚ_29 v_29
  parameter_valuation :
    v_29 parameter.q = 26 * (padicValNat 29 (B + 3) : ℤ)
  jSeries : FullTateJSeries ℚ_29
  tateCurve : EllipticCurve ℚ_29
  freyBaseChange : EllipticCurve ℚ_29
  j_tate_eq_series : tateCurve.j = jSeries.j parameter.q
  frey_j_eq_series : freyBaseChange.j = jSeries.j parameter.q
  curve_isomorphism :
    BealMatveevBeal.TateGalois.tate_curve_at_29

set_option genInjectivity true

/-- Missing Tate-uniformization theorem for every displayed Frey solution. -/
def tate_curve_at_29 : Prop :=
  ∀ (A B : ℕ) (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13),
    Nonempty (TateUniformizationData A B hsol)

/-- Forward name for the same uninhabited construction boundary. -/
def Tate_uniformization : Prop :=
  tate_curve_at_29

/-- Curve-attached Tate-parameter target, separated from full
uniformization so the valid forward implication can be stated explicitly. -/
def Tate_q : Prop :=
  ∀ (A B : ℕ) (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13),
    Frey_Tate_q_at_29 A B hsol

/-- Full uniformization data supplies the attached parameter. The converse is
not asserted. -/
theorem tate_uniformization_to_parameter :
    Tate_uniformization → Tate_q := by
  intro h A B hsol
  rcases h A B hsol with ⟨data⟩
  exact ⟨data.parameter, data.parameter_valuation⟩

#check TatePowerSubgroup
#check TateMultiplicativeQuotient
#check tateJTruncation
#check FullTateJSeries
#check TateUniformizationData
#check tate_curve_at_29
#check Tate_uniformization
#check Tate_q
#check tate_uniformization_to_parameter

end BealMatveevBeal.TateCurve