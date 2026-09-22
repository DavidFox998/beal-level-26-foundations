/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import TateCurve.TateParameter
import TateGalois

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

/-- Existing uninhabited Tate-curve boundary, re-exposed in the library
namespace. This is deliberately not defined as `True`. -/
def tate_curve_at_29 : Prop :=
  BealMatveevBeal.TateGalois.tate_curve_at_29

/-- Forward alias: constructing the Tate curve supplies uniformization. -/
def Tate_uniformization : Prop :=
  tate_curve_at_29

/-- Forward alias: uniformization supplies the curve-attached parameter. -/
def Tate_q : Prop :=
  Tate_uniformization

#check tate_curve_at_29
#check Tate_uniformization
#check Tate_q

end BealMatveevBeal.TateCurve