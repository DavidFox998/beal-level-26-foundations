/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import BSD_MordellWeil
import Mathlib.Analysis.Complex.Basic

/-!
# Elliptic-curve `L`-function interface

Mathlib 4.12 does not construct the Hasse--Weil `L`-function of an elliptic
curve.  This module defines the typed analytic object required by the
Kolyvagin argument.  It deliberately provides no arbitrary default object
and proves no Euler product, analytic continuation, or curve attachment.
-/

namespace BealMatveevBeal.KolyvaginCurve

open BealMatveevBeal.BSD_MordellWeil

/-- Analytic data denoted by `L(E,s)` once the Hasse--Weil construction and
its attachment to `E` have been formalized.  The curve parameter prevents
data for different curves from being interchanged. -/
structure EllipticCurveLFunction (E : WeierstrassCurve ℚ) where
  value : ℂ → ℂ

instance {E : WeierstrassCurve ℚ} :
    CoeFun (EllipticCurveLFunction E) (fun _ => ℂ → ℂ) :=
  ⟨EllipticCurveLFunction.value⟩

/-- The exact analytic input used by Kolyvagin: `L(E,1) ≠ 0`. -/
def EllipticCurveLFunction.NonzeroAtOne
    {E : WeierstrassCurve ℚ} (L : EllipticCurveLFunction E) : Prop :=
  L 1 ≠ 0

/-- Type of a formal Hasse--Weil `L`-function for the displayed `26a1`
curve.  No term of this type is selected by this library. -/
abbrev L_26a1 :=
  EllipticCurveLFunction curve26a1_Q

/-- Type of a formal Hasse--Weil `L`-function for the displayed `26b1`
curve.  No term of this type is selected by this library. -/
abbrev L_26b1 :=
  EllipticCurveLFunction curve26b1_Q

/-- Formal analytic nonvanishing predicate for `26a1`, parameterized by the
constructed `L`-function rather than by the displayed rational quotient. -/
def L_26a1_ne_zero (L : L_26a1) : Prop :=
  L.NonzeroAtOne

/-- Formal analytic nonvanishing predicate for `26b1`. -/
def L_26b1_ne_zero (L : L_26b1) : Prop :=
  L.NonzeroAtOne

#check EllipticCurveLFunction
#check EllipticCurveLFunction.NonzeroAtOne
#check L_26a1
#check L_26b1
#check L_26a1_ne_zero
#check L_26b1_ne_zero

end BealMatveevBeal.KolyvaginCurve