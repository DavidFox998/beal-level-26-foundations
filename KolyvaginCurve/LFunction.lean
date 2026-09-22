/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.Periods
import Mathlib.Analysis.Complex.Basic

/-!
# Elliptic-curve `L`-function scaffold

Mathlib 4.12 has no elliptic-curve `L`-function object connecting the two
Cremona curves to the displayed rational `L/Ω` values. Consequently
`L_26a1` and `L_26b1` below are proposition boundaries for the missing
objects, not functions asserted to exist.
-/

namespace BealMatveevBeal.KolyvaginCurve

/-- Boundary for constructing the `26a1` elliptic-curve `L`-function. -/
def L_26a1 : Prop :=
  BealMatveevBeal.J0_26_BSD_26a1_26b1.L_26a1_ne_zero

/-- Boundary for constructing the `26b1` elliptic-curve `L`-function. -/
def L_26b1 : Prop :=
  BealMatveevBeal.J0_26_BSD_26a1_26b1.L_26b1_ne_zero

/-- Actual analytic nonvanishing boundary for `L(26a1,1)`. The displayed
`1/3 ≠ 0` does not inhabit it. -/
def L_26a1_ne_zero : Prop :=
  L_over_Omega_26a1 = (1 / 3 : ℚ) →
    BealMatveevBeal.X0_26_Full2Torsion.J0_26_rank0

/-- Actual analytic nonvanishing boundary for `L(26b1,1)`. -/
def L_26b1_ne_zero : Prop :=
  L_over_Omega_26b1 = (1 / 7 : ℚ) →
    BealMatveevBeal.X0_26_Full2Torsion.J0_26_rank0

#check L_26a1
#check L_26b1
#check L_26a1_ne_zero
#check L_26b1_ne_zero

end BealMatveevBeal.KolyvaginCurve