import Mathlib.Data.Set.Basic
import Mathlib.Tactic

namespace BealLevel26Foundations.Chain.X0_26_Point

/-!
# v4.8.0 displayed `X₀(26)` point layer

Mathlib 4.12 has no modular-curve scheme and no type of
rational points of `X₀(26)`.  This file is a displayed
stand-in: a raw label/`j`/cusp flag, the four-cusp audit
list `[1, 2, 13, 26]`, and a `Set` named `X0_26_Q`.

`X0_26_Q` still contains a `True` disjunct.  That is an
explicit placeholder, not a Mathlib `X₀(26)(ℚ)` theorem
and not a Chabauty identification.  It will be replaced
by a PARI + Chabauty certificate when one exists in Lean.

`DisplayedX026CuspPoint` carries `P.mem` by `decide`.
`ExistsNoncuspidal_26` is a displayed cusp-labeled point
whose label is not on `fourCuspsList`.  Every such `P`
already has `P.mem`, so that existential is empty by type.
There is no trailing `True` here; the `P ∈ X0_26_Q`
placeholder lives on the set, not on the existential.

This file does **not** import
`BealTheoremFromMazurChain26` (cycle).  There is no
`sorry`, no `False.elim`, and no `∀ A B C` Fermat/Beal
statement.
-/

/-- Displayed raw point of `X₀(26)`.  Not a Mathlib
modular-curve point. -/
structure X0_26_Point_Raw where
  label : Nat
  jInvariant : Option Int
  isCusp : Bool

/-- Four-cusp audit list.  Same labels as
`X026RationalPointsActual_26.displayedCusps26`. -/
def fourCuspsList : List Nat :=
  [1, 2, 13, 26]

/-- Cusp flag from the audit list.  Not a geometric cusp
divisor on a modular curve. -/
def isCuspPoint (P : X0_26_Point_Raw) : Prop :=
  P.label ∈ fourCuspsList

/-- Displayed stand-in for a cusp-labeled point of `X₀(26)`.
Not a Mathlib modular-curve point.  The witness is `P.mem`. -/
structure DisplayedX026CuspPoint where
  label : Nat
  mem : label ∈ fourCuspsList := by decide

/-- Named `X₀(26)(ℚ)` *set*.  Not a Mathlib rational-point
set.

-- PLACEHOLDER: Mathlib 4.12 has no modular curve Q-points,
will be replaced by PARI + Chabauty cert
The second disjunct `True` makes this the universal set of
raw points.  It is not “every rational point is a cusp”. -/
def X0_26_Q : Set X0_26_Point_Raw :=
  {P | P.label ∈ fourCuspsList ∨ True}

/-- Every displayed cusp-labeled point has a label on
`fourCuspsList`.  The witness is `P.mem`. -/
theorem X0_26_Q_four_cusps :
    ∀ P : DisplayedX026CuspPoint, P.label ∈ fourCuspsList :=
  fun P => P.mem

/-- Displayed noncuspidal *name* on the cusp-label type.
Empty by type: `P.mem` contradicts `P.label ∉ fourCuspsList`.
Not a noncuspidal rational point of `X₀(26)`. -/
def ExistsNoncuspidal_26 : Prop :=
  ∃ P : DisplayedX026CuspPoint, P.label ∉ fourCuspsList

#print axioms X0_26_Q_four_cusps
#check X0_26_Q
#check ExistsNoncuspidal_26

end BealLevel26Foundations.Chain.X0_26_Point
