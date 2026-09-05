import BealLevel26Foundations.Chain.FreyCurve_13_26
import BealLevel26Foundations.Chain.RationalPoints_26_FourCusps_26
import BealLevel26Foundations.Mazur.EndgameScaffold

namespace BealLevel26Foundations.Final

open BealLevel26Foundations.Chain.Frey13
open BealLevel26Foundations.Chain.X0_26_FourCusps
open BealLevel26Foundations.Mazur.EndgameScaffold

/-!
# v4.3.0 Final ∀ *package* for exponent 13

`BealExponent13_Final_Package` is

`X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`.

That records PARI `|Sel₂| = 1` twice (`1 = 1`), `det M₃ = 2`,
the displayed Frey level `2 * 13 = 26`, and the cusp-point audit
forall over `DisplayedX026CuspPoint`.  It is not
`∀ A B C, ¬ A^13 + B^13 = C^13`.

Blueprint: rank 0 plus formal immersion would force
`X₀(26)(ℚ)` onto the four cusps, and a Frey curve from
`A^13+B^13=C^13` would be a noncuspidal point.  Mathlib 4.12
has no Ribet, no `SelmerGroup`, no `MordellWeil.rank`, and no
`X0_26_Point`.  A `∀` proof by vacuous contradiction would put
`False` in the kernel.  Typed
`fourCusps → ¬ ExistsNoncuspidal` stays uninhabitable
(`True → ¬True`).

This file does **not** import `BealTheoremFromMazurChain26`.
`X026RationalPointsActual_26` is unchanged.  Descent SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.
-/

/-- Computational final package.  Not a Fermat / Beal forall. -/
def BealExponent13_Final_Package : Prop :=
  X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints

theorem BealExponent13_Final_Package.certified :
    BealExponent13_Final_Package :=
  ⟨X0_26_Q_four.certified, freyLevel26_computational,
    fourCuspsForallCuspPoints.certified⟩

#print axioms BealExponent13_Final_Package.certified

end BealLevel26Foundations.Final
