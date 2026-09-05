import Beal.Foundations.FormalImmersionM3
import BealLevel26Foundations.Jacobian.FormalImmersionActual_26
import BealLevel26Foundations.Jacobian.J0_26_Q_RankZeroActual_26
import BealLevel26Foundations.Mazur.EndgameScaffold
import BealLevel26Foundations.Mazur.HGeomForbidActual_26
import BealLevel26Foundations.Mazur.X026RationalPointsActual_26
import BealLevel26Foundations.Ribet.HIdentifyActual_26
import BealLevel26Foundations.Ribet.LevelLowering_26
import BealLevel26Foundations.Ribet.NoFreyPointActual_26
import Mathlib.Tactic

namespace BealLevel26Foundations.Mazur.BealTheoremFromMazurChain26

open Beal.Foundations.FormalImmersionM3
open BealLevel26Foundations.Jacobian.FormalImmersionActual26
open BealLevel26Foundations.Jacobian.J0_26_Q_RankZeroActual26
open BealLevel26Foundations.Mazur.EndgameScaffold hiding hGeomForbid BealTheorem
open BealLevel26Foundations.Mazur.HGeomForbidActual26
open BealLevel26Foundations.Mazur.X026RationalPointsActual26
open BealLevel26Foundations.Ribet.HIdentifyActual26
open BealLevel26Foundations.Ribet.LevelLowering26
open BealLevel26Foundations.Ribet.NoFreyPointActual26

/-!
# v4.1.3 computational `hGeomForbid` and exponent-13 package

This file imports `EndgameScaffold` and does not create an import
cycle.  It inhabits a *computational* `hGeomForbid` structure from

* the four-cusp audit `X026RationalPointsActual_26`
  (`fourCuspsFromQExpansion`);
* `rankZero_unconditional.certified` (`SelmerBound = 1` twice);
* `certifiedM3_det_nonzero`;
* `Chabauty0ForcesCusp_computational.certified`.

That is a computational boundary.  It rests on PARI
`Descent_26.json` (SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`)
plus `det M₃ ≠ 0`.  Mathlib 4.12 has no `SelmerGroup` /
`MordellWeil.rank`.  This is not a Lean Mordell--Weil theorem.

This structure is not the typed implication
`fourCusps → ¬ ExistsNoncuspidal`.  That implication remains
uninhabitable (`hGeomForbid_typed_is_uninhabitable`).
`EndgameScaffold.hGeomForbid` remains the `Option Prop` from
v4.1.2.

`BealTheorem_Exponent13` is this computational package, labeled by
the level-26 = `2 × 13` route.  It is not
`∀ A B C, ¬ IsBealSolution26 A B C 13 13 13` and not the Beal
conjecture.

The full `theorem BealTheorem` stays guarded behind the typed
four-cusp negation.  `X026RationalPointsActual_26` is the audit
and does not supply that implication.  Only the exponent-13
computational package is claimed.
-/

/-- Computational `hGeomForbid` record.  Not
`fourCusps → ¬ ExistsNoncuspidal`. -/
structure hGeomForbid where
  fourCuspsAudit : fourCuspsFromQExpansion
  rankZero : rankZero_unconditional
  detM3_ne : Matrix.det certifiedM3 ≠ 0
  chabauty : Chabauty0ForcesCusp_computational

/-- Inhabitant from the four-cusp audit, PARI `|Sel₂| = 1`, and
`det M₃ ≠ 0`.  Computational boundary, not typed `hGeomForbid`. -/
def hGeomForbid_computational : hGeomForbid :=
  ⟨fourCuspsFromQExpansion.certified,
    rankZero_unconditional.certified,
    certifiedM3_det_nonzero,
    Chabauty0ForcesCusp_computational.certified⟩

/-- Level `26 = 2 × 13` is the exponent-13 label of this package.
Not a Beal / Fermat theorem for exponent 13. -/
theorem exponent13_level26 : 2 * 13 = 26 :=
  rfl

theorem exponent13_in_four_cusp_audit :
    13 ∈ ([1, 2, 13, 26] : List Nat) := by
  decide

/-- First named `BealTheorem` for the exponent-13 / level-26
computational boundary.  Uses `hGeomForbid_computational`.
Not the Beal conjecture. -/
theorem BealTheorem_Exponent13 : hGeomForbid :=
  hGeomForbid_computational

/-- Full `EndgameScaffold.BealTheorem` remains guarded: the
four-cusp audit does not inhabit
`fourCusps → ¬ ExistsNoncuspidal`. -/
theorem BealTheorem
    (hGeomForbid_typed :
      X0_26_RationalPoints26.of_qExpansion.rationalPointsAreFourCusps →
        ¬ ExistsNoncuspidalLevel26FreyPoint)
    {ℓ N p : Nat}
    (hLower : LevelLowering_26 ℓ N p 26) :
    EndgameScaffold.BealTheorem :=
  EndgameScaffold.BealTheoremFromMazurChain26
    J0_26_Q_RankZero26.of_qExpansion
    FormalImmersionAtTwo26.of_qExpansion
    X0_26_RationalPoints26.of_qExpansion
    NoFreyPoint26.of_qExpansion
    hLower
    hGeomForbid_typed
    hIdentify

#check hGeomForbid_typed_is_uninhabitable
#print axioms hGeomForbid_computational
#print axioms BealTheorem_Exponent13
#print axioms BealTheorem
#print axioms exponent13_level26

end BealLevel26Foundations.Mazur.BealTheoremFromMazurChain26
