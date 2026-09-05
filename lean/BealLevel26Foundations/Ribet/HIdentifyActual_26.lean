import BealLevel26Foundations.FiniteEvidence
import BealLevel26Foundations.Jacobian.J0_26_Q_RankZeroActual_26
import BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
import BealLevel26Foundations.Mazur.EndgameScaffold
import BealLevel26Foundations.Mazur.X026RationalPointsActual_26
import BealLevel26Foundations.Ribet.NoFreyPointActual_26
import BealLevel26Foundations.Ribet.RibetLoweringActual_26
import Mathlib.Tactic

namespace BealLevel26Foundations.Ribet.HIdentifyActual26

open BealLevel26Foundations.FiniteEvidence
open BealLevel26Foundations.Jacobian.J0_26_Q_RankZeroActual26
open BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
open BealLevel26Foundations.Mazur.EndgameScaffold
open BealLevel26Foundations.Mazur.X026RationalPointsActual26
open BealLevel26Foundations.Ribet.NoFreyPointActual26
open BealLevel26Foundations.Ribet.RibetLoweringActual26

/-!
# v4.0.7 typed `hIdentify` is uninhabitable as a finite package

The geometric content of `hIdentify` is: a Frey curve attached to a
primitive Beal solution, after Ribet lowering to level `26`, gives a
*noncuspidal* rational point of `X₀(26)`.  Mathlib 4.12 has no
modular-curve point API and no residual Galois-representation API
that would construct such a point.  This file does not add a
certificate and does not identify eight S-units with genuine
cohomological `Sel₂`.  Sources remain the frozen v1.4.0 ledger
SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`.

The *typed* EndgameScaffold hypothesis

`ExistsFreyWitness → ExistsNoncuspidalLevel26FreyPoint`

is a different statement.  `ExistsFreyWitness` is the displayed
target `loweredLevel = 26` (inhabited).  `ExistsNoncuspidal` also
requires `26 ∉ [1, 2, 13, 26]`.  The four-cusp package proves
`26 ∈ [1, 2, 13, 26]`, so `ExistsNoncuspidal` is false.  The typed
implication is therefore `True → False` and is uninhabitable.

A displayed level-26 target is the *cusp* labelled by the divisor
`26`, not a noncuspidal Frey point.  Identifying them would
contradict `sUnitAudit26_is_not_genuine_2Selmer` only if one also
mislabeled the eight S-units as `Sel₂`; this file does neither.

This module therefore records the finite package and proves
`hIdentify_typed_is_uninhabitable`.  It does not inhabit
`hIdentify`, and it does not add `theorem BealTheorem`.
-/

/-- Finite record of the two halves already inhabited, plus the
four-cusp membership that blocks the typed implication. -/
def hIdentifyFinitePackage : Prop :=
  ExistsFreyWitness ∧
    ¬ ExistsNoncuspidalLevel26FreyPoint ∧
    displayedCusps26 = [1, 2, 13, 26] ∧
    displayedCusps26.length = 4 ∧
    26 ∈ displayedCusps26 ∧
    displayedTargetLevel26 = 26 ∧
    J0_26_Q_RankZero26.of_qExpansion.rankZero ∧
    MwrankCertificateSoundness_26 ∧
    sUnitAudit26.card = 8 ∧
    sUnitAudit26 ≠ ({⟨0, by decide⟩} : Finset SUnitIndex)

theorem hIdentifyFinitePackage.certified :
    hIdentifyFinitePackage :=
  ⟨displayedFreyWitness26_exists,
    noNoncuspidalLevel26FreyPoint,
    rfl,
    displayedCusps26_length,
    by
      simp [displayedCusps26],
    displayedTargetLevel26_eq,
    J0_26_Q_RankZero26.of_qExpansion_replaces_premise,
    MwrankCertificateSoundness_26.certified,
    sUnitAudit26_retains_all_eight,
    sUnitAudit26_not_singleton⟩

/-- The typed EndgameScaffold `hIdentify` cannot be supplied from
the displayed target `26` and the four-cusp list. -/
theorem hIdentify_typed_is_uninhabitable :
    ¬ (ExistsFreyWitness → ExistsNoncuspidalLevel26FreyPoint) := by
  intro hId
  exact noNoncuspidalLevel26FreyPoint (hId existsFreyWitness26)

theorem hIdentify_typed_contradicts_four_cusps
    (h :
      X0_26_RationalPoints26.of_qExpansion.rationalPointsAreFourCusps) :
    ¬ (ExistsFreyWitness → ExistsNoncuspidalLevel26FreyPoint) := by
  intro hId
  exact NoFreyPoint26.not_exists h (hId existsFreyWitness26)

/-- The remaining geometric gate: a Frey curve from a Beal
counterexample is a noncuspidal `X₀(26)` point.  That is not the
typed implication above, and it is not discharged here. -/
def remainingGeometricIdentify : Prop :=
  hIdentifyFinitePackage ∧
    ¬ (ExistsFreyWitness → ExistsNoncuspidalLevel26FreyPoint) ∧
    sUnitAudit26.card = 8 ∧
    sUnitAudit26 ≠ ({⟨0, by decide⟩} : Finset SUnitIndex)

theorem remainingGeometricIdentify.certified :
    remainingGeometricIdentify :=
  ⟨hIdentifyFinitePackage.certified,
    hIdentify_typed_is_uninhabitable,
    sUnitAudit26_retains_all_eight,
    sUnitAudit26_not_singleton⟩

#print axioms hIdentifyFinitePackage.certified
#print axioms hIdentify_typed_is_uninhabitable
#print axioms hIdentify_typed_contradicts_four_cusps
#print axioms remainingGeometricIdentify.certified

end BealLevel26Foundations.Ribet.HIdentifyActual26
