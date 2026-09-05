import BealLevel26Foundations.Jacobian.FormalImmersionActual_26
import BealLevel26Foundations.Jacobian.J0_26_DecompActual
import BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
import BealLevel26Foundations.Mazur.EndgameScaffold
import BealLevel26Foundations.Mazur.X026RationalPointsActual_26
import Mathlib.Tactic

namespace BealLevel26Foundations.Ribet.NoFreyPointActual26

open BealLevel26Foundations.Jacobian.FormalImmersionActual26
open BealLevel26Foundations.Jacobian.J0_26_DecompActual
open BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
open BealLevel26Foundations.Mazur.EndgameScaffold
open BealLevel26Foundations.Mazur.X026RationalPointsActual26

/-!
# v4.0.6 four-cusp absence (`¬ ExistsNoncuspidal`)

This module is the *absence* half of the former combined
`NoFreyPointActual_26`.  Ribet existence (`ExistsFreyWitness`,
`loweredLevel = 26`) lives in `RibetLoweringActual_26`.  This file
does not inhabit that existence proposition.

It loads the v1.4.0 sources

* `sagemath/level_26_ledger.json`
  (SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`);
* `sagemath/certs/j0_26_decomposition.json`;
* `sagemath/certs/formal_immersion_M3.json`

as the already-promoted Lean four-cusp package
`X0_26_RationalPoints26.of_qExpansion`.  The displayed cusps are
the divisors `[1, 2, 13, 26]` of length `4`.  A noncuspidal
level-26 witness would need `loweredLevel = 26` and
`26 ∉ [1, 2, 13, 26]`.  Those are incompatible, so
`¬ ExistsNoncuspidalLevel26FreyPoint`.

This is not a scheme-theoretic statement that a Frey point is
absent from `X₀(26)(ℚ)`.  Mathlib 4.12 has no modular-curve
rational-point API.  It does not add a certificate.
-/

theorem displayedCusps26_contain_26
    (h : X0_26_RationalPoints26.of_qExpansion.rationalPointsAreFourCusps) :
    displayedCusps26.length = 4 ∧
      displayedCusps26 = [1, 2, 13, 26] ∧
      26 ∈ displayedCusps26 :=
  ⟨h.1, h.2.1, by
    rw [h.2.1]
    decide⟩

theorem twentySix_mem_four_displayed_cusps :
    26 ∈ ([1, 2, 13, 26] : List Nat) := by
  decide

/-- Absence of a *noncuspidal* level-26 Frey witness, from the
displayed four-cusp list.  Not from Ribet existence. -/
theorem NoFreyPoint26.not_exists
    (h : X0_26_RationalPoints26.of_qExpansion.rationalPointsAreFourCusps) :
    ¬ ExistsNoncuspidalLevel26FreyPoint := by
  intro w
  obtain ⟨pt⟩ := w
  have hlist : displayedCusps26 = [1, 2, 13, 26] :=
    (displayedCusps26_contain_26 h).2.1
  have hlen : displayedCusps26.length = 4 :=
    (displayedCusps26_contain_26 h).1
  have hmem : pt.loweredLevel ∈ ([1, 2, 13, 26] : List Nat) := by
    rw [pt.loweredLevel_eq_26]
    exact twentySix_mem_four_displayed_cusps
  let _pin := And.intro hlist hlen
  exact pt.notDisplayedCusp hmem

/-- Unconditional absence: the of_qExpansion four-cusp package is
already certified. -/
theorem noNoncuspidalLevel26FreyPoint :
    ¬ ExistsNoncuspidalLevel26FreyPoint :=
  NoFreyPoint26.not_exists fourCuspsFromQExpansion.certified

/-- Finite package that inhabits the Mazur `NoFreyPoint26` premise
by the four-cusp *negation*, not by Ribet existence. -/
def NoFreyPoint26.of_qExpansion : NoFreyPoint26 where
  displayedTargetLevel := 26
  displayedTargetLevel_eq_26 := rfl
  noNoncuspidalFrey := noNoncuspidalLevel26FreyPoint
  ofFourCusps := fun _hPts _hCusps =>
    noNoncuspidalLevel26FreyPoint

theorem NoFreyPoint26.of_qExpansion_replaces_premise :
    NoFreyPoint26.of_qExpansion.displayedTargetLevel = 26 ∧
      ¬ ExistsNoncuspidalLevel26FreyPoint :=
  ⟨NoFreyPoint26.of_qExpansion.displayedTargetLevel_eq_26,
    NoFreyPoint26.of_qExpansion.noNoncuspidalFrey⟩

/-- `hGeomForbid` inhabitant: four displayed cusps imply
`¬ ExistsNoncuspidal`. -/
theorem hGeomForbid_of_qExpansion :
    X0_26_RationalPoints26.of_qExpansion.rationalPointsAreFourCusps →
      ¬ ExistsNoncuspidalLevel26FreyPoint :=
  NoFreyPoint26.not_exists

#print axioms displayedCusps26_contain_26
#print axioms NoFreyPoint26.not_exists
#print axioms noNoncuspidalLevel26FreyPoint
#print axioms NoFreyPoint26.of_qExpansion_replaces_premise
#print axioms hGeomForbid_of_qExpansion

end BealLevel26Foundations.Ribet.NoFreyPointActual26
