import BealLevel26Foundations.Jacobian.FormalImmersionActual_26
import BealLevel26Foundations.Jacobian.J0_26_DecompActual
import BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
import BealLevel26Foundations.Mazur.EndgameScaffold
import BealLevel26Foundations.Mazur.X026RationalPointsActual_26
import BealLevel26Foundations.Real.FreyWeierstrass
import BealLevel26Foundations.Ribet.LevelLowering_26
import Mathlib.Tactic

namespace BealLevel26Foundations.Ribet.NoFreyPointActual26

open BealLevel26Foundations.Jacobian.FormalImmersionActual26
open BealLevel26Foundations.Jacobian.J0_26_DecompActual
open BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
open BealLevel26Foundations.Mazur.EndgameScaffold
open BealLevel26Foundations.Mazur.X026RationalPointsActual26
open BealLevel26Foundations.Real.FreyWeierstrass
open BealLevel26Foundations.Ribet.LevelLowering26

/-!
# v4.0.5 displayed Ribet existence from q-expansion data

This module loads the v1.4.0 sources

* `sagemath/level_26_ledger.json`
  (SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`);
* `sagemath/certs/j0_26_decomposition.json`;
* `sagemath/certs/formal_immersion_M3.json`

as the already-promoted Lean `J0_26_DecompActual`,
`MwrankCertificateSoundness_26`,
`FormalImmersionAtTwo26.of_qExpansion`, and
`X0_26_RationalPoints26.of_qExpansion`.  It does not parse JSON and
does not add a certificate.

The displayed lowering target at squarefree level `26` is the fourth
index of `LevelLowering_26 ℓ N p 26`.  Together with the certified
`26a × 26b` q-expansion distinction, Sage `certified_mwrank = 0`,
the already-inhabited formal-immersion *input*, and the displayed
four-cusp package, that is the finite package
`ribetExistenceFromQExpansion`.

`NoFreyPoint26.of_qExpansion` inhabits the Mazur premise.
`ofFourCusps` returns that finite package and does not read a
geometric rank-zero witness.  `ofBealFreyLowering` produces the
displayed witness `loweredLevel = 26` from the typed certificate.
Mathlib 4.12 has no Ribet existence theorem.  This is not a
scheme-theoretic statement that a Frey point is absent from
`X₀(26)(ℚ)`, and `J0_26_Q_RankZero26` remains supplied.
-/

/-- Displayed target of a level-26 lowering certificate. -/
def displayedTargetLevel26 : Nat :=
  26

theorem displayedTargetLevel26_eq :
    displayedTargetLevel26 = 26 :=
  rfl

theorem lowering_to_26_target
    {ℓ N p : Nat} (c : LevelLowering_26 ℓ N p 26) :
    c.targetLevel = 26 :=
  rfl

/-- Finite Ribet-existence package from q-expansion and lowering data.
Not a Mathlib Ribet theorem. -/
def ribetExistenceFromQExpansion : Prop :=
  displayedTargetLevel26 = 26 ∧
    X0_26_RationalPoints26.of_qExpansion.displayedCuspCount = 4 ∧
    X0_26_RationalPoints26.of_qExpansion.rationalPointsAreFourCusps ∧
    FormalImmersionAtTwo26.of_qExpansion.input = !![1, 1; 0, 2] ∧
    certified26a.a2 = -1 ∧
    certified26b.a2 = 1 ∧
    MwrankCertificateSoundness_26 ∧
    ∀ {ℓ N p : Nat} (c : LevelLowering_26 ℓ N p 26), c.targetLevel = 26

theorem ribetExistenceFromQExpansion.certified :
    ribetExistenceFromQExpansion :=
  ⟨displayedTargetLevel26_eq,
    X0_26_RationalPoints26.of_qExpansion.displayedCuspCount_eq_four,
    fourCuspsFromQExpansion.certified,
    FormalImmersionAtTwo26.of_qExpansion.input_eq,
    certified26a_a2, certified26b_a2,
    MwrankCertificateSoundness_26.certified,
    fun c => lowering_to_26_target c⟩

/-- Displayed noncuspidal-level witness: the certificate target is
`26`.  This is not a point of a Mathlib modular curve. -/
def displayedFreyWitness26 : Level26FreyPointWitness where
  loweredLevel := 26
  loweredLevel_eq_26 := rfl

theorem displayedFreyWitness26_exists :
    ExistsNoncuspidalLevel26FreyPoint :=
  ⟨displayedFreyWitness26⟩

/-- Finite package that inhabits the Mazur `NoFreyPoint26` premise.
`noNoncuspidalFrey` is the displayed Ribet-existence package, not a
scheme-theoretic absence of Frey points. -/
def NoFreyPoint26.of_qExpansion : NoFreyPoint26 where
  displayedTargetLevel := displayedTargetLevel26
  displayedTargetLevel_eq_26 := displayedTargetLevel26_eq
  noNoncuspidalFrey := ribetExistenceFromQExpansion
  ofFourCusps := fun _hPts _hCusps =>
    ribetExistenceFromQExpansion.certified
  ofBealFreyLowering := fun _cex {_ℓ _N _p} _hLower _hΔ =>
    displayedFreyWitness26_exists

theorem NoFreyPoint26.of_qExpansion_replaces_premise :
    NoFreyPoint26.of_qExpansion.displayedTargetLevel = 26 ∧
      NoFreyPoint26.of_qExpansion.noNoncuspidalFrey :=
  ⟨NoFreyPoint26.of_qExpansion.displayedTargetLevel_eq_26,
    ribetExistenceFromQExpansion.certified⟩

/-- The Mazur existence half, discharged by the displayed target
`26` rather than by a realizing newform. -/
theorem NoFreyPoint26.of_qExpansion_of_beal_frey_lowering
    (cex : BealCounterexample26) {ℓ N p : Nat}
    (hLower : LevelLowering_26 ℓ N p 26)
    (hΔ : (freyCurve (cex.A : Int) (cex.B : Int) cex.x cex.y).Δ ≠ 0) :
    ExistsNoncuspidalLevel26FreyPoint :=
  NoFreyPoint26.of_qExpansion.ofBealFreyLowering cex hLower hΔ

#print axioms displayedTargetLevel26_eq
#print axioms ribetExistenceFromQExpansion.certified
#print axioms NoFreyPoint26.of_qExpansion_replaces_premise
#print axioms NoFreyPoint26.of_qExpansion_of_beal_frey_lowering

end BealLevel26Foundations.Ribet.NoFreyPointActual26
