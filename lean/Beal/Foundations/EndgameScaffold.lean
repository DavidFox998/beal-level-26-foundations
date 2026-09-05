import BealLevel26Foundations.Mazur.EndgameScaffold

namespace Beal.Foundations.EndgameScaffold

/-!
# v4.0.0 Foundations entry for the Mazur endgame scaffold

Re-exports `BealLevel26Foundations.Mazur.EndgameScaffold`.
`BealTheoremFromMazurChain26` is conditional on the four named
structures plus v2 Frey, v3 `LevelLowering_26`, the four-cusp
negation `hGeomForbid`, and the remaining identification
`hIdentify : ExistsFreyWitness → ExistsNoncuspidal`.  It is
not an unconditional `BealTheorem`.
-/

export BealLevel26Foundations.Mazur.EndgameScaffold
  (J0_26_Q_RankZero26 FormalImmersionAtTwo26
    X0_26_RationalPoints26 NoFreyPoint26
    ExistsFreyWitness ExistsNoncuspidalLevel26FreyPoint
    BealTheorem BealTheoremFromMazurChain26)

end Beal.Foundations.EndgameScaffold
