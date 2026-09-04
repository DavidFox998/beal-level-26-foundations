import BealLevel26Foundations.Mazur.EndgameScaffold

namespace Beal.Foundations.EndgameScaffold

/-!
# v4.0.0 Foundations entry for the Mazur endgame scaffold

Re-exports `BealLevel26Foundations.Mazur.EndgameScaffold`.
`BealTheoremFromMazurChain26` is conditional on the four named
structures plus v2 Frey and v3 `LevelLowering_26`.  It is not an
unconditional `BealTheorem`.
-/

export BealLevel26Foundations.Mazur.EndgameScaffold
  (J0_26_Q_RankZero26 FormalImmersionAtTwo26
    X0_26_RationalPoints26 NoFreyPoint26
    BealTheorem BealTheoremFromMazurChain26)

end Beal.Foundations.EndgameScaffold
