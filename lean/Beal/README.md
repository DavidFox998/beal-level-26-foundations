# lean/Beal/

Parent-facing `Beal.Foundations` namespace. **Current as of**
`v4.1.3-beal-13-theorem`.

[`Foundations.lean`](Foundations.lean) is the entrypoint. Its `release`
string is still `"v1.4.0"`: that is the **certificate-bridge / ledger**
version, not the latest Foundations git tag. The ledger SHA is
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`.

See [`Foundations/`](Foundations/README.md) for the individual modules
(J₀(26) Weierstrass bridge, FormalImmersionM3, typed `LevelLowering_26`,
Mazur endgame re-export). `Foundations.lean` also imports the Jacobian
skeleton and S-unit audit from
[`../BealLevel26Foundations/Jacobian/`](../BealLevel26Foundations/Jacobian/README.md)
(including v4.0.3 `FormalImmersionActual_26` and v4.0.6
`J0_26_Q_RankZeroActual_26`) and the v4.0.4
four-cusp package
[`../BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean`](../BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean)
and the v4.0.7-j finite `j`-invariant `hIdentify`, v4.0.8
typed `hGeomForbid`, v4.0.9 cusp-point forall, v4.0.10 Chabauty-0 package, v4.0.11 residue-disk input, v4.0.12 scheme boundary, v4.0.13 named `det ≠ 0` immersion, v4.0.14 named Coleman/Chabauty packages, v4.0.15 LMFDB display data, v4.1.0-descent-start certified models, v4.1.1-descent-compute displayed `|Sel₂|=1`, and v4.1.2-beal-13-endgame computational `Option` `hGeomForbid`, and v4.1.3-beal-13-theorem computational `BealTheorem_Exponent13`.

This directory does not replace
[`DavidFox998/beal-conjecture`](https://github.com/DavidFox998/beal-conjecture)
and does not change the status of `Beal.Final.ConditionalBealTheorem`.
