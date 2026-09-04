# lean/Beal/

Parent-facing `Beal.Foundations` namespace. **Current as of**
`v4.0.2-selmer`.

[`Foundations.lean`](Foundations.lean) is the entrypoint. Its `release`
string is still `"v1.4.0"`: that is the **certificate-bridge / ledger**
version, not the latest Foundations git tag. The ledger SHA is
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`.

See [`Foundations/`](Foundations/README.md) for the individual modules
(J₀(26) Weierstrass bridge, FormalImmersionM3, typed `LevelLowering_26`,
Mazur endgame re-export). Jacobian skeleton and the S-unit audit live
under
[`../BealLevel26Foundations/Jacobian/`](../BealLevel26Foundations/Jacobian/README.md)
and are imported from `Foundations.lean`.

This directory does not replace
[`DavidFox998/beal-conjecture`](https://github.com/DavidFox998/beal-conjecture)
and does not change the status of `Beal.Final.ConditionalBealTheorem`.
