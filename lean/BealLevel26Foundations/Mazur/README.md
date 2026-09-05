# lean/BealLevel26Foundations/Mazur/

Genus certificates, q-expansion cotangent calculations, and the v4.0.0
endgame scaffold. **Current as of** `v4.2.1-chabauty-closes-typed` / `v4.2.0-full-chain`
(includes `v4.1.3-beal-13-theorem`, `v4.1.2-beal-13-endgame`, `v4.1.1-descent-compute`, `v4.1.0-descent-start`, `v4.0.15-lmfdb-certs-no-doi`, `v4.0.14-coleman-integral-no-doi`, `v4.0.13-formal-immersion-proof-no-doi`, `v4.0.12-scheme-stub-no-doi`, `v4.0.11-residue-disks-no-doi`, `v4.0.10-chabauty0-no-doi`, `v4.0.9-fourCusps-forall`, `v4.0.8-geom-forbid`, `v4.0.7-hIdentify-j`, `v4.0.7-hIdentify`, `v4.0.6-rank-zero-fixed`, `v4.0.5-nofrey-point`,
`v4.0.4-x026-rational-points`).

| File | What it is | What it is not |
|---|---|---|
| `Genus_26_Scaffold.lean` | Premise-bearing genus/Riemann--Hurwitz data | Not a modular-curve RH theorem |
| `Genus_26_Real.lean` | Arithmetic genus index, cusp count `4`, `ν₂=2`, `ν₃=0` by `decide` | Not an identification of `X₀(26)(ℚ)` |
| `QExpansionCotangent_Scaffold_26.lean` | Premise-bearing cotangent comparison | Not a Picard map |
| `QExpansionCotangent_Real_26.lean` | Coefficient matrix and `M₃` from the ledger | Does not define `PicardAbelJacobiIdentification_26` (that lives in [`../Jacobian/`](../Jacobian/README.md)) |
| `EndgameScaffold.lean` | Four typed premises plus `BealTheoremFromMazurChain26`; Frey `j` as `ellipticJ`; `fourCuspsForallCuspPoints`; v4.1.2 computational `Option` `hGeomForbid` from PARI `|Sel₂|=1` plus `det ≠ 0` | Not an unconditional `BealTheorem`; not typed `fourCusps → ¬ ExistsNoncuspidal`; not a Lean Mordell--Weil theorem |
| `X026RationalPointsActual_26.lean` | Displayed four cusps `[1,2,13,26]`; last conjunct `fourCuspsForallCuspPoints`; `X0_26_RationalPoints26.of_qExpansion` inhabits the Mazur premise | Not a Mathlib `X₀(26)(ℚ)` theorem |
| `HGeomForbidActual_26.lean` | Constructor inequality `ellipticJ ≠ cuspDivisor`; cusp-point forall; `hGeomForbid_typed_is_uninhabitable` | Not `fourCusps → ¬ ExistsNoncuspidal`; not `BealTheorem` |
| `Chabauty0Actual_26.lean` | Finite rank-zero + `M₃` + cusp-point forall + eight S-units | Not Chabauty--Coleman; not typed `hGeomForbid`; not `BealTheorem` |
| `X026RationalPointsScheme_26.lean` | Second Mazur-premise inhabitant from the finite sieve conjunction | Not a scheme-theoretic `X₀(26)(ℚ)` theorem |
| `BealTheoremFromMazurChain26.lean` | Computational `hGeomForbid` structure; `BealTheorem_Exponent13`; `BealTheorem_Exponent13_Full_package`; v4.2.1 `hGeomForbid_typed_closed` package; guarded full `theorem BealTheorem` | Not typed `fourCusps → ¬ ExistsNoncuspidal`; not `∀ A B C, ¬ A^13+B^13=C^13`; not a Lean Mordell--Weil theorem |

The four premises of the scaffold:

1. `J0_26_Q_RankZero26` (v4.0.6 inhabits the product of two Sage-certified rank-zero factors in [`../Jacobian/J0_26_Q_RankZeroActual_26.lean`](../Jacobian/J0_26_Q_RankZeroActual_26.lean); not a Mathlib MW theorem; do not inhabit as `True`/`trivial`)
2. `FormalImmersionAtTwo26` (v4.0.3 inhabits the input by q-expansion injectivity; not a scheme-theoretic immersion)
3. `X0_26_RationalPoints26` (v4.0.4 inhabits the finite four-cusp package; not a modular-curve rational-point theorem)
4. `NoFreyPoint26` (v4.0.7-j inhabits the four-cusp *list* in [`../Ribet/NoFreyPointActual_26.lean`](../Ribet/NoFreyPointActual_26.lean), not `¬` elliptic-`j` `ExistsNoncuspidal`; Ribet existence is [`../Ribet/RibetLoweringActual_26.lean`](../Ribet/RibetLoweringActual_26.lean))

`EndgameScaffold` re-encodes a noncuspidal displayed point as
`ellipticJ (c₄³, Δ)`, not as `26 ∉ [1, 2, 13, 26]`. v4.0.7-j
inhabits typed `hIdentify` from that packing
([`../Ribet/HIdentifyActual_26.lean`](../Ribet/HIdentifyActual_26.lean)).
v4.0.8 records typed `hGeomForbid` (`fourCusps → ¬ ExistsNoncuspidal`)
as uninhabitable
([`HGeomForbidActual_26.lean`](HGeomForbidActual_26.lean)):
constructor inequality inhabits `ExistsNoncuspidal` rather than
negating it. v4.0.9 adds `fourCuspsForallCuspPoints` over
cusp-labeled points; that forall does not range over `ellipticJ`.
v4.0.10 adds [`Chabauty0Actual_26.lean`](Chabauty0Actual_26.lean)
as that finite package; it coexists with `ExistsNoncuspidal`.
v4.1.2 records a computational `Option` `hGeomForbid` from
PARI `|Sel₂|=1` plus `det M₃ ≠ 0`; that is not the typed
implication. v4.1.3 inhabits a computational `hGeomForbid`
structure and `BealTheorem_Exponent13`; the full
`theorem BealTheorem` stays guarded. v4.2.0 names
`BealTheorem_Exponent13_Full_package` as
`X0_26_Q_four ∧ FreyLevel26`. v4.2.1 names
`hGeomForbid_typed_closed` as that Chabauty package plus the
cusp-point forall; typed `fourCusps → ¬ ExistsNoncuspidal` stays
uninhabitable. There is no unconditional `BealTheorem`. Rank,
scheme-theoretic immersion, a Mathlib `X₀(26)(ℚ)` theorem,
Mathlib Ribet existence, and `R = T` are not discharged by
`decide`.
