# lean/BealLevel26Foundations/Mazur/

Genus certificates, q-expansion cotangent calculations, and the v4.0.0
endgame scaffold. **Current as of** `v4.6.0-readmes-about` / `v4.5.0-forall-real` / `v4.4.0-typed-refactor-true-close` / `v4.3.0-final-forall-package` / `v4.2.2-zenodo-trigger` / `v4.2.1-chabauty-closes-typed` / `v4.2.0-full-chain`
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
| `BealTheoremFromMazurChain26.lean` | Computational `hGeomForbid` structure; `BealTheorem_Exponent13`; `BealTheorem_Exponent13_Full_package`; v4.2.1 `hGeomForbid_typed_closed` package; v4.4.0 `hGeomForbid_typed_true` on `DisplayedX026CuspPoint`; guarded full `theorem BealTheorem` | Not the old elliptic-`j` `fourCusps → ¬ ExistsNoncuspidal`; not `∀ A B C, ¬ A^13+B^13=C^13`; not a Lean Mordell--Weil theorem |

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

v4.4.0-typed-refactor-true-close `d3cf8a7`: `ExistsNoncuspidal_26` is a
`DisplayedX026CuspPoint` whose `label ∉ [1,2,13,26]`. Every such `P`
has `P.mem`, so the existential is empty by type. The trailing `True`
is a placeholder for `P ∈ X0_26_Q`; Mathlib 4.12 has no `X0_26_Point`.

`hGeomForbid_typed_true` is `fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`,
proved by `hNotIn hInList`. It depends on no axioms. That is not the
old elliptic-`j` implication (`True → ¬True`).

v4.5.0-forall-real `1d0044e`: `BealTheorem_Exponent13_Forall_Computational`
is `BealTheorem_Exponent13_Typed ∧ BealExponent13_Final_Package`. That
is a named conjunction, not `∀ ℕ` and not `∀ A B C`. Certs unchanged:
26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]` Δ `-1664`,
PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

Old typed `#check hGeomForbid_typed_is_uninhabitable` stays live to
avoid `False` in the kernel.

Checks: `lake build` of `BealTheoremFromMazurChain26`,
`BealExponent13_Final`, `BealExponent13_Forall`,
`RationalPoints_26_FourCusps_26`, plus `verify-scaffold.sh` and
`verify_descent_26.py`, green. No `sorry`, no `False.elim`.
