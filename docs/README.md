# v4.5.0 ∀ Real (computational package)

Versioned release notes for
[beal-level-26-foundations](https://github.com/DavidFox998/beal-level-26-foundations).

**Current as of** tag `v4.5.0-forall-real` (prior
`v4.4.0-typed-refactor-true-close`,
`v4.3.0-final-forall-package`,
`v4.2.2-zenodo-trigger`, `v4.2.1-chabauty-closes-typed`,
`v4.2.0-full-chain`; GitHub release;
version DOI recorded after DataCite `state: findable`).

Certified: 26a1 `[1,0,1,-5,-8]` Δ `-17576` conductor 26 torsion 3;
26b1 `[1,-1,1,-3,3]` Δ `-1664` conductor 26 torsion 7.

PARI 2.17.2: `ellrank [0,0]`, empty `ell2cover`, `|Sel₂|=1` twice
(`1=1`), JSON Sha[2] computational, SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

Chabauty: `certifiedM3_det_nonzero` det=`2` over `ZMod 3`,
`X0_26_Q_four = rankZero_unconditional ∧ Chabauty0ForcesCusp_computational`.

`fourCuspsList` `[1,2,13,26]` = audit,
`fourCuspsList_complete_computational` is
`∀ P : DisplayedX026CuspPoint, P.label ∈ fourCuspsList`,
`fourCuspsForallCuspPoints`.

`hGeomForbid_typed_closed = X0_26_Q_four ∧ fourCuspsForallCuspPoints`.
Typed `fourCusps → ¬ ExistsNoncuspidal` still uninhabitable as
`True → ¬True` (no vacuous contradiction in the kernel).

`FreyLevel26 = 2*13=26` (`rfl`), displayed level only. Mathlib 4.12
has no modularity / Ribet.

`hGeomForbid_typed_true` is
`fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26` on the
displayed cusp-label type (`P.mem`), without `False.elim`.
The old elliptic-`j` implication stays uninhabitable.

`BealTheorem_Exponent13_Typed` is that implication plus
`FreyLevel26`.
`BealTheorem_Exponent13_Forall_Computational` is
`BealTheorem_Exponent13_Typed ∧ BealExponent13_Final_Package`
(not `∀ A B C`).
`BealExponent13_Final_Package = X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`,
`BealExponent13_Final_Package.certified`.
`BealTheorem_Exponent13_Full_package` is the same conjunction
in Mazur (no Final import). No `∀` with vacuous contradiction.

Checks: `lake build` of the three roots plus Final,
`verify-scaffold.sh`, `verify_descent_26.py` green.
`X026RationalPointsActual_26` audit unchanged. No `sorry` /
`True` / `trivial` inhabitants for those names.

Releases: `v4.2.0-full-chain` `62d0e13`,
`v4.2.1-chabauty-closes-typed` `eed5170`,
`v4.2.2-zenodo-trigger` fresh, `v4.3.0-final-forall-package`,
`v4.4.0-typed-refactor-true-close`, `v4.5.0-forall-real`.

Prior tag
[`v4.1.3-beal-13-theorem`](releases/v4.1.3-beal-13-theorem.md).
Prior tag
[`v4.1.2-beal-13-endgame`](releases/v4.1.2-beal-13-endgame.md).
Prior tag
[`v4.1.1-descent-compute`](releases/v4.1.1-descent-compute.md).
Prior tag
[`v4.1.0-descent-start`](releases/v4.1.0-descent-start.md).
Prior tag
[`v4.0.15-lmfdb-certs-no-doi`](releases/v4.0.15-lmfdb-certs-no-doi.md).
Prior tag
[`v4.0.14-coleman-integral-no-doi`](releases/v4.0.14-coleman-integral-no-doi.md).
Prior tag
[`v4.0.13-formal-immersion-proof-no-doi`](releases/v4.0.13-formal-immersion-proof-no-doi.md).
Prior tag
[`v4.0.12-scheme-stub-no-doi`](releases/v4.0.12-scheme-stub-no-doi.md).
Prior tag
[`v4.0.11-residue-disks-no-doi`](releases/v4.0.11-residue-disks-no-doi.md).
Prior tag
[`v4.0.10-chabauty0-no-doi`](releases/v4.0.10-chabauty0-no-doi.md).
Prior published tag
[`v4.0.9-fourCusps-forall`](releases/v4.0.9-fourCusps-forall.md)
(commit `2281aad`, version DOI
[10.5281/zenodo.22322627](https://doi.org/10.5281/zenodo.22322627)).
Prior published tag
[`v4.0.8-geom-forbid`](releases/v4.0.8-geom-forbid.md) (commit `916f696`,
version DOI
[10.5281/zenodo.22314435](https://doi.org/10.5281/zenodo.22314435)).
Prior published tag
[`v4.0.7-hIdentify-j`](releases/v4.0.7-hIdentify-j.md) (commit `ade01a2`,
version DOI
[10.5281/zenodo.22314212](https://doi.org/10.5281/zenodo.22314212)).
Prior published tag
[`v4.0.7-hIdentify`](releases/v4.0.7-hIdentify.md) (commit `a4143fc`,
version DOI
[10.5281/zenodo.22314092](https://doi.org/10.5281/zenodo.22314092)).
Prior tags
[`v4.0.6-rank-zero-fixed`](releases/v4.0.6-rank-zero-fixed.md)
(commit `2290809`, version DOI
[10.5281/zenodo.22313955](https://doi.org/10.5281/zenodo.22313955)),
[`v4.0.5-nofrey-point`](releases/v4.0.5-nofrey-point.md)
(commit `5b29092`, version DOI
[10.5281/zenodo.22313407](https://doi.org/10.5281/zenodo.22313407)),
[`v4.0.4-x026-rational-points`](releases/v4.0.4-x026-rational-points.md)
(commit `4619a5d`, version DOI
[10.5281/zenodo.22313318](https://doi.org/10.5281/zenodo.22313318)) and
[`v4.0.3-formal-immersion`](releases/v4.0.3-formal-immersion.md)
(commit `75c533d`, version DOI
[10.5281/zenodo.22313241](https://doi.org/10.5281/zenodo.22313241)).

This folder is the release-note archive. It is not a second theorem
statement. The Lean sources and the v1.4.0 ledger remain the evidence;
these notes only record what each tag claimed.

| Path | Contents |
|---|---|
| [`releases/`](releases/README.md) | One note per tagged Foundations release, from `v1.0.0-computable` through `v4.2.1-chabauty-closes-typed` |

The staged plan and open acceptance gates live in [`../PLAN.md`](../PLAN.md).
The public DOI trail is in [`../README.md`](../README.md).
