# lean/BealLevel26Foundations/

# v4.7.0 Iter typed no axioms

Main foundations library. **Current as of** `v4.7.0-iter-typed-no-axioms-closing`.

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
`BealExponent13_Iter_Typed_And_Package` is
`BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`
(not `∀ A B C`).
`BealExponent13_Iter_Package = X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`,
`BealExponent13_Iter_Package.certified`.
`BealTheorem_Exponent13_Full_package` is the same conjunction
in Mazur (no import of this folder). No `∀` with vacuous contradiction.

v4.4.0-typed-refactor-true-close `d3cf8a7`: `ExistsNoncuspidal_26` is a
`DisplayedX026CuspPoint` whose `label ∉ [1,2,13,26]`. Every such `P`
has `P.mem`, so the existential is empty by type. The trailing `True`
is a placeholder for `P ∈ X0_26_Q`; Mathlib 4.12 has no `X0_26_Point`.

`hGeomForbid_typed_true` is `fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`,
proved by `hNotIn hInList`. It depends on no axioms. That is not the
old elliptic-`j` implication (`True → ¬True`).

v4.5.0-forall-real `1d0044e`: `BealExponent13_Iter_Typed_And_Package`
is `BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`. That
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

Releases: `v4.2.0-full-chain` `62d0e13`,
`v4.2.1-chabauty-closes-typed` `eed5170`,
`v4.2.2-zenodo-trigger` fresh, `v4.3.0-final-forall-package`,
`v4.4.0-typed-refactor-true-close` `d3cf8a7`, `v4.5.0-forall-real`
`1d0044e`, `v4.6.0-readmes-about`,
`v4.7.0-iter-typed-no-axioms-closing`.

[`Final/`](Final/README.md) holds the v4.7.0 Iter package.

Top-level computable files:

| File | Role |
|---|---|
| `CoefficientLedger_26.lean` | 101-coefficient `26a1` / `26b1` arrays from the v1.4.0 ledger |
| `M3_Explicit.lean` | Ledger-derived `M₃ = [[1,1],[0,2]]`, `det = 2` |
| `FiniteEvidence.lean` | Eight S-units, ten quartic rows, `8 × 10` bad-prime audit |
| `FiniteChecks_26.lean` | Stable names for that audit; not genuine 2-Selmer |
| `AbelJacobiDifferential.lean` | Finite symmetric-square cusp chart; not a Picard map |
| `Scaffold.lean` | Named-bridge entrypoint |
| `Real.lean` | Arithmetic entrypoint |

| Directory | Current contents |
|---|---|
| [`Frey/`](Frey/README.md) | Conductor *data* and odd-prime valuation input |
| [`Jacobian/`](Jacobian/README.md) | v4.0.1 finite product + Picard `Prop`; v4.0.2 S-unit audit; v4.0.3 formal-immersion input; v4.0.6 product rank-zero package; v4.0.11 residue-disk input; v4.0.12 scheme boundary; v4.0.13 named `det ≠ 0` immersion; v4.0.14 named Coleman/Chabauty packages |
| [`Certs/`](Certs/README.md) | v4.0.15 LMFDB display; v4.1.1 `Descent_26.json` PARI 2-descent; not a Mordell--Weil theorem |
| [`Descent/`](Descent/README.md) | certified Weierstrass models; v4.1.1 displayed `|Sel₂|=1` from PARI; not a Selmer group |
| [`Blueprint/`](Blueprint/README.md) | Phase 3 track board; no `sorry` |
| [`Mazur/`](Mazur/README.md) | Genus certificates, four-premise endgame scaffold, v4.0.4 four-cusp package, v4.0.8 typed `hGeomForbid`, v4.0.9 cusp-point forall, v4.0.10 Chabauty-0 package |
| [`Chain/`](Chain/README.md) | v4.2.0 `FreyLevel26` (`2 * 13 = 26`) and `X0_26_Q_four` from PARI `|Sel₂|=1` twice plus `det M₃ = 2`; not Ribet and not `X₀(26)(ℚ)` |
| [`Final/`](Final/README.md) | v4.7.0 `BealExponent13_Iter_Package` / `BealExponent13_Iter_Typed_And_Package`; not `∀ A B C` |
| [`Real/`](Real/README.md) | Frey Weierstrass model and re-exported lowering |
| [`Ribet/`](Ribet/README.md) | Typed `LevelLowering_26`; v4.0.6 split; v4.0.7-j finite `j`-invariant `hIdentify` |

Certified models (PARI 2.17.2; Descent SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`):
`26a1` `[1,0,1,-5,-8]` Δ `-17576` conductor 26 torsion 3;
`26b1` `[1,-1,1,-3,3]` Δ `-1664` conductor 26 torsion 7;
both `ellrank [0,0]`, empty `ell2cover`, `|Sel₂|=1`.
`BealTheorem_Exponent13_Full_package` is
`X0_26_Q_four ∧ FreyLevel26`. Not `∀ A B C`.

The parent premises
`J0DecompositionSoundness_26`, geometric
`MwrankCertificateSoundness_26`, `FormalImmersionSoundness_26`,
`FreyCurveExists`, and supplier `LevelLowering_26` are **not**
discharged here.
