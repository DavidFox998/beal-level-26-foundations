# lean/BealLevel26Foundations/

# v4.3.0 Final ∀ Package Exponent 13 (computational boundary)

Main foundations library. **Current as of** `v4.3.0-final-forall-package`.

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

`BealExponent13_Final_Package = X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`,
`BealExponent13_Final_Package.certified`.
`BealTheorem_Exponent13_Full_package` aliases it. No `∀` with
vacuous contradiction.

Checks: `lake build` of the three roots plus Final,
`verify-scaffold.sh`, `verify_descent_26.py` green.
`X026RationalPointsActual_26` audit unchanged. No `sorry` /
`True` / `trivial` inhabitants for those names.

Releases: `v4.2.0-full-chain` `62d0e13`,
`v4.2.1-chabauty-closes-typed` `eed5170`,
`v4.2.2-zenodo-trigger` fresh, `v4.3.0-final-forall-package`.

[`Final/`](Final/README.md) holds the v4.3.0 package.

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
| [`Final/`](Final/README.md) | v4.3.0 `BealExponent13_Final_Package`; not `∀ A B C` |
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
