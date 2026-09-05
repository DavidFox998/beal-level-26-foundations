# lean/BealLevel26Foundations/Jacobian/

Finite Jacobian *skeleton*, S-unit audit, and formal-immersion input.
**Current as of** `v4.1.2-beal-13-endgame`
(includes `v4.1.1-descent-compute`, `v4.1.0-descent-start`, `v4.0.15-lmfdb-certs-no-doi`, `v4.0.14-coleman-integral-no-doi`, `v4.0.13-formal-immersion-proof-no-doi`, `v4.0.12-scheme-stub-no-doi`, `v4.0.11-residue-disks-no-doi`, `v4.0.10-chabauty0-no-doi`, `v4.0.9-fourCusps-forall`, `v4.0.8-geom-forbid`, `v4.0.7-hIdentify-j`, `v4.0.7-hIdentify`, `v4.0.6-rank-zero-fixed`, `v4.0.5-nofrey-point`,
`v4.0.4-x026-rational-points`, `v4.0.3-formal-immersion`).

Mathlib 4.12 has no modular-curve Jacobian, Picard scheme, Abel--Jacobi
map, Galois cohomology, or Mordell--Weil group. Nothing in this folder
constructs those objects.

Sources are the already-promoted Lean data from

* [`sagemath/level_26_ledger.json`](../../../sagemath/level_26_ledger.json)
  v1.4.0 SHA-256
  `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`;
* [`sagemath/certs/j0_26_decomposition.json`](../../../sagemath/certs/j0_26_decomposition.json);
* [`sagemath/certs/formal_immersion_M3.json`](../../../sagemath/certs/formal_immersion_M3.json).

No new certificate is added here.

| File | What it proves | What it is not |
|---|---|---|
| `J0_26_DecompActual.lean` | Finite model `s₁=q₁+q₂`, `s₂=-q₁q₂`; certified `26a × 26b` via q-expansion `a₂=-1` versus `1`; `M₃=[[1,1],[0,2]]`, `det=2` by `decide` | Not a scheme-theoretic `J₀(26)` isogeny |
| `PicardAbelJacobiIdentification_26.lean` | Standalone `Prop`: supplied matrix `= qExpansionM3` | Does not discharge the geometric Picard map |
| `TwoSelmer_vs_SUnits_26.lean` | Eight S-unit indices retained; audit is not a singleton; finite `MwrankCertificateSoundness_26` for Sage `certified_mwrank = 0` on `26a` and `26b` | Not genuine cohomological 2-Selmer; comparison remains future |
| `FormalImmersionActual_26.lean` | `M₃` injective (`det = 2 ≠ 0`); `FormalImmersionAtTwo26.of_qExpansion` inhabits the Mazur input premise; `formalImmersion_at_2_surjective_from_M3` is `det ≠ 0` | Not a scheme-theoretic formal immersion; not completed-local-ring surjectivity |
| `J0_26_Q_RankZeroActual_26.lean` | Product of certified `26a × 26b` with Sage `certified_mwrank = 0` on both; inhabits `J0_26_Q_RankZero26.of_qExpansion`; v4.1.1-descent-compute links Selmer names (`1 = 1`) as a comment only | Not a Mathlib Mordell--Weil theorem; not genuine `Sel₂`; Selmer names do not replace `rankZero` |
| `ResidueDisks_26.lean` | `M₃` input and `det ≠ 0`; rank-zero plus that input | Not a residue-disk theorem |
| `ResidueDisksProof_26.lean` | Alias `diskEqualityFromImmersion` of `formalImmersion_at_2_surjective_from_M3` | Not a residue-disk theorem |
| `ColemanIntegral_26.lean` | `ColemanVanishesOnRankZero` is the product rank-zero package | Not a Coleman integral |
| `ColemanNonVanishing_26.lean` | `Chabauty0ForcesCusp` is rank-zero product ∧ `det ≠ 0` | Not a Chabauty--Coleman theorem |
| `MordellWeilSieve_26.lean` | Finite conjunction `chabauty0Package ∧ ResidueDiskAt2ContainsOnlyCusp` | Not a scheme-theoretic `X₀(26)(ℚ)` theorem |
| `J0_26_Scheme_26.lean` | Premise-bearing Jacobian-as-scheme boundary; displayed dimension 2 | Not a Mathlib Jacobian; not inhabited |
| `AbelJacobi_26.lean` | Premise-bearing Abel--Jacobi data | Not a map `X₀(26) → J₀(26)` |

The displayed four-cusp package that can replace
`X0_26_RationalPoints26` lives in
[`../Mazur/X026RationalPointsActual_26.lean`](../Mazur/X026RationalPointsActual_26.lean).
It is not a Mathlib `X₀(26)(ℚ)` theorem.

The v1.0 README boundary still holds: the finite audit is not
mislabeled as a genuine 2-Selmer calculation.
