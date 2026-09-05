[![v4.0.9-fourCusps-forall DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22322627.svg)](https://doi.org/10.5281/zenodo.22322627)
[![Concept DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22272382.svg)](https://doi.org/10.5281/zenodo.22272382)
[![CI](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml/badge.svg)](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml)

# Beal Level-26 Foundations

## Geometry: X₀(26) Level 26

![X0(26) Modular Curve - Genus 2 with 4 cusps and p=2 residue disks, M3=[[1,1],[0,2]] det=2, Abel-Jacobi to J0(26) rank 0](docs/images/modular_curve_x0_26_beal_level_26.webp)

*Figure: X₀(26) is genus 2 (double torus) with cusps 1,2,13,26. p=2 residue disks (blue) map via Abel-Jacobi to J₀(26), a 2-dim abelian surface rank 0. Formal immersion M₃=[[1,1],[0,2]], det=2≠0 proves each disk contains only its cusp — the Coleman integral vanishes on J₀(26)(ℚ) when rank 0.*

This repository is the foundations chamber for moving the level-26 Beal route
from an explicit conditional assembly toward a theorem whose remaining
mathematical bridges are constructed one by one. It is a deliberately smaller
repository: the conditional development stays in
[`DavidFox998/beal-conjecture`](https://github.com/DavidFox998/beal-conjecture).

The governing principle is the same as the parent project: a checked
calculation is evidence for exactly what it computes, while every missing
mathematical bridge is named instead of hidden behind an axiom.

**Current public surface:** tag
[`v4.0.13-formal-immersion-proof-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.13-formal-immersion-proof-no-doi)
(git tag only; no version DOI; prior
[`v4.0.12-scheme-stub-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.12-scheme-stub-no-doi);
prior
[`v4.0.11-residue-disks-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.11-residue-disks-no-doi);
prior
[`v4.0.10-chabauty0-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.10-chabauty0-no-doi);
prior published
[`v4.0.9-fourCusps-forall`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.9-fourCusps-forall),
commit `2281aad`, version DOI
[10.5281/zenodo.22322627](https://doi.org/10.5281/zenodo.22322627);
prior
[`v4.0.8-geom-forbid`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.8-geom-forbid),
commit `916f696`, version DOI
[10.5281/zenodo.22314435](https://doi.org/10.5281/zenodo.22314435);
prior [`v4.0.7-hIdentify-j`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.7-hIdentify-j),
commit `ade01a2`, version DOI
[10.5281/zenodo.22314212](https://doi.org/10.5281/zenodo.22314212)).
The coefficient ledger is still
[`sagemath/level_26_ledger.json`](sagemath/level_26_ledger.json) **v1.4.0**,
SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`.
There is no `axiom`, `sorry`, or `admit`. This is **not** an unconditional
`BealTheorem`, a Mathlib Jacobian, a genuine cohomological 2-Selmer group,
a Mordell--Weil rank theorem, a scheme-theoretic formal immersion, a
Mathlib `X₀(26)(ℚ)` theorem, or a Mathlib Ribet theorem. v4.0.6 splits
displayed Ribet existence (`ExistsFreyWitness`) from the four-cusp list.
v4.0.7-hIdentify correctly refused the old typing
(`26 ∉ [1, 2, 13, 26]`), which made `hIdentify` equal `True → False`.
v4.0.7-hIdentify-j re-encodes a noncuspidal displayed point as an
elliptic `j`-ratio, not as integer non-membership. Typed `hIdentify`
packs that `j`. Four cusp labels stay as cusps. v4.0.8-geom-forbid
proves typed `hGeomForbid` (`fourCusps → ¬ ExistsNoncuspidal`)
uninhabitable: `ellipticJ ≠ cuspDivisor` as a point kind is how a
Frey `j` is shown *not* to be a cusp label, so it inhabits
`ExistsNoncuspidal` rather than negating it. v4.0.9-fourCusps-forall
retypes four cusps as `fourCuspsForallCuspPoints` over those
cusp-labeled points. That forall is true and does not quantify
over `ellipticJ`. The same-type forall `fourCuspsForallAllKinds`
is false. Typed `hGeomForbid` remains uninhabitable. v4.0.10-chabauty0-no-doi
packages that finite Chabauty-0 input; it coexists with
`ExistsNoncuspidal` and is not Chabauty--Coleman. v4.0.11-residue-disks-no-doi
adds the `M₃` residue-disk *input* and the finite sieve
conjunction; those are not a scheme `X₀(26)(ℚ)` theorem. Typed `hIdentify`
stays the elliptic-`j` packing. The remaining
geometric gate is a Mathlib noncuspidal point of `X₀(26)`.

Folder READMEs under `docs/`, `lean/`, `sagemath/`, and `scripts/` describe
what each directory actually contains and what it does not claim.

## Starting point

The companion Beal v11.0.0 assembly compiles
`Beal.Final.ConditionalBealTheorem` from five explicit theorem arguments. It
is conditionally complete: this repository does not silently change the
status of that theorem.

1. `J0DecompositionSoundness_26 J0_26`;
2. `MwrankCertificateSoundness_26`;
3. `FormalImmersionSoundness_26 J0_26 cotangent`;
4. `FreyCurveExists`, reusing `FreyCurveConstruction_26`; and
5. `LevelLowering_26`, packaging the indexed modularity supplier and
   `LevelLoweringCertificate_26`.

This repository does not claim those premises are already discharged. Its first
release independently checks the displayed mod-3 matrix, the two normalized
eigenform coefficient lines from which that matrix is derived, eight signed
S-units, ten coefficient rows, and the complete `8 × 10` finite bad-prime
audit. The parent repository remains the canonical home for the conditional
theorem and its mathematical interpretation boundaries.

## Staged foundation plan

The staged plan follows four releases.

### v1.x — Unconditional computable foundations

The 101-coefficient level-26 ledger, explicit `M₃`, and complete finite checks
at 2 and 13 are reproducible, kernel-checked computations. The matrix is
derived as `basisChange * coefficientMatrix`, not entered as a differential
table. The audit retains all eight S-unit indices and is proved not to be
singleton, so it is not mislabeled as a genuine 2-Selmer calculation. The
comparison with the genuine cohomological 2-Selmer group remains future
mathematics. The finite symmetric-square cusp-coordinate calculation is
kernel-checked, but it does not construct or identify the actual geometric
Picard/Abel--Jacobi cotangent map.

This is an unconditional statement about the computations themselves. It is
not an unconditional proof of the level-26 endgame.

v1.3.0 adds SageMath 10.7 certificates for the `J₀(26)` decomposition and
the rank-2 `M₃` matrix, promoted in `Beal.Foundations`. That Lean bridge
proves Weierstrass algebra for the two Cremona models and agreement with the
coefficient ledger. v1.4.0 adds `Beal.Foundations.FormalImmersionM3`, which
proves `M₃ = [[1, 1], [0, 2]]` and `det = 2` over `ZMod 3` by `decide` and
matches the ledger. Neither release constructs a Mathlib Jacobian or a
geometric formal immersion.

### Explicit bridge scaffold

`BealLevel26Foundations.Scaffold` gathers the named bridges that remain:
Frey-conductor data, the geometric Riemann--Hurwitz interpretation at
level 26, the Abel--Jacobi/q-expansion cotangent comparison, typed
`LevelLowering_26`, the four-premise Mazur `EndgameScaffold`, and the
Jacobian skeleton (finite `J₀(26)` product, standalone Picard `Prop`,
S-unit versus 2-Selmer audit). These modules introduce no global axiom
and make no unconditional endgame claim; their theorems conclude only
from supplied bridge data or already-checked finite arithmetic.

### Real arithmetic extension

`BealLevel26Foundations.Real` goes beyond the bridge structures where Mathlib
4.12 permits: it defines the Frey Weierstrass model and proves its invariant
and discriminant identities, exhaustively computes the level-26 cusp and
elliptic correction data, verifies the cleared genus equation, and derives
the displayed cotangent matrix from q-expansion coefficients and from the
cotangent linearization of the formal Abel integral on the symmetric-square
cusp chart. v3.0.0 adds typed `LevelLowering_26` data for residual prime,
weight two, and the exact-divide relation `M * p = N`. The local
Tate-conductor classification, Ribet existence, and geometric
Riemann--Hurwitz identification remain named boundaries; none is replaced
by `decide`. v4.0.1--v4.0.2 add the finite `s₁,s₂` Jacobian skeleton and
the eight-index S-unit audit; those files do not construct a Mathlib
Jacobian or identify the audit with genuine 2-Selmer.

## DOI / Citation — versioned audit trail

| Version | Git Tag / Commit | Zenodo DOI | Audit / Notes |
| :--- | :--- | :--- | :--- |
| v1.0.0 unconditional computable foundations | `v1.0.0-computable` / `6aa613c` | [10.5281/zenodo.22272382](https://doi.org/10.5281/zenodo.22272382) (concept) | 2315/2315 passed, 0 axiom/sorry/admit, ledger 101 coeff SHA-256 audited, 160 Hensel witnesses, finite checks not called genuine Selmer |
| v1.1.0 arithmetic frey genus qexpansion matrix | `v1.1.0-arithmetic-frey-genus-qexpansion-matrix` / `c670d1c` | [10.5281/zenodo.22284436](https://doi.org/10.5281/zenodo.22284436) | 2315 isolated + 2319 real green, arithmetic Frey c4/c6/Δ via `ring` with no `frey_conductor_data`, arithmetic genus index 42 divisors `[1,2,13,26]`, cusp 4, ν2=2, ν3=0, certificate 2 via `decide`; ledger-derived `M3 = [[1,1],[0,2]]`, det=2 via `decide`; Picard bridge isolated as `PicardAbelJacobiIdentification_26` |
| v1.1.1 choice-clean representation | `v1.1.1-choice-clean-representation-dependency` / `1c2c52b` | [10.5281/zenodo.22285575](https://doi.org/10.5281/zenodo.22285575) | Full parent integration: explicit `ledgerM3` has footprint `[propext, Classical.choice, Quot.sound]`; even `fun _ _ => 0 : Matrix (Fin 2) (Fin 2) (ZMod 3)` has the same footprint in Mathlib 4.12. This is a representation dependency, not a domain axiom. Focused point checks at 2 and 13 audit to the genuinely choice-free two-item footprint `[propext, Quot.sound]`. Quartic ledgers under the `Beal17Mazur.Jacobian` namespace are fixed. The formal-immersion certificate was regenerated because its source now imports `ledgerM3` instead of duplicating a literal: source hash and checksum changed, while matrix, determinant, level, and prime did not. |
| v1.2.0 formal-coordinate matrix and valuation input | `v1.2.0-abel-jacobi-differential-closed-valuation-input` / `ed74e3b` | [10.5281/zenodo.22286222](https://doi.org/10.5281/zenodo.22286222) | A finite model in coordinates `s₁=q₁+q₂`, `s₂=-q₁q₂` derives `[[1,1],[0,2]]`; it does **not** construct or identify an actual Picard/Abel--Jacobi cotangent map. Odd-prime input proves `vₚ(c₄)=0` and `vₚ(Δ)>0` without `frey_conductor_data`. The `[propext, Classical.choice, Quot.sound]` footprint is representational. Both geometric compatibility and Tate/Kodaira conductor classification remain explicit. Archive SHA-256 `9ea2b4f7d95460315736fb9f926678d57b39af5b682b168849173ea6cbd891fa`. |
| v1.2.1 corrected formal-coordinate boundary | `v1.2.1-formal-coordinate-boundary-corrected` / `05b8159` | [10.5281/zenodo.22286630](https://doi.org/10.5281/zenodo.22286630) | Corrective immutable release: the finite model remains, but `PicardAbelJacobiIdentification_26` is premise-bearing and no theorem identifies it with an actual geometric cotangent map. Archive SHA-256 `001d43aa7d02a93ab75122c58c8bf99e9e1395957a4e6657ce32e75b53b5e9e5`. |
| v1.3.0 J0(26) decomposition and M3 certificates | `v1.3.0` / `e657d15` | [10.5281/zenodo.22310313](https://doi.org/10.5281/zenodo.22310313) | SageMath 10.7 certificates for `J₀(26)` dim 2 = `26a × 26b` and rank-2 `M₃=[[1,1],[0,2]]` over `𝐅₃`. Lean 4.12 proves Weierstrass `c₄,c₆,Δ` for the two Cremona models and ledger agreement. Not a Jacobian, Mordell--Weil, or formal-immersion theorem. Ledger SHA-256 `9671052435714618d8106b25ed3f04fd7b87d5332ebccf76f949f768276c6875`. Archive SHA-256 `b748a2bfd30037ad1c1b2aeb8cf26795b2f8ca56f57d3e3f5137cc41ab9690da`. |
| v1.4.0 FormalImmersionM3 ledger match | `v1.4.0` / `bfcd70d` | [10.5281/zenodo.22310574](https://doi.org/10.5281/zenodo.22310574) | Lean 4.12 `Beal.Foundations.FormalImmersionM3` reads `sagemath/certs/formal_immersion_M3.json` and proves `M₃=[[1,1],[0,2]]`, `det=2` over `ZMod 3` by `decide`, matching `ledgerM3`. Not a Jacobian, Mordell--Weil, or Picard theorem. Ledger SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `09bee85fea4154c0db0db0863f0655dfec5400c8f67f0cf37795dcf919767a4a`. |
| v2.0.0-frey Weierstrass model and valuation input | `v2.0.0-frey` / `517449f` | [10.5281/zenodo.22310825](https://doi.org/10.5281/zenodo.22310825) | `BealLevel26Foundations.Real.FreyWeierstrass` defines the parent integral Frey model and proves `c₄,c₆,Δ` by `ring`. `Conductor_26_Unconditional` proves `vₚ(c₄)=0` and `vₚ(Δ)>0` from `p ∤ c₄`, `p ∣ Δ`, `Δ ≠ 0`, with no `frey_conductor_data` or `tate_step2_odd_prime_external`. Tate/Kodaira classification remains an explicit boundary. Archive SHA-256 `7ef05ce1d5b9e47115a5225292cce7b0153d9c0c4018b8bdeaca5cd1886f9532`. |
| v3.0.0-ribet typed LevelLowering_26 certificate | `v3.0.0-ribet` / `febeb7a` | [10.5281/zenodo.22311107](https://doi.org/10.5281/zenodo.22311107) | `LevelLowering_26` is indexed certificate data for residual prime `ℓ`, weight 2, and the exact-divide step `M * p = N` with `vₚ(N)=1`. Proves `vₚ(26 p)=1` from `p ∤ 26` and the factorization `26 = 2 * 13`. Not a Ribet, modularity, or Galois-representation theorem. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `1be962c3bdce99d6de3a4cf171e152f69b1fc4e517f4d4cb48d54904daae3a2f`. |
| v4.0.0-mazur Mazur endgame scaffold | `v4.0.0-mazur` / `aa4e4e6` | [10.5281/zenodo.22311182](https://doi.org/10.5281/zenodo.22311182) | `EndgameScaffold` carries rank-zero, formal-immersion-at-2 input (`M₃=[[1,1],[0,2]]`, `det=2`), four-cusps, and no-Frey-point structures. `BealTheoremFromMazurChain26` concludes `BealTheorem` only from those plus v2 Frey and v3 `LevelLowering_26`. Not an unconditional Beal theorem. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `ff8b4a7a16705db0e5f98704a745eec9687d7047e9d2dfd14eae7b16a0f2b1d6`. |
| v4.0.1-jacobian-skeleton finite J0 product and Picard Prop | `v4.0.1-jacobian-skeleton` / `235a0bc` | [10.5281/zenodo.22312844](https://doi.org/10.5281/zenodo.22312844) | `Jacobian/J0_26_DecompActual` loads the v1.4.0 ledger and certs, defines `s₁=q₁+q₂`, `s₂=-q₁q₂`, and proves the certified `26a × 26b` distinction `a₂=-1` versus `1` plus `M₃=[[1,1],[0,2]]`, `det=2` by `decide`. `PicardAbelJacobiIdentification_26` is a standalone `Prop`. Not a Mathlib Jacobian. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `4a47641e072e945ce02f1b9fef273b52e63d0ff70f3bdadfdf87f5449df7d87d`. |
| v4.0.2-selmer S-unit audit versus genuine 2-Selmer | `v4.0.2-selmer` / `c2f829d` | [10.5281/zenodo.22313148](https://doi.org/10.5281/zenodo.22313148) | `Jacobian/TwoSelmer_vs_SUnits_26` audits the eight S-unit indices from the v1.4.0 decomposition cert, proves the finite audit retains all eight and is not a singleton, and therefore is not genuine cohomological 2-Selmer. `MwrankCertificateSoundness_26` packages Sage `certified_mwrank = 0` for `26a` and `26b` with the `s₁,s₂` model and `a₂ = -1` versus `1`. Not a Mathlib Jacobian or MW theorem. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `c7585189484c0cdaed1d6739dabf17b83d424efae5b44382c7085ed69fe9f6b6`. |
| v4.0.3-formal-immersion q-expansion cotangent injectivity | `v4.0.3-formal-immersion` / `75c533d` | [10.5281/zenodo.22313241](https://doi.org/10.5281/zenodo.22313241) | `Jacobian/FormalImmersionActual_26` proves `M₃` injective (`det = 2 ≠ 0`) and inhabits `FormalImmersionAtTwo26.of_qExpansion` from q-expansion data and `PicardAbelJacobiIdentification_26`. Not a scheme-theoretic formal immersion. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `8fb5e22ba5a72604b025b1a8bf8af3f5e745f4186afdf54ede49640e13148ad8`. |
| v4.0.4-x026-rational-points displayed four cusps | `v4.0.4-x026-rational-points` / `4619a5d` | [10.5281/zenodo.22313318](https://doi.org/10.5281/zenodo.22313318) | `Mazur/X026RationalPointsActual_26` inhabits `X0_26_RationalPoints26.of_qExpansion` from displayed cusps `[1,2,13,26]`, already-decided `a₂` / `MwrankCertificateSoundness_26` / `FormalImmersionAtTwo26.of_qExpansion`. Not a Mathlib `X₀(26)(ℚ)` theorem. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `d9449a352f4b1e580330a076f89256e754194433c8c00eefa5784517f14f5e04`. |
| v4.0.5-nofrey-point displayed Ribet existence | `v4.0.5-nofrey-point` / `5b29092` | [10.5281/zenodo.22313407](https://doi.org/10.5281/zenodo.22313407) | `Ribet/NoFreyPointActual_26` inhabits `NoFreyPoint26.of_qExpansion` from displayed target `26` plus the v4.0.1–v4.0.4 q-expansion chain. Not a Mathlib Ribet theorem. `J0_26_Q_RankZero26` and `hGeomForbid` stay supplied. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `02094d6dc522603fed7478500f5ee1f9c7ab3ddc0530d16262003ff866f5f942`. |
| v4.0.6-rank-zero-fixed split existence from absence | `v4.0.6-rank-zero-fixed` / `2290809` | [10.5281/zenodo.22313955](https://doi.org/10.5281/zenodo.22313955) | Splits Ribet existence (`RibetLoweringActual_26` / `ExistsFreyWitness`, `loweredLevel=26`) from four-cusp absence (`NoFreyPointActual_26` / `¬ ExistsNoncuspidal` from divisors `[1,2,13,26]`). Inhabits `J0_26_Q_RankZero26` as the product of certified `26a×26b` with Sage `certified_mwrank=0` on both; not genuine `Sel₂`. `hGeomForbid` is `fourCusps → ¬ ExistsNoncuspidal`. Remaining named gate: `hIdentify`. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `3597879ae2492dbd48ef3b8d7755bd742c14373988ff9af0469fd89060313570`. |
| v4.0.7-hIdentify typed implication uninhabitable | `v4.0.7-hIdentify` / `a4143fc` | [10.5281/zenodo.22314092](https://doi.org/10.5281/zenodo.22314092) | `Ribet/HIdentifyActual_26` proves `hIdentify_typed_is_uninhabitable`: `ExistsFreyWitness → ExistsNoncuspidal` is `True → False` because `26` is a displayed cusp. Does not inhabit that implication and does not add `theorem BealTheorem`. Remaining geometric gate: Frey curve from a Beal counterexample. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `df6ff673d4661ae736ff726f7b03f3271493483895910fb97267808bd785e41a`. |
| v4.0.7-hIdentify-j finite `j`-invariant encoding | `v4.0.7-hIdentify-j` / `ade01a2` | [10.5281/zenodo.22314212](https://doi.org/10.5281/zenodo.22314212) | Redefines `ExistsNoncuspidal` as an elliptic `j`-ratio `(c₄³ : Δ)`, not `26 ∉ [1,2,13,26]`. `HIdentify26.of_qExpansion` inhabits typed `hIdentify` from q-expansion `26a × 26b`, `MwrankCertificateSoundness_26`, and the four-cusp package. `NoFreyPoint26` keeps the cusp list and does not Lean-negate the elliptic `j`. `hGeomForbid` remains. No `theorem BealTheorem`. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `0a93c94fc19aa64ca8a57a76b1106a8991be4b29ba7ac1bc33839b81ba590e45`. |
| v4.0.8-geom-forbid typed `hGeomForbid` uninhabitable | `v4.0.8-geom-forbid` / `916f696` | [10.5281/zenodo.22314435](https://doi.org/10.5281/zenodo.22314435) | `Mazur/HGeomForbidActual_26` proves `hGeomForbid_typed_is_uninhabitable`: `fourCusps → ¬ ExistsNoncuspidal` is `True → ¬True` because constructor inequality `ellipticJ ≠ cuspDivisor` inhabits `ExistsNoncuspidal`. Finite package from formal immersion, rank-zero product, and four-cusp list. Does not inhabit that implication and does not add `theorem BealTheorem`. Remaining geometric gate: Mathlib `X₀(26)` noncuspidal point. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `0de1f3a446b09ba9602962116406a1afdab6ebf233cc8163f1b7c27a29c54931`. |
| v4.0.9-fourCusps-forall cusp-point forall | `v4.0.9-fourCusps-forall` / `2281aad` | [10.5281/zenodo.22322627](https://doi.org/10.5281/zenodo.22322627) | Retypes four cusps as `fourCuspsForallCuspPoints` over `DisplayedX026CuspPoint`. That forall is true and does not quantify over `ellipticJ`. `fourCuspsForallAllKinds_is_false` records the same-type forall is false. Typed `hGeomForbid` remains `True → ¬True`. Does not inhabit that implication and does not add `theorem BealTheorem`. Remaining geometric gate: Mathlib `X₀(26)` noncuspidal point. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `c58219380fd559d49e2d813a7c642e1708221c35d2ea9f828bf852afa07fa056`. |
| v4.0.10-chabauty0-no-doi Chabauty-0 finite package | `v4.0.10-chabauty0-no-doi` | none (git tag only) | `Mazur/Chabauty0Actual_26` packages rank-zero product, `M₃` input, `fourCuspsForallCuspPoints`, `¬ fourCuspsForallAllKinds`, and eight S-units. Not Chabauty--Coleman. Typed `hIdentify` stays the elliptic-`j` packing (not `True`/`trivial`). Audits `HGeomForbidActual_26` and `X026RationalPointsActual_26` unchanged. Typed `hGeomForbid` remains uninhabitable. No `theorem BealTheorem`. No version DOI. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.0.11-residue-disks-no-doi `M₃` residue-disk input | `v4.0.11-residue-disks-no-doi` | none (git tag only) | `ResidueDisks_26` is `M₃` plus `det ≠ 0`. `MordellWeilSieve_26` conjoins that with `chabauty0Package` under the name `X0_26_Q_EqualsFourCuspsAsScheme`; that is a finite conjunction, not a scheme `X₀(26)(ℚ)` theorem. `X026RationalPointsScheme_26` inhabits the Mazur premise from that package. The four-cusp audit is unchanged. No `theorem BealTheorem`. No version DOI. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.0.12-scheme-stub-no-doi Jacobian-as-scheme boundary | `v4.0.12-scheme-stub-no-doi` | none (git tag only) | Phase 3 Track A. `J0_26_Scheme_26` and `AbelJacobi_26` are premise-bearing named boundaries. Mathlib 4.12 has no Jacobian. Not `sorry`, not `26a × 26b`, not inhabited as `True`. `X026RationalPointsActual_26` unchanged. No `theorem BealTheorem`. No version DOI. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.0.13-formal-immersion-proof-no-doi named `det ≠ 0` immersion | `v4.0.13-formal-immersion-proof-no-doi` | none (git tag only) | Phase 3 Track B. `formalImmersion_at_2_surjective_from_M3` is `of_qExpansion.input.det ≠ 0`. `diskEqualityFromImmersion` aliases that same `det ≠ 0`. Not surjectivity of completed local rings and not a residue-disk theorem. Tracks C and D not started. No `theorem BealTheorem`. No version DOI. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |

The corrected v1.0.1 theorem uses each signed S-unit in the finite-field
equation. It supersedes v1.0.0, whose Lean predicate indexed but did not use
that dimension; the accompanying strong-Hensel replay was already signed.

### v2.0.0 — Frey discriminant foundations

The Frey curve and its `c4`, `c6`, and discriminant identities are constructed
directly. `Conductor_26_Unconditional.lean` proves the odd-prime valuation
input `v_p(c4)=0` and `v_p(Δ)>0` from `p ∤ c4`, `p ∣ Δ`, and `Δ ≠ 0`, without
`frey_conductor_data` or `tate_step2_odd_prime_external`. Mathlib 4.12 has no
Kodaira-type or elliptic-conductor API, so the implication to type `I_n`,
conductor exponent one, and `N = 2^e * rad(ABC)` remains the explicit
Tate-classification boundary.

### v3.0.0 — Ribet level lowering

`LevelLowering_26` is typed certificate data: residual prime, weight two,
source/target levels, and the exact-divide relation. The arithmetic
`v_p(26 p) = 1` from `p ∤ 26` is proved in Mathlib 4.12. Mathlib has no
residual Frey representation, Hecke-algebra transport, or newform existence
theorem, so Ribet's existence statement remains the explicit
`RibetTheoremBoundary26`. This does not replace the parent supplier.

### v4.0.0 — Mazur endgame

Formalize the remaining Mazur chain:

```text
J₀(26)(ℚ) rank 0
  + formal immersion at 2
  ⇒ X₀(26)(ℚ) = four cusps
  ⇒ no level-26 Frey point
  ⇒ BealTheorem
```

v4.0.0-mazur packages that chain as `EndgameScaffold`. The four premises
are typed structures. `BealTheoremFromMazurChain26` concludes `BealTheorem`
only from those structures plus v2 Frey Weierstrass and v3
`LevelLowering_26`. Mathlib 4.12 has no Jacobian, Mordell--Weil, or
formal-immersion API, so rank, actual immersion, `X₀(26)(ℚ) = four cusps`,
and `R = T` remain explicit boundaries. A green scaffold build is not an
unconditional `BealTheorem`.

v4.0.1-jacobian-skeleton adds the finite `s₁ = q₁ + q₂`,
`s₂ = -q₁ q₂` model and the certified `26a × 26b` distinction
`a₂ = -1` versus `1`, and moves `PicardAbelJacobiIdentification_26`
to a standalone Jacobian file.

v4.0.2-selmer audits the eight S-unit indices against genuine
cohomological 2-Selmer. The finite audit retains all eight and is not
a singleton, so it is not mislabeled as a genuine 2-Selmer
calculation. `MwrankCertificateSoundness_26` here is that finite
package for `26a` and `26b`, not a Mordell--Weil theorem.

v4.0.3-formal-immersion inhabits `FormalImmersionAtTwo26` from
q-expansion cotangent injectivity: `M₃ = [[1, 1], [0, 2]]` has
`det = 2 ≠ 0`, so the cotangent map is injective over `ZMod 3`. That
can replace the formal-immersion *input* premise. It is not a
scheme-theoretic immersion.

v4.0.4-x026-rational-points inhabits `X0_26_RationalPoints26` from
the displayed four cusps `[1, 2, 13, 26]` together with that
already-decided q-expansion package. `ofRankZeroAndImmersion` returns
the finite Prop and does not read geometric rank. It is not a Mathlib
`X₀(26)(ℚ)` theorem.

v4.0.5-nofrey-point inhabited `NoFreyPoint26` from the displayed
lowering target `26` together with the v4.0.1 (`235a0bc`) → v4.0.2
(`c2f829d` / [10.5281/zenodo.22313148](https://doi.org/10.5281/zenodo.22313148))
→ v4.0.3 (`75c533d` / [10.5281/zenodo.22313241](https://doi.org/10.5281/zenodo.22313241))
→ v4.0.4 (`4619a5d` / [10.5281/zenodo.22313318](https://doi.org/10.5281/zenodo.22313318))
q-expansion chain. That made `hGeomForbid` the uninhabitable
`True → True → False`.

v4.0.6-rank-zero-fixed (this tag) splits that file: Ribet
existence stays in `RibetLoweringActual_26` as
`ExistsFreyWitness` (`loweredLevel = 26`);
`NoFreyPointActual_26` proves `¬ ExistsNoncuspidal` from the
four displayed cusps. `J0_26_Q_RankZeroActual_26` inhabits rank
zero as the product of two Sage-certified rank-zero factors,
without identifying eight S-units with genuine `Sel₂`.
`hGeomForbid` is now `fourCusps → ¬ ExistsNoncuspidal`.
`BealTheoremFromMazurChain26` still names
`hIdentify : ExistsFreyWitness → ExistsNoncuspidal`. v4.0.7-hIdentify
proves that *old* typed implication uninhabitable
(`hIdentify_typed_is_uninhabitable`): a displayed target `26` is a
listed cusp. v4.0.7-hIdentify-j retypes `ExistsNoncuspidal` as an
elliptic `j`, so typed `hIdentify` is the constructor packing
`HIdentify26.of_qExpansion`. Four cusp labels stay as cusps.
`hGeomForbid` (`fourCusps → ¬ ExistsNoncuspidal`) remains the
named geometric gate: that implication would put `False` in the
kernel if inhabited together with the new `hIdentify`.
v4.0.8-geom-forbid records that fact as
`hGeomForbid_typed_is_uninhabitable`. v4.0.9-fourCusps-forall
retypes four cusps as `fourCuspsForallCuspPoints` over
cusp-labeled points. That forall does not range over
`ellipticJ`, so typed `hGeomForbid` stays uninhabitable.
v4.0.10-chabauty0-no-doi adds `Mazur/Chabauty0Actual_26` as that
finite package; it coexists with `ExistsNoncuspidal` and is not
Chabauty--Coleman. v4.0.11-residue-disks-no-doi adds the `M₃`
residue-disk *input* and finite sieve conjunction; those are not
a scheme-theoretic `X₀(26)(ℚ)` theorem. v4.0.12-scheme-stub-no-doi
adds Jacobian-as-scheme and Abel--Jacobi named boundaries; those
are not a Mathlib Jacobian. v4.0.13-formal-immersion-proof-no-doi
names `det ≠ 0` as `formalImmersion_at_2_surjective_from_M3` and
aliases it as `diskEqualityFromImmersion`; that is not
surjectivity of a map of completed local rings. There is no
unconditional `BealTheorem`.

The detailed milestones, acceptance gates, and dependency order are in
[`PLAN.md`](PLAN.md).

## Repository layout

```text
.
├── README.md                    # this file: status, DOI trail, how to build
├── PLAN.md                      # v1–v4 unconditionalization plan and open gates
├── CITATION.cff                 # v1.0.1-computable citation record
├── .github/workflows/main.yml   # lake + verify-scaffold on github.com main
├── DOCKERFILE                   # Elan + Lean 4.12.0 + Mathlib verification image
├── docs/                        # versioned release notes (see docs/README.md)
│   └── releases/
├── lean/                        # Lean 4.12 sources (see lean/README.md)
│   ├── Beal/                    # Beal.Foundations certificate re-exports
│   └── BealLevel26Foundations/  # computable, scaffold, and real modules
│       ├── Frey/
│       ├── Jacobian/            # v4.0.1–v4.0.3 skeleton, Selmer audit, immersion input, v4.0.6 rank-zero product, v4.0.11 residue-disk input, v4.0.12 scheme boundary, v4.0.13 named det≠0 immersion
│       ├── Mazur/               # genus arithmetic, endgame scaffold, v4.0.4 four-cusp package, v4.0.8 typed hGeomForbid, v4.0.9 cusp-point forall, v4.0.10 Chabauty0 package
│       ├── Real/
│       └── Ribet/               # typed lowering; v4.0.6 split; v4.0.7-j finite j-invariant hIdentify
├── sagemath/                    # v1.4.0 ledger + SageMath 10.7 certs
│   └── certs/                   # j0_26_decomposition.json, formal_immersion_M3.json
├── scripts/                     # ledger, cert, Hensel, and scaffold checks
├── lakefile.lean                # three lake targets
└── lean-toolchain               # pinned leanprover/lean4:v4.12.0
```

Each of those directories has a `README.md` stating current contents and
the interpretation boundary. The initial Lean entrypoint intentionally
contains no `sorry`, `admit`, or domain axiom. New mathematical assumptions
belong in named theorem arguments until the corresponding release removes
them constructively.

## Verification

The workflow runs on pushes and pull requests:

```sh
lake exe cache get
lake build BealLevel26Foundations
lake build BealLevel26FoundationsScaffold
lake build BealLevel26FoundationsReal
bash scripts/verify-scaffold.sh
```

The corrected v1.0.1-computable release uses Lean 4.12.0 to match the parent Beal project. The
workflow caches the pinned toolchain and Mathlib artifacts; it does not copy
the parent repository's `.lake` directory or silently import its theorem
boundaries.

A containerized replay of the same three Lake targets is in `DOCKERFILE`.
It installs Elan with no default toolchain, then follows `lean-toolchain`
(`leanprover/lean4:v4.12.0`) and Mathlib `v4.12.0`. Build with:

```sh
docker build -f DOCKERFILE -t beal-level-26-foundations .
docker run --rm beal-level-26-foundations
```

## Relationship to `beal-conjecture`

The repositories are companion works with different purposes:

- `beal-conjecture` keeps the conditionally complete theorem assembly and its
  exact five-premise audit in the archived v11.0.0 companion release
  ([DOI 10.5281/zenodo.22281075](https://doi.org/10.5281/zenodo.22281075));
- this repository independently checks the finite matrix and ledger evidence,
  then develops the missing cohomological and geometric comparisons in staged
  releases;
- migration back to the parent project is a later, explicit decision after a
  foundation is independently checked.

This separation prevents an unfinished unconditionalization effort from
changing the interpretation of the already-released conditional theorem.
Foundations v1 is unconditional computable foundations, archived separately
as a Zenodo companion. It does not claim that `decide` proves a genuine Selmer
singleton, and it does not claim an unconditional proof of the endgame.

## Citation

For the v4.0.9 cusp-point forall record, cite version DOI
[`10.5281/zenodo.22322627`](https://doi.org/10.5281/zenodo.22322627).
For the v4.0.8 typed-`hGeomForbid` record, cite version DOI
[`10.5281/zenodo.22314435`](https://doi.org/10.5281/zenodo.22314435).
For the v4.0.7-j finite `j`-invariant encoding, cite version DOI
[`10.5281/zenodo.22314212`](https://doi.org/10.5281/zenodo.22314212).
For the v4.0.7 typed-`hIdentify` record, cite version DOI
[`10.5281/zenodo.22314092`](https://doi.org/10.5281/zenodo.22314092).
For the v4.0.6 existence/absence split and product rank-zero
package, cite version DOI
[`10.5281/zenodo.22313955`](https://doi.org/10.5281/zenodo.22313955).
For the displayed Ribet-existence package,
cite version DOI
[`10.5281/zenodo.22313407`](https://doi.org/10.5281/zenodo.22313407).
For the displayed four-cusp package,
cite version DOI
[`10.5281/zenodo.22313318`](https://doi.org/10.5281/zenodo.22313318).
For q-expansion formal-immersion input,
cite version DOI
[`10.5281/zenodo.22313241`](https://doi.org/10.5281/zenodo.22313241).
For the S-unit audit versus genuine 2-Selmer,
cite version DOI
[`10.5281/zenodo.22313148`](https://doi.org/10.5281/zenodo.22313148).
For the Jacobian skeleton,
cite version DOI
[`10.5281/zenodo.22312844`](https://doi.org/10.5281/zenodo.22312844).
For the Mazur endgame scaffold,
cite version DOI
[`10.5281/zenodo.22311182`](https://doi.org/10.5281/zenodo.22311182).
For the typed `LevelLowering_26` certificate,
cite version DOI
[`10.5281/zenodo.22311107`](https://doi.org/10.5281/zenodo.22311107).
For the Frey Weierstrass model and odd-prime valuation input,
cite version DOI
[`10.5281/zenodo.22310825`](https://doi.org/10.5281/zenodo.22310825).
For the FormalImmersionM3 ledger match,
cite version DOI
[`10.5281/zenodo.22310574`](https://doi.org/10.5281/zenodo.22310574).
For the SageMath `J₀(26)` decomposition and `M₃` certificates,
cite version DOI
[`10.5281/zenodo.22310313`](https://doi.org/10.5281/zenodo.22310313).
For the finite formal-coordinate matrix calculation and unconditional
valuation input, cite
[`10.5281/zenodo.22286630`](https://doi.org/10.5281/zenodo.22286630).
For the corrected finite-only release, cite
[`10.5281/zenodo.22272714`](https://doi.org/10.5281/zenodo.22272714).
The stable DOI for the evolving Foundations project is
[`10.5281/zenodo.22272382`](https://doi.org/10.5281/zenodo.22272382).
Citation metadata is in [`CITATION.cff`](CITATION.cff), and the exact v1 claims
are recorded in
[`docs/releases/v1.0.1-computable.md`](docs/releases/v1.0.1-computable.md).
