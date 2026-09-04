[![v1.3.0 DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22310313.svg)](https://doi.org/10.5281/zenodo.22310313)
[![Concept DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22272382.svg)](https://doi.org/10.5281/zenodo.22272382)
[![CI](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml/badge.svg)](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml)

# Beal Level-26 Foundations

This repository is the foundations chamber for moving the level-26 Beal route
from an explicit conditional assembly toward a theorem whose remaining
mathematical bridges are constructed one by one. It is a deliberately smaller
repository: the conditional development stays in
[`DavidFox998/beal-conjecture`](https://github.com/DavidFox998/beal-conjecture).

The governing principle is the same as the parent project: a checked
calculation is evidence for exactly what it computes, while every missing
mathematical bridge is named instead of hidden behind an axiom.

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

`BealLevel26Foundations.Scaffold` gathers three premise-bearing structures for
the mathematics that remains: Frey-conductor data, the geometric
Riemann--Hurwitz interpretation at level 26, and the Abel--Jacobi/q-expansion
cotangent comparison. These modules introduce no global axiom and make no
unconditional endgame claim; their theorems conclude only from supplied
bridge data.

### Real arithmetic extension

`BealLevel26Foundations.Real` goes beyond the bridge structures where Mathlib
4.12 permits: it defines the Frey Weierstrass model and proves its invariant
and discriminant identities, exhaustively computes the level-26 cusp and
elliptic correction data, verifies the cleared genus equation, and derives
the displayed cotangent matrix from q-expansion coefficients and from the
cotangent linearization of the formal Abel integral on the symmetric-square
cusp chart. The local Tate-conductor classification and geometric
Riemann--Hurwitz identification remain named boundaries; neither is replaced
by `decide`.

## DOI / Citation — versioned audit trail

| Version | Git Tag / Commit | Zenodo DOI | Audit / Notes |
| :--- | :--- | :--- | :--- |
| v1.0.0 unconditional computable foundations | `v1.0.0-computable` / `6aa613c` | [10.5281/zenodo.22272382](https://doi.org/10.5281/zenodo.22272382) (concept) | 2315/2315 passed, 0 axiom/sorry/admit, ledger 101 coeff SHA-256 audited, 160 Hensel witnesses, finite checks not called genuine Selmer |
| v1.1.0 arithmetic frey genus qexpansion matrix | `v1.1.0-arithmetic-frey-genus-qexpansion-matrix` / `c670d1c` | [10.5281/zenodo.22284436](https://doi.org/10.5281/zenodo.22284436) | 2315 isolated + 2319 real green, arithmetic Frey c4/c6/Δ via `ring` with no `frey_conductor_data`, arithmetic genus index 42 divisors `[1,2,13,26]`, cusp 4, ν2=2, ν3=0, certificate 2 via `decide`; ledger-derived `M3 = [[1,1],[0,2]]`, det=2 via `decide`; Picard bridge isolated as `PicardAbelJacobiIdentification_26` |
| v1.1.1 choice-clean representation | `v1.1.1-choice-clean-representation-dependency` / `1c2c52b` | [10.5281/zenodo.22285575](https://doi.org/10.5281/zenodo.22285575) | Full parent integration: explicit `ledgerM3` has footprint `[propext, Classical.choice, Quot.sound]`; even `fun _ _ => 0 : Matrix (Fin 2) (Fin 2) (ZMod 3)` has the same footprint in Mathlib 4.12. This is a representation dependency, not a domain axiom. Focused point checks at 2 and 13 audit to the genuinely choice-free two-item footprint `[propext, Quot.sound]`. Quartic ledgers under the `Beal17Mazur.Jacobian` namespace are fixed. The formal-immersion certificate was regenerated because its source now imports `ledgerM3` instead of duplicating a literal: source hash and checksum changed, while matrix, determinant, level, and prime did not. |
| v1.2.0 formal-coordinate matrix and valuation input | `v1.2.0-abel-jacobi-differential-closed-valuation-input` / `ed74e3b` | [10.5281/zenodo.22286222](https://doi.org/10.5281/zenodo.22286222) | A finite model in coordinates `s₁=q₁+q₂`, `s₂=-q₁q₂` derives `[[1,1],[0,2]]`; it does **not** construct or identify an actual Picard/Abel--Jacobi cotangent map. Odd-prime input proves `vₚ(c₄)=0` and `vₚ(Δ)>0` without `frey_conductor_data`. The `[propext, Classical.choice, Quot.sound]` footprint is representational. Both geometric compatibility and Tate/Kodaira conductor classification remain explicit. Archive SHA-256 `9ea2b4f7d95460315736fb9f926678d57b39af5b682b168849173ea6cbd891fa`. |
| v1.2.1 corrected formal-coordinate boundary | `v1.2.1-formal-coordinate-boundary-corrected` / `05b8159` | [10.5281/zenodo.22286630](https://doi.org/10.5281/zenodo.22286630) | Corrective immutable release: the finite model remains, but `PicardAbelJacobiIdentification_26` is premise-bearing and no theorem identifies it with an actual geometric cotangent map. Archive SHA-256 `001d43aa7d02a93ab75122c58c8bf99e9e1395957a4e6657ce32e75b53b5e9e5`. |
| v1.3.0 J0(26) decomposition and M3 certificates | `v1.3.0` / `e657d15` | [10.5281/zenodo.22310313](https://doi.org/10.5281/zenodo.22310313) | SageMath 10.7 certificates for `J₀(26)` dim 2 = `26a × 26b` and rank-2 `M₃=[[1,1],[0,2]]` over `𝐅₃`. Lean 4.12 proves Weierstrass `c₄,c₆,Δ` for the two Cremona models and ledger agreement. Not a Jacobian, Mordell--Weil, or formal-immersion theorem. Ledger SHA-256 `9671052435714618d8106b25ed3f04fd7b87d5332ebccf76f949f768276c6875`. Archive SHA-256 `b748a2bfd30037ad1c1b2aeb8cf26795b2f8ca56f57d3e3f5137cc41ab9690da`. |
| v1.4.0 FormalImmersionM3 ledger match | `v1.4.0` | Zenodo version DOI minted by this git tag | Lean 4.12 `Beal.Foundations.FormalImmersionM3` reads `sagemath/certs/formal_immersion_M3.json` and proves `M₃=[[1,1],[0,2]]`, `det=2` over `ZMod 3` by `decide`, matching `ledgerM3`. Not a Jacobian, Mordell--Weil, or Picard theorem. Ledger SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |

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

Formalize the Ribet level-lowering certificate as Lean
`LevelLowering_26` without a supplier. This milestone depends on the required
Mathlib modular-forms infrastructure and should expose each representation,
level, and lowering relation as typed data rather than a single opaque claim.

### v4.0.0 — Mazur endgame

Formalize the remaining Mazur chain:

```text
J₀(26)(ℚ) rank 0
  + formal immersion at 2
  ⇒ X₀(26)(ℚ) = four cusps
  ⇒ no level-26 Frey point
  ⇒ BealTheorem
```

The intended endpoint is an unconditional `BealTheorem`, but only after the
actual Jacobian, cotangent-map, rational-point, Frey, and level-lowering
bridges have been constructed and audited. A green scaffold build is not that
endpoint.

The detailed milestones, acceptance gates, and dependency order are in
[`PLAN.md`](PLAN.md).

## Repository layout

```text
.
├── .github/workflows/main.yml   # reproducible Lean and scaffold checks
├── DOCKERFILE                   # Elan + Lean 4.12.0 + Mathlib verification image
├── docs/                        # design notes and evidence maps
├── lean/                        # Lean entrypoints (computable, scaffold, real, Beal.Foundations)
├── sagemath/                    # coefficient ledger and SageMath certificates
│   └── certs/                   # v1.3.0 J₀(26) and M₃ JSON archives
├── scripts/                     # deterministic repository checks
├── PLAN.md                      # v1–v4 unconditionalization plan
├── lakefile.lean                # Lean package definition
└── lean-toolchain               # pinned Lean 4.12.0
```

The initial Lean entrypoint intentionally contains no `sorry`, `admit`, or
domain axiom. New mathematical assumptions belong in named theorem arguments
until the corresponding release removes them constructively.

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
