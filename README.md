[![v1.0.1-computable DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22272714.svg)](https://doi.org/10.5281/zenodo.22272714)
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
comparison with the genuine cohomological 2-Selmer group and the Abel--Jacobi
cotangent compatibility remain future mathematics.

This is an unconditional statement about the computations themselves. It is
not an unconditional proof of the level-26 endgame.

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
the displayed cotangent matrix from q-expansion coefficients. The local
Tate-conductor theorem, geometric Riemann--Hurwitz identification, and
Picard/Abel--Jacobi cotangent identification remain named boundaries; none is
replaced by `decide`.

The corrected v1.0.1 theorem uses each signed S-unit in the finite-field
equation. It supersedes v1.0.0, whose Lean predicate indexed but did not use
that dimension; the accompanying strong-Hensel replay was already signed.

### v2.0.0 — Frey discriminant foundations

Formalize the Frey-curve discriminant argument in Lean. The target is to
replace `FreyCurveExists` with a theorem constructing the required curve and
proving the discriminant/conductor properties used by the level-26 route.

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
├── docs/                        # design notes and evidence maps
├── lean/                        # minimal Lean entrypoint
├── scripts/                     # deterministic repository checks
├── PLAN.md                      # v1–v4 unconditionalization plan
├── lakefile.lean                # Lean package definition
└── lean-toolchain               # pinned Lean version
```

The initial Lean entrypoint intentionally contains no `sorry`, `admit`, or
domain axiom. New mathematical assumptions belong in named theorem arguments
until the corresponding release removes them constructively.

## Verification

The workflow runs on pushes and pull requests:

```sh
lake exe cache get
lake build BealLevel26Foundations
bash scripts/verify-scaffold.sh
```

The corrected v1.0.1-computable release uses Lean 4.12.0 to match the parent Beal project. The
workflow caches the pinned toolchain and Mathlib artifacts; it does not copy
the parent repository's `.lake` directory or silently import its theorem
boundaries.

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

For reproducible use, cite the corrected version DOI
[`10.5281/zenodo.22272714`](https://doi.org/10.5281/zenodo.22272714).
The stable DOI for the evolving Foundations project is
[`10.5281/zenodo.22272382`](https://doi.org/10.5281/zenodo.22272382).
Citation metadata is in [`CITATION.cff`](CITATION.cff), and the exact v1 claims
are recorded in
[`docs/releases/v1.0.1-computable.md`](docs/releases/v1.0.1-computable.md).
