# Beal Level-26 Foundations

This repository is the foundations chamber for moving the level-26 Beal route
from an explicit conditional assembly toward an unconditional theorem. It is a
new, deliberately smaller repository: the active conditional development and
its remaining tasks stay in
[`DavidFox998/beal-conjecture`](https://github.com/DavidFox998/beal-conjecture).

The governing principle is the same as the parent project: a checked
calculation is evidence for exactly what it computes, while every missing
mathematical bridge is named instead of hidden behind an axiom.

## Starting point

The v10.0.0 Beal assembly already compiles
`Beal.Final.ConditionalBealTheorem` from five explicit premises:

1. `J0DecompositionSoundness_26 J0_26`;
2. `MwrankCertificateSoundness_26`;
3. `FormalImmersionSoundness_26 J0_26 cotangent`;
4. `FreyCurveExists`, reusing `FreyCurveConstruction_26`; and
5. `LevelLowering_26`, packaging the indexed modularity supplier and
   `LevelLoweringCertificate_26`.

This repository does not claim those five premises are already discharged.
Its first release is a staging area for turning the finite level-26 evidence
into constructive Lean foundations. The parent repository remains the
canonical home for the current certificates, conditional theorem, and open
tasks.

## Tentative unconditionalization plan

The staged plan follows four releases.

### v1.0.0 — Computable level-26 foundations

Formalize the explicit `M₃`, the level-26 coefficient ledger, and the singleton
2-Selmer result as reproducible, kernel-checked computations. The target is to
discharge three of the five v10 premises to computable checks, while preserving
the exact interpretation boundaries until their mathematical bridges are
constructed.

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

The current scaffold uses Lean 4.12.0 to match the parent Beal project. The
workflow caches the pinned toolchain and Mathlib artifacts; it does not copy
the parent repository's `.lake` directory or silently import its theorem
boundaries.

## Relationship to `beal-conjecture`

Work remains split intentionally:

- `beal-conjecture` keeps the v10.0.0 conditional assembly and the active
  level-26 tasks, including the full 2-Selmer and formal-geometry work;
- this repository develops the replacement foundations in staged releases;
- migration back to the parent project is a later, explicit decision after a
  foundation is independently checked.

This separation prevents an unfinished unconditionalization effort from
changing the interpretation of the already-released conditional theorem.