# Phase 3 blueprint

Project board for the scheme-theoretic Jacobian / formal-immersion /
Chabauty--Coleman work. Ledger remains v1.4.0 SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`.
No version DOI unless explicitly requested. No `theorem BealTheorem`.
The displayed-cusp audit `Mazur/X026RationalPointsActual_26` stays
unchanged.

Mathlib 4.12 has no modular-curve scheme, no Jacobian of `X₀(26)`,
no Abel--Jacobi map, no completed-local-ring formal immersion, and
no Coleman integral. This folder does not add `sorry`, `axiom`, or
`admit`. Named Lean boundaries live next to this board.

## Track A — Jacobian as scheme

Status: **named boundaries shipped** (`v4.0.12-scheme-stub-no-doi`).

| File | What it is | What it is not |
|---|---|---|
| [`../Jacobian/J0_26_Scheme_26.lean`](../Jacobian/J0_26_Scheme_26.lean) | Premise-bearing `J0_26_Scheme` / `J0_26_Scheme_26` | Not a Mathlib Jacobian; not the finite product `26a × 26b`; not inhabited |
| [`../Jacobian/AbelJacobi_26.lean`](../Jacobian/AbelJacobi_26.lean) | Premise-bearing Abel--Jacobi data (`∞ ↦ 0`, cusps torsion) | Not a map `X₀(26) → J₀(26)` |

References (not imported, not discharged): Mumford, *Abelian Varieties*;
Rohrlich on the cuspidal divisor class group and the Abel--Jacobi map
of `X₀(N)`.

## Track B — Formal immersion at 2

Status: **named `det ≠ 0` package shipped**
(`v4.0.13-formal-immersion-proof-no-doi`).

| File | What it is | What it is not |
|---|---|---|
| [`../Jacobian/FormalImmersionActual_26.lean`](../Jacobian/FormalImmersionActual_26.lean) | `formalImmersion_at_2_surjective_from_M3` is `of_qExpansion.input.det ≠ 0` | Not surjectivity of a map of completed local rings |
| [`../Jacobian/ResidueDisksProof_26.lean`](../Jacobian/ResidueDisksProof_26.lean) | Alias `diskEqualityFromImmersion` of that same `det ≠ 0` | Not a residue-disk theorem |

Remaining: completed local rings / q-expansion at `∞`, and a genuine
residue-disk implication from rank zero plus immersion. Do not treat
`M₃` injectivity as scheme-theoretic immersion.

Reference (not imported, not discharged): Mazur 1978 Prop III.3.2.

## Track C — Mordell--Weil sieve / Chabauty--Coleman

Status: **not started.** Remaining: Coleman integrals and a genuine
`∀ P : X₀(26)(ℚ), P ∈ {cusps}`. Mathlib 4.12 has no such point type.

## Track D — LMFDB certificates

Status: **not started.** Must not change
`sagemath/level_26_ledger.json`. Any LMFDB file is extra computational
evidence, not a Mordell--Weil theorem.
