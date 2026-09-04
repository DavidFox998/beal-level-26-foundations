# Plan: Beal Level-26 Foundations

## Purpose

Build a clean, independently checkable foundation for the level-26 Beal route.
The goal is not to relabel the v10.0.0 conditional theorem. The goal is to
replace its theorem-valued boundaries one at a time with actual Lean
constructions and proofs.

The companion project,
[`beal-conjecture`](https://github.com/DavidFox998/beal-conjecture), remains
the source of truth for the conditional theorem assembly. This repository
develops independently checked foundations and never changes the companion
theorem's status merely by reproducing finite evidence.

## Premise ledger

| v10 premise | Initial status here | Intended replacement |
|---|---|---|
| `J0DecompositionSoundness_26 J0_26` | inherited boundary | Construct the relevant Jacobian/isogeny realization and its rational-point consequences. |
| `MwrankCertificateSoundness_26` | inherited boundary | Prove the finite ledger, covering completeness, 2-Selmer identification, and rank semantics from typed certificates. |
| `FormalImmersionSoundness_26 J0_26 cotangent` | inherited boundary | Construct the Abel–Jacobi cotangent map and prove the formal-immersion/cusp criterion in scheme geometry. |
| `FreyCurveExists` | inherited supplier | Prove the Frey curve, discriminant, reduction, and level-26 properties directly in Lean. |
| `LevelLowering_26` | inherited supplier | Build the modular-form and Galois-representation level-lowering theorem without an external supplier. |

The v1 target is to move the first three rows as far as possible toward
computable checks. The v2 and v3 targets remove the final two supplier
boundaries. v4 composes the resulting constructive chain.

## Staged milestones

### v1.x — Computable certificate foundations

**Scope**

- Derive the explicit level-26 `M₃` witness from the normalized eigenform
  coefficients and displayed basis change.
- Make the coefficient ledger finite, typed, and replayable.
- Record the computed eight-candidate outcome without calling it a singleton
  2-Selmer result.
- Preserve transcript hashes and source provenance without treating them as
  proofs of their own semantics.
- Add focused CI checks for every finite witness.

**Acceptance gates**

- Exact matrix shape and rank are checked in Lean.
- Every ledger row has a typed finite-field status result at `2` and `13`.
- The complete finite audit is proved to retain all eight S-unit indices.
- No `axiom`, `sorry`, `admit`, or vacuous `True` declaration is introduced.
- The README identifies which interpretation premises remain.

**Current status:** the coefficient matrix, basis change, derived `M₃`,
determinant, typed ledger, cardinalities, and all eighty finite checks are
complete. A standard-library producer separately replays all 160 strong-Hensel
witnesses at `2` and `13`. v1.3.0--v1.4.0 add SageMath 10.7 certificates and
the Lean 4.12 bridges `J0_26_Decomp` and `FormalImmersionM3`. v2.0.0-frey
defines the parent integral Frey Weierstrass model and proves `c₄,c₆,Δ` by
`ring`, plus the odd-prime valuation input `vₚ(c₄)=0`, `vₚ(Δ)>0`. v3.0.0-ribet
adds typed `LevelLowering_26` certificate data (representation, level, and
the exact-divide relation) and the arithmetic `vₚ(26 p)=1` from `p ∤ 26`.
Tate/Kodaira classification, Ribet existence, Jacobian geometry, Selmer, and
Abel--Jacobi remain explicit later milestones. It does not replace the parent
`FreyCurveExists` or `LevelLowering_26` suppliers.

### v2.0.0 — Frey discriminant theorem

**Scope**

- Define the indexed Frey curve from a primitive Beal counterexample.
- Prove the discriminant formula and its nonvanishing.
- Prove the reduction and conductor facts needed to identify level `26`.
- Replace `FreyCurveExists` with a theorem-valued construction.

**Acceptance gates**

- The theorem returns actual curve data, not only an existence `Prop`.
- Discriminant and bad-prime claims are proved from the displayed model.
- The resulting interface can feed the parent `frey_to_X0_26_point` route
  without a supplier axiom.

**Dependency:** v1 certificate types and the parent Frey API.

### v3.0.0 — Ribet level-lowering theorem

**Scope**

- Add or develop the Mathlib modular-form objects required by the argument.
- Define the Galois representation and modular-form compatibility data.
- Prove the level-lowering relation from the stated local hypotheses.
- Replace the supplier-backed `LevelLowering_26`.

**Acceptance gates**

- The lowering theorem is indexed by the representation, weight, and levels.
- No global modularity or level-lowering axiom is smuggled into a wrapper.
- The output is directly consumable by the level-26 Frey-to-curve bridge.

**Current status:** v3.0.0-ribet exposes `LevelLowering_26` as indexed
certificate data and proves the exact-divide arithmetic available in
Mathlib 4.12. It does not construct residual Galois representations, Hecke
algebras, or a realizing newform, and it does not replace the parent
supplier.

**Dependency:** v2 and the required Mathlib modular-forms foundations.

### v4.0.0 — Constructive Mazur endgame

**Scope**

- Construct the Jacobian/isogeny realization for `J₀(26)`.
- Connect `M₃` to the actual cotangent map at `2`.
- Prove the formal-immersion criterion and four-cusp rational-point result.
- Compose the constructive Frey and Ribet results into an unconditional
  `BealTheorem`.

**Acceptance gates**

- `X₀(26)(ℚ) = four_cusps` is a theorem, not a soundness premise.
- The Frey point is proved noncuspidal and cannot lie in that set.
- The final theorem has no domain-specific axioms or suppliers.
- A full CI run checks the complete chain and a transitive axiom audit.

**Current status:** v4.0.0-mazur adds `BealLevel26Foundations.Mazur.EndgameScaffold`
with four typed premises (`J0_26_Q_RankZero26`, `FormalImmersionAtTwo26`,
`X0_26_RationalPoints26`, `NoFreyPoint26`) and
`BealTheoremFromMazurChain26`, which concludes `BealTheorem` only from
those structures plus v2 Frey Weierstrass and v3 `LevelLowering_26`.
v4.0.1-jacobian-skeleton adds `Jacobian/J0_26_DecompActual` (finite
`s₁=q₁+q₂`, `s₂=-q₁q₂` model and the certified `26a × 26b` distinction
`a₂=-1` versus `1`, plus `M₃` by `decide`) and moves
`PicardAbelJacobiIdentification_26` to a standalone Jacobian file.
v4.0.2-selmer adds `Jacobian/TwoSelmer_vs_SUnits_26`: the eight S-unit
indices are audited, proved to retain all eight and not to be a
singleton, and therefore not mislabeled as genuine cohomological
2-Selmer. `MwrankCertificateSoundness_26` packages Sage
`certified_mwrank = 0` for `26a` and `26b` with that audit and the
already-decided `s₁,s₂` / `a₂` data. v4.0.3-formal-immersion adds
`Jacobian/FormalImmersionActual_26`: q-expansion `M₃` is injective
(`det = 2 ≠ 0`) and inhabits `FormalImmersionAtTwo26.of_qExpansion`.
That replaces the formal-immersion *input* premise by finite cotangent
injectivity. v4.0.4-x026-rational-points adds
`Mazur/X026RationalPointsActual_26`: displayed four cusps
`[1, 2, 13, 26]` (`= divisors26`, length `4 = cuspCount26`) plus
already-decided `a₂` / `MwrankCertificateSoundness_26` /
`FormalImmersionAtTwo26.of_qExpansion`.
`X0_26_RationalPoints26.of_qExpansion` is a finite package that can
replace the `X0_26_RationalPoints26` premise;
`ofRankZeroAndImmersion` returns that package and does not read
geometric rank. It does not construct a Mathlib Jacobian, prove
Mordell--Weil rank, identify the audit with `Sel₂(J₀(26)/ℚ)`, prove a
scheme-theoretic formal immersion, inhabit `J0_26_Q_RankZero26` as
`True`/`trivial`, inhabit `NoFreyPoint26`, prove a Mathlib
`X₀(26)(ℚ)` theorem, or claim an unconditional `BealTheorem`. The
PLAN.md acceptance gates above remain open.

**Dependency:** v1, v2, v3, and genuine scheme/Jacobian geometry.

## Roadmap status

The v2--v4 headings are planning markers, not claims that those mathematical
bridges have been completed. The genuine Selmer comparison, Mordell--Weil
interpretation, Jacobian geometry, q-expansion/cotangent compatibility, Frey
construction, and level lowering remain future work until their actual Lean
theorems pass the corresponding acceptance gates.

## Release discipline

Each milestone should ship only after:

1. its focused Lean target builds on the pinned toolchain;
2. finite certificate checks are deterministic;
3. a transitive axiom scan identifies only accepted Lean foundations;
4. the README states exactly which v10 premise has been discharged; and
5. the parent repository link and migration boundary remain current.

The version labels are tentative planning markers, not claims that the
corresponding mathematics has already been completed.