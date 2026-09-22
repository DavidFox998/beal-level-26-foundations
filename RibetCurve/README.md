# Ribet level-lowering library

This directory develops the `928 → 32` route in forward mathematical order.
It separates concrete arithmetic and representation records from the deep
theorems unavailable in the pinned Lean 4.12 / Mathlib revision.

## Modules

- `Modularity.lean` packages an elliptic curve with the displayed Frey
  `j`-invariant and states the specialized Wiles/BCDT construction target.
- `GaloisRep.lean` defines an abstract two-dimensional residual
  representation, designated inertia at `29`, irreducibility, unramifiedness,
  and the exact compatibility needed to use the Mazur `X₀(13)` implication.
- `Conductor.lean` defines local conductor and global Néron-conductor
  certificates and proves how a certificate specializes to the displayed
  values `32` and `928`.
- `LevelLowering.lean` defines the residual eigenform data that a genuine
  Ribet theorem must produce at level `32`.
- `Newform32.lean` separates the missing identification with `32a1` from the
  complete trace-exclusion target.
- `KrausElimination.lean` reuses the exact finite-field trace and coefficient
  table and exposes the proved good-reduction mismatch at `29`.
- `BlockerDoc.lean` consumes the proved numerical surface and records the
  remaining assumptions in construction order.

## What the numerical layer proves

`Ribet_928_to_32_Numerical.lean` proves the displayed division and
multiplication identities, selector values, dimension and table-length
numerals, `a₂₉(32a1) = -10`, Sturm arithmetic, and the cardinality of an
explicitly empty candidate set.  This file is preserved unchanged.

These theorems do not identify `32` or `928` with a Néron conductor.
Likewise, dimension one does not construct the eigenform produced by level
lowering, identify it with `32a1`, or prove a mismatch for every residue
class.

## Remaining boundary

The uninhabited boundary consists of modularity of the displayed Frey curve,
attachment of its geometric mod-`13` representation, absolute irreducibility
through the two Mazur inputs, Tate's algorithm and the Néron conductor,
cyclotomic inertia and unramifiedness at `29`, Ribet's theorem, identification
with `32a1`, and a complete Kraus elimination including the classes where
`29` divides `A`, `B`, or `B+3`.