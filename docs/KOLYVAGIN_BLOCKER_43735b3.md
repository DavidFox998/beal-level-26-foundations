# Kolyvagin / Mordell--Weil finiteness blocker at baseline `43735b3`

## Scope and pinned environment

This note records the formal boundary of the Kolyvagin branch on:

- foundations baseline `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee`;
- branch lineage `kolyvagin-fintype`;
- branch head `6e88d945e3ede435eb209911abc416bd104e59de`;
- Lean `v4.12.0`;
- Mathlib `809c3fb3b5c8f5d7dace56e200b426187516535a`;
- manifest input revision `v4.12.0`.

`Kolyvagin_MW_Rank0_Numerical.lean` contains only theorem terms supported
by this pin. Existing propositions for Kato/Kolyvagin, two descent, and
Mordell--Weil finiteness remain uninhabited. No target proposition is
introduced as an assumption or axiom.

## Correct rank-zero formulation

The project's earlier name:

```lean
def MordellWeilGroup.IsRankZero (E : WeierstrassCurve K) : Prop :=
  Subsingleton (MordellWeilGroup E)
```

means that the rational point group contains only the identity. That is
stronger than algebraic rank zero and is false for curves with nontrivial
rational torsion. The project proves:

```lean
¬ MordellWeilGroup.IsRankZero curve26a1_Q
¬ MordellWeilGroup.IsRankZero curve26b1_Q
```

using explicit nonzero rational points.

The corrected branch-level target is:

```lean
def MW_rank_zero_fintype (E : WeierstrassCurve K) : Prop :=
  Nonempty (Fintype (MordellWeilGroup E))
```

For these curves, finiteness of the full rational point group is the
appropriate rank-zero statement when the torsion subgroup is nontrivial.
The corrected target remains uninhabited.

## What is proved

The project proves or records:

- `L_over_Omega_26a1 = 1/3`;
- `L_over_Omega_26b1 = 1/7`;
- both displayed rational values are nonzero;
- `Sel2_card_26a1 = 1` and `Sel2_card_26b1 = 1`;
- `2 ^ Sel2_F2_dim_26a1 = 1`;
- `2 ^ Sel2_F2_dim_26b1 = 1`;
- both displayed certified mwrank values are zero;
- the displayed torsion-order product is `3 * 7 = 21`;
- the displayed discriminants are `-17576` and `-1664`; and
- both `Subsingleton` rank-zero predicates are refuted.

These are numerical certificates and explicit point statements. They do
not construct `Fintype (MordellWeilGroup E)`.

## Exact open propositions

The corrected finite-group targets remain:

```lean
def MW_rank_zero_26a1_fintype : Prop :=
  MW_rank_zero_fintype curve26a1_Q

def MW_rank_zero_26b1_fintype : Prop :=
  MW_rank_zero_fintype curve26b1_Q
```

The analytic route is only an implication schema:

```lean
def Kolyvagin_L_nonzero_imp_MW_rank_zero : Prop :=
  (L_26a1_ne_zero → MW_rank_zero_26a1_fintype) ∧
  (L_26b1_ne_zero → MW_rank_zero_26b1_fintype)
```

The two-descent route is also only an implication schema:

```lean
def TwoDescent_implies_MW_rank_zero_fintype : Prop :=
  (Sel2_card_26a1 = 1 → MW_rank_zero_26a1_fintype) ∧
  (Sel2_card_26b1 = 1 → MW_rank_zero_26b1_fintype)
```

The purported analytic antecedents are themselves open propositions:

```lean
def L_26a1_ne_zero : Prop :=
  L_over_Omega_26a1 = (1 / 3 : ℚ) → J0_26_rank0

def L_26b1_ne_zero : Prop :=
  L_over_Omega_26b1 = (1 / 7 : ℚ) → J0_26_rank0
```

They are not theorem terms asserting that a formally defined elliptic-curve
value `L(E,1)` is nonzero.

## Why displayed `L/Ω ≠ 0` is not `L(E,1) ≠ 0`

`L_over_Omega_26a1` and `L_over_Omega_26b1` are recorded rational display
values. The pinned project does not define:

- the complex elliptic-curve `L`-function for these curves;
- analytic continuation or the value at `s = 1`;
- the real period `Ω` as an analytic integral;
- a theorem identifying the recorded rationals with `L(E,1)/Ω`; or
- a transfer from nonzero displayed quotient to nonzero formal `L(E,1)`.

Consequently, proving that `1/3` and `1/7` are nonzero does not supply the
analytic hypothesis of Kato or Kolyvagin.

## Why displayed `|Sel₂| = 1` does not construct a `Fintype`

`Sel2_card_26a1` and `Sel2_card_26b1` are stored natural-number
certificates. There is no formal two-Selmer group whose cardinality is being
computed. In particular, the project lacks:

- a Selmer group attached to each displayed curve;
- the Kummer and local-condition maps defining it;
- the exact sequence relating `E(ℚ)/2E(ℚ)`, `Sel₂(E)`, and
  `Sha(E)[2]`;
- a proof that the displayed certificate computes that group;
- finite generation of the project's `MordellWeilGroup E`; and
- a construction proving that every rational point is torsion.

The equality of a stored natural number with `1` cannot create a
`Fintype` instance for the point group.

## Missing pinned-library infrastructure

Pinned Mathlib does not provide the connected development needed here:

1. elliptic-curve `L`-functions and their value at `s = 1`;
2. periods and a theorem interpreting the displayed `L/Ω` values;
3. Kato or Kolyvagin's theorem from `L(E,1) ≠ 0` to algebraic rank zero
   and finiteness results;
4. a formal Tate--Shafarevich group for these curves;
5. Mordell--Weil finite generation for the project's affine-point group;
6. formal two-Selmer groups and their exact sequences;
7. a verified bridge from the displayed descent certificates to those
   groups; and
8. a proof that every rational point on `26a1` and `26b1` is torsion,
   yielding `Nonempty (Fintype (MordellWeilGroup E))`.

Until those interfaces are available, the numerical module is the strongest
honest Kolyvagin/rank-zero surface supported by the pinned project.