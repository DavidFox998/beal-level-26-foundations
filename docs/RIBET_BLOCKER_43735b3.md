# Ribet `928 → 32` blocker at baseline `43735b3`

## Scope and pinned environment

This note records the formal boundary of the Ribet branch on:

- foundations baseline `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee`;
- branch lineage `ribet-928-32`;
- branch head `b61bec2bfbd735707fab2abd6d9f3647b3b2b7fd`;
- Lean `v4.12.0`;
- Mathlib `809c3fb3b5c8f5d7dace56e200b426187516535a`;
- manifest input revision `v4.12.0`.

`Ribet_928_to_32_Numerical.lean` contains only theorem terms supported by
this pin. Existing propositions for modularity, Galois representations,
inertia, level lowering, and newform elimination remain uninhabited. No
target proposition is introduced as an assumption or axiom.

## What is proved

The project proves or records:

- `928 / 29 = 32`;
- `32 * 29 = 928`;
- `928 ≠ 32`;
- `29 ∤ 32`;
- the displayed selector `level_after_ribet_29 A B` is `32` when
  `29 ∤ A` and `29 ∤ B`;
- the same selector is `928` when `29 ∣ A` or `29 ∣ B`;
- the recorded LMFDB level-32 full-space dimension is `1`;
- the recorded level-32 newform-name list has one entry, `32a1`;
- the recorded coefficient is `a₂₉(32a1) = -10`;
- the arithmetic identities `32 * 3 / 2 = 48` and
  `2 * 48 / 12 = 8`; and
- an explicitly empty `Finset` has cardinality zero.

The pinned branch has no formal level-16 modular-form-space object and no
formal Sturm-bound object. Therefore the level-16 zero, index, Sturm, and
empty-set statements in the numerical file are deliberately labeled as
numeral or finite-container identities. They are not dimension, Sturm, or
newform-classification theorems in Mathlib.

## Exact open proposition chain

The local and Ribet chain is:

```lean
def ribet_level_lowering_29_to_32 : Prop :=
  inertia_trivial_mod13_when_13_dvd_v →
    ribet_lowers_Frey_to_level_32

def Ribet_928_to_32 : Prop :=
  ribet_level_lowering_29_to_32
```

The modularity input remains:

```lean
def modular_Frey : Prop :=
  modularity_Frey_semistable
```

The residual level-32 elimination target is:

```lean
def level_32_no_newform_for_Frey_gap3 : Prop :=
  ∀ A B : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13 → 0 < B →
    ∃ l : ℕ, Nat.Prime l ∧ l ≠ 2 ∧ l ≠ 13 ∧
      ¬ l ∣ A ∧ ¬ l ∣ B ∧ ¬ l ∣ B + 3 ∧
      some (frey_ap l (A % l) (B % l)) ≠ newform_32a1_ap l
```

Its aliases remain uninhabited:

```lean
def no_newforms_at_32_mod13 : Prop :=
  level_32_no_newform

def explicit_a29_mod13 : Prop :=
  Ribet_level_lowering_abstract

def Ribet_level_lowering_abstract : Prop :=
  ribet_level_lowering_29_to_32
```

Renaming or aliasing these propositions does not provide their proofs.

## Why `928 / 29 = 32` is not level lowering

The identity

```text
928 / 29 = 32
```

is necessary arithmetic after deciding that a local factor `29` is legally
removed from a conductor. It does not prove:

- that `928` is the Néron or residual conductor of the Frey curve;
- that the local conductor exponent at `29` is removable;
- that the mod-`13` representation is unramified at `29`;
- that the representation is absolutely irreducible;
- that the Frey curve is modular;
- that Ribet's theorem applies; or
- that the lowered representation is represented by a level-32 newform.

Likewise, a recorded one-entry list `["32a1"]` is data, not a construction
of the weight-2 newspace or a theorem that every relevant residual
eigenform arises from that entry.

## Dependencies on the open Tate and Mazur branches

The intended level-lowering application depends on two independently open
inputs:

1. **Tate/local branch:** Tate uniformization, the precise local reduction
   type and conductor exponent, and the mod-`13` inertia calculation proving
   unramifiedness at `29`.
2. **Mazur/irreducibility branch:** a formal Frey mod-`13` Galois
   representation and a proof of its absolute irreducibility or equivalent
   non-Borel statement.

The numerical Tate and Mazur files prove only their respective displayed
arithmetic surfaces. They do not inhabit these Galois-theoretic inputs.

## Missing pinned-library infrastructure

Pinned Mathlib does not provide the connected development required for the
full argument:

1. modularity of the displayed Frey elliptic curve;
2. its mod-`13` Galois representation;
3. absolute irreducibility from the open Mazur branch;
4. unramifiedness at `29` from the open Tate branch;
5. a precise Néron conductor and local conductor exponent;
6. Ribet level lowering specialized to `p = 13`, removing `29`;
7. construction of the matching residual eigenform/newform at level `32`;
8. a formal level-32 newspace and Sturm comparison;
9. the explicit `a₂₉` congruence obtained from level lowering; and
10. a complete Kraus trace-mismatch argument eliminating every gap-3
    residue class, including bad-reduction cases.

Lean `v4.12.0` / Mathlib `809c3fb` has general modular-form definitions,
but no theorem connecting all these elliptic-curve, Galois, conductor, and
newform objects. Until that infrastructure exists, the numerical module is
the strongest honest Ribet surface supported by the pinned project.