# Tate conductor blocker at baseline `43735b3`

## Scope

This note records the exact boundary of the Tate-at-`29` formalization on:

- foundations baseline `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee`;
- branch lineage `tate-v29`;
- Lean `v4.12.0`;
- Mathlib `809c3fb3b5c8f5d7dace56e200b426187516535a`;
- manifest input revision `v4.12.0`.

`Tate_Frey_Conductor_29_Numerical.lean` contains the local numerical theorem
terms available at this pin. The existing propositions for Tate
uniformization, inertia, and the Néron conductor remain explicitly
uninhabited. No target proposition is introduced as an assumption or axiom.

## What is proved

For the displayed Frey model

```text
y² = x(x - A⁴)(x + B⁴),
```

the project proves:

- `Δ = 16 A⁸ B⁸ (A⁴ + B⁴)²`;
- the corresponding natural-number discriminant identity;
- both discriminant specializations at `(A,B)=(1,1)` equal `64`;
- on a gap-3 solution with `29 ∤ A` and `29 ∤ B`,
  `v₂₉(Δ) = 26 v₂₉(B+3)`;
- if also `29 ∣ B+3`, then `13 ∣ v₂₉(Δ)`;
- the displayed branch selector is `32` when `29 ∤ A,B`;
- the displayed branch selector is `928` when `29 ∣ A` or `29 ∣ B`;
- `928 / 29 = 32`;
- `32 * 29 = 928`.

The `32`/`928` selector is project display data. It is not a formal Néron
conductor.

## Missing pinned-library infrastructure

Pinned Mathlib supplies Weierstrass curves, affine/projective/Jacobian
models, group laws, division polynomials, p-adic valuations, and general
valuation-theoretic inertia subgroups.

It does not supply the connected elliptic-curve infrastructure required for
the intended theorem:

1. Tate elliptic curves over a nonarchimedean local field;
2. Tate uniformization of the displayed Frey curve;
3. inversion of the full Tate `j`-series to attach a parameter `q`;
4. Kodaira reduction types and Tate's algorithm;
5. minimal elliptic models over local fields;
6. elliptic Néron conductors and local conductor exponents;
7. elliptic-curve mod-`13` Galois representations;
8. the inertia action on `E[13]`; and
9. the Tate-curve cyclotomic inertia formula showing triviality when
   `13 ∣ v₂₉(q)`.

The existing truncated expression

```text
q⁻¹ + 744 + 196884q
```

has the required valuation behavior, but it is not a Tate parameter attached
to the Frey curve and cannot be used as one.

## Existing open proposition chain

The current source honestly records:

```lean
def Tate_uniformization : Prop :=
  tate_curve_at_29

def Tate_q : Prop :=
  Tate_uniformization

def inertia_trivial_mod13_when_13_dvd_v : Prop :=
  inertia_at_29_trivial_mod13_full
```

These declarations name missing interfaces; they do not inhabit them.

The chain eventually reaches:

```lean
def ribet_unramified_at_29_of_dvd_C : Prop :=
  ∀ A B : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
    29 ∣ B + 3 → ¬ 29 ∣ A → ¬ 29 ∣ B →
      residualOddEstimate A B ∣ 32
```

with:

```lean
def residualOddEstimate (A B : ℕ) : ℕ :=
  32 * oddRadical (A * B)
```

This target is global. It requires every odd prime dividing `A*B` to
disappear from the residual level. A local theorem at `29` cannot prove it.
It would additionally require a global level-lowering theorem, elimination
of all other odd prime factors, or a proof that no relevant solutions exist.

## Alias-direction problem

The intended mathematical direction is:

```text
Tate uniformization
  → Tate parameter and cyclotomic inertia formula
  → trivial mod-13 inertia at 29
  → a Ribet unramified/local level-lowering input.
```

An inhabitant of the final inertia or level-lowering conclusion does not
construct Tate uniformization in the reverse direction. Therefore
`Tate_algorithm_at_29` and `Frey_Neron_conductor` cannot honestly be derived
backward from `Frey_conductor_29_is_Neron` under their current types.

## Required development before the full theorem

An honest full implementation requires a new library layer connecting:

1. the displayed `WeierstrassCurve ℚ` to a curve over `ℚ_[29]`;
2. minimality and multiplicative reduction at `29`;
3. an attached Tate parameter `q`;
4. `v₂₉(q)` to the minimal discriminant valuation;
5. the mod-`13` representation and its inertia restriction;
6. the cyclotomic inertia formula;
7. the local conductor exponent and Néron conductor; and
8. a separately stated global Ribet theorem that does not conflate the
   local prime `29` with every odd prime dividing `A*B`.

Until those interfaces exist, the numerical theorem file is the strongest
honest Tate-at-`29` result supported by this pinned project.