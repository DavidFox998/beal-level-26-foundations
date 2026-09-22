# Mazur / `X₀(13)` blocker at baseline `43735b3`

## Scope and pinned environment

This note records the formal boundary of the Mazur branch on:

- foundations baseline `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee`;
- branch lineage `mazur-x0-13`;
- branch head `146d463c83f0c350c24b7f5a835b7608044fc207`;
- Lean `v4.12.0`;
- Mathlib `809c3fb3b5c8f5d7dace56e200b426187516535a`;
- manifest input revision `v4.12.0`.

`Mazur_X0_13_Numerical.lean` contains only the numerical theorem terms
supported by this pin. Existing propositions for the modular-curve,
isogeny, Galois-representation, and image arguments remain uninhabited.
No target proposition is introduced as an assumption or axiom.

## What is proved

The project has theorem terms for:

- the displayed genus numeral `0`;
- the displayed standard-cusp count `2`;
- `13 * 12 * 14 = 2184`;
- `13 = 2² + 3²`;
- `2 * (13 - 1)² = 288`;
- `48 < 2184`; and
- `288 / 48 = 6`.

These are honest numerical statements. In particular:

- the genus and cusp declarations are natural-number display data, not a
  constructed modular curve with a computed genus or cusp scheme;
- `X₀(13)` has genus zero and rational cusps, so its rational points are
  infinite rather than only the two cusps;
- Mazur's rational cyclic-isogeny degree list includes degree `13`;
- `48 < 2184` does not identify either number with the order of the image
  of the Frey representation.

## Exact open proposition chain

The current Mazur route is recorded as:

```lean
def reducible_13_iff_j_in_image : Prop :=
  ∀ A B : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
    ¬ MazurIrreducibility13.rho_Frey_mod13_irreducible →
      ∃ t : ℚ, t ≠ 0 ∧ frey_j A B = j_of_X0_13 t

def no_t_gives_Frey_j_when_29_dvd_C : Prop :=
  ∀ A B : ℕ, ∀ t : ℚ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 → 1 ≤ B →
      ¬ 29 ∣ A → ¬ 29 ∣ B → 29 ∣ B + 3 →
        t ≠ 0 → frey_j A B ≠ j_of_X0_13 t

def mazur_irreducible_13_via_X0_13 : Prop :=
  reducible_13_iff_j_in_image → no_t_gives_Frey_j_when_29_dvd_C →
    MazurIrreducibility13.rho_Frey_mod13_irreducible
```

Thus even applying `mazur_irreducible_13_via_X0_13` requires two
uninhabited antecedents. It is not an already-proved Mazur theorem.

The later aliases remain:

```lean
def frey_no_rational_13_isogeny : Prop :=
  mazur_irreducible_13_via_X0_13

def Serre_non_Borel_mod13 : Prop :=
  card_32a1_le_48

def mazur_no_Frey_13_isogeny : Prop :=
  mazur_irreducible_13_theorem
```

None of these aliases supplies an inhabitant.

## Missing pinned-library infrastructure

Pinned Mathlib does not provide the connected development needed here:

1. a modular-curve or moduli-stack object realizing `X₀(13)` over `ℚ`;
2. its interpretation as elliptic curves equipped with a rational cyclic
   subgroup of order `13`;
3. a theorem relating reducibility of `ρ̄_{E,13}` to a rational cyclic
   `13`-isogeny and hence to a rational point or parameter on `X₀(13)`;
4. a formal mod-`13` Galois representation attached to the displayed Frey
   elliptic curve;
5. a proof that the displayed Fricke `j`-map parametrizes the required
   moduli problem for that formal curve;
6. a global argument excluding every rational parameter `t` compatible
   with a gap-3 solution; and
7. a formal image subgroup whose order and Borel containment can be
   compared with `48`, `288`, and `2184`.

The existing local calculations at `29` restrict valuations of possible
parameters. They do not exclude every rational parameter globally.

## Why the cardinality inequalities do not prove non-Borel

The inequality

```text
48 < 2184
```

only compares two natural numbers. To prove that the Frey image is
non-Borel, one first needs:

- a defined representation `ρ̄_{E,13}`;
- its image as a subgroup of `GL₂(𝔽₁₃)`;
- a theorem identifying the relevant full or determinant-compatible
  comparison group;
- a theorem that reducibility is equivalent to Borel containment; and
- a proved image order or lower bound for this particular Frey curve.

Likewise, the uninhabited proposition `card_32a1_le_48` concerns the
displayed CM comparison curve, not the Frey image. Even an inhabited
`card(im ρ_{32a1,13}) ≤ 48` would not transfer to the Frey curve without a
proved representation isomorphism. The bare inequalities cannot supply
these missing objects or identifications.

Until those interfaces and global arguments exist, the numerical module is
the strongest honest Mazur surface supported by the pinned project.