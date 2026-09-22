# Mazur and `X₀(13)` library

This directory develops the degree-`13` isogeny route in forward
construction order while keeping every unavailable geometric or global input
explicit.

## Modules

- `X0_13_Moduli.lean` defines `E(K)[13]` as the kernel of multiplication by
  `13` on Mathlib's affine elliptic-curve points, and defines a point-level
  `X₀(13)` object as an elliptic curve with a cyclic order-`13` subgroup.  It
  also gives the exact Fricke `j`-map.
- `FreyJInvariant.lean` defines the displayed Frey `j = c₄³/Δ`, the exact
  Fricke-image theorem required from the modular interpretation, and the
  Frey-specific global exclusion required under `29 ∣ B+3`.
- `GaloisRepresentation.lean` defines abstract two-dimensional mod-`13`
  representations, Borel containment through an invariant line, and proves
  that the two missing `X₀(13)` inputs imply the stated Frey irreducibility
  target.
- `BlockerDoc.lean` packages the proved numerical layer and records the
  remaining mathematical boundary.

## Point-level moduli versus the modular curve

The pinned Mathlib revision has elliptic curves and their affine point
groups, so the subgroup `C ≤ E(K)[13]` is concrete.  It has no modular-curve
or subgroup-scheme API.  A subgroup of rational points is not a substitute
for a Galois-stable geometric subgroup scheme.  The `X0_13_ModuliCurve`
certificate is therefore left uninhabited.

The equalities saying the displayed genus is `0` and the cusp count is `2`
remain valid numerical theorems.  They do not construct the modular curve,
and genus zero does not imply that its rational points are only the two
cusps.  The Fricke parameter describes infinitely many rational points.

## Representation and global boundary

An abstract representation `G → GL₂(𝔽₁₃)` is available through Mathlib's
general representation theory.  The library defines Borel containment as
preservation of a nonzero proper submodule of `𝔽₁₃²`.  What is still missing
is the canonical absolute-Galois action on the Frey curve's geometric
`13`-torsion and the theorem identifying reducibility with the Fricke image.

Finally, `48 < 2184` compares two proved numerals; it does not identify either
number with the Frey image.  The local `29`-adic alternatives for a Fricke
parameter also do not exclude every rational parameter.  The global
gap-3-compatible exclusion remains a separate, uninhabited proposition.