# Conditional level-32 newform bridge

`Bridge.lean` is the integration point for the proved Frey numerics and three
explicit mathematical assumptions.  It proves the discriminant identity

`Δ = 16 A⁸ B⁸ (A⁴+B⁴)²`,

the local valuation identity `v₂₉(Δ) = 26 v₂₉(B+3)`, the divisibility
`13 ∣ v₂₉(Δ)`, and the level arithmetic `928 / 29 = 32` and
`32 * 29 = 928`.  The theorem
`has_newform_at_level_32_of_assumptions` then takes exactly the named Mazur,
Tate, and Ribet assumptions needed by this conditional interface.

## Dependencies and interaction

- `MazurCurve` supplies the vocabulary for the Frey-specific absence of a
  rational `13`-isogeny.  The calculations `|SL₂(𝔽₁₃)| = 2184` and
  `48 < 2184` do not inhabit that boundary.
- `TateCurve` supplies the local Néron/conductor boundary at `29`; its
  valuation numerics alone do not construct Tate uniformization or inertia.
- `RibetCurve` supplies the `928 → 32` lowering boundary; the quotient
  calculation does not construct a residual eigenform.
- `KolyvaginCurve` is deliberately not a dependency of the bridge.
  `L/Ω = 1/3`, `L/Ω = 1/7`, and displayed `Sel₂_card = 1` concern a separate
  analytic and Mordell–Weil route.

## Formal status

`HasNewformAtLevel32` is a proposition-valued evidence record.  It is not a
Mathlib modular-form object and does not claim an unconditional newform.
Removing its assumptions requires Wiles/BCDT modularity, a geometric
mod-`13` Galois representation with absolute irreducibility, Tate/Néron and
cyclotomic-inertia theory, mod-`13` unramifiedness, genuine Ribet lowering,
identification with `32a1`, and complete Kraus bad-reduction elimination.