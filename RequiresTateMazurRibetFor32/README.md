# Why the level-32 construction remains conditional

`Doc.lean` records the exact boundary between the integrated numerical
formalization and an unconditional level-`32` newform theorem.  The repository
proves the displayed discriminant, valuation, divisibility, group-order, and
level arithmetic.  It does not turn those numerals into the missing geometric,
local, modular, or analytic objects.

## Required foundations

An unconditional construction still requires:

1. Wiles/BCDT modularity specialized to the displayed Frey curve;
2. the curve's geometric mod-`13` Galois representation and absolute
   irreducibility through a complete Mazur/`X₀(13)` argument;
3. Tate uniformization, Tate's algorithm, the Néron model and conductor,
   cyclotomic inertia, and the required mod-`13` unramifiedness;
4. genuine Ribet level lowering from conductor `928` to level `32`;
5. identification of the resulting newform with `32a1`; and
6. a complete Kraus analysis of all bad-reduction residue classes.

The analytic rank-zero route is separate.  Displayed values `L/Ω = 1/3` and
`1/7` and displayed `Sel₂_card = 1` do not replace any item above.  To become
formal rank-zero proofs they would themselves require curve-attached
`L`-functions and periods, Kato–Kolyvagin theorems, Mordell–Weil finite
generation, Selmer exact sequences, and concrete `Fintype` witnesses.

The distinction `¬ Subsingleton E(ℚ)` versus
`Nonempty (Fintype E(ℚ))` is essential: finite Mordell–Weil groups may contain
nonzero torsion.  This documentation therefore reports the current formal
status without treating a numerical display as an inhabitant of a stronger
proposition.