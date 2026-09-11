# v8.79.0 Beal Frey cubic distinguished from displayed cubic

`lean/BealLevel26Foundations/Beal/FullProof/BealFreyB14.lean`

The *Beal Frey cubic* is the integer polynomial
`x * (x - A^4) * (x + B^4)` with roots
`0`, `A^4`, `-B^4`.
The *displayed cubic* already in
`LevelLoweringB14` is
`x * (x - B^4) * (x + (B+3)^4)` with roots
`0`, `B^4`, `-(B+3)^4`.
Those are different cubics
(`displayed_cubic_ne_beal_frey_example`).

Inhabited:
* `beal_frey_has_full_2_torsion` — three
  integer roots.  Axiom `propext`.
* `beal_frey_rewrite` — under
  `A^4 + B^4 = (B+3)^13` the last factor
  is `x - A^4 + (B+3)^13`.  Axiom `propext`.
* `displayed_cubic_ne_beal_frey_example` —
  empty axioms.
* `beal_4_13_13_gap3_B_le_2M_eliminated_full_honest`
  — the two-element `[196, 1500003]` kill
  via mod 16.  Empty axioms.

Uninhabited Props:
* `beal_frey_modular` — not BCDT, not
  `Classical.em`, not Wiles.
* `beal_frey_mod13_irreducible_B14` —
  recorded `a53 ∈ {-2,-10,1,6,14}` values
  are Euler counts of the *displayed*
  cubic and do not migrate.
* `level_lowering_to_26_B14_honest` —
  the Ribet–Mazur pack is a miss pair,
  not a congruence.  The Zsig pool does
  not prove `N | 26`.
* `beal_4_13_13_gap3_B_le_2M_eliminated_B14_honest`
  — `∀ B ∈ step60_b14_list, ¬∃ A`.
* `beal_4_13_13_gap3_B_le_2M_eliminated_5983_honest`
  — conjunction of the 2-element kill
  with the 352-row Prop.  The 5983
  identity remains `zsig_density_2M_stats`.

Not Mathlib `EllipticCurve`.
Does not import `RibetMazur`.
Does not import `frey_modular_13`.
Chain `ExistsNewformLevel2` stays `0 != 0`.
