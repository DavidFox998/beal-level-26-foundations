# v4.18.0 Typed ∧ Forall Lock — Axiom-Free Cert (c9ab61b → 5be16b3)

Package lock for `BealExponent13_Iter_Package`. Both conjuncts of
`typed_and_forall` / `certified_typed_and_forall` are
`BealTheorem_Exponent13_Typed` via axiom-free
`hGeomForbid_typed_true` (`hNotIn hInList`). This is **not**
`∀ N` and **not** a Mathlib `X₀(26)(ℚ)` theorem.

- `typed_and_forall` ⟨beal_exponent13_from_ribet, beal_forall_from_ribet⟩ — none
- `certified_typed_and_forall` ⟨certified_from_forall, beal_forall_certified_from_ribet⟩ — none
- `beal_forall_from_ribet` = `Contradiction.beal_exponent13_from_ribet` -- BRIDGE none via hGeomForbid
- `X0_26_Q = {P | P.label ∈ fourCuspsList}` `rfl` `[1,2,13,26]` `P.mem`, Frey `2*13=26` `rfl`, `certs/pari_x0_26_four_cusps.json` 26a1 `[1,0,1,-5,-8]` `-17576` 26b1 `[1,-1,1,-3,3]` `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`, image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB

## Axiom table

| Theorem | Axioms |
|---|---|
| typed_and_forall | none ⟨beal_exponent13_from_ribet, beal_forall_from_ribet⟩ |
| certified_typed_and_forall | none ⟨certified_from_forall, beal_forall_certified_from_ribet⟩ |
| beal_forall_from_ribet / beal_forall_certified_from_ribet / certified_from_forall | none |
| beal_exponent13_from_ribet / certified_from_ribet | none (hGeomForbid_typed_true via hNotIn hInList) |
| contradiction_from_ribet | ribet_level_lowering_26 only |
| BealExponent13_Contradiction.certified | frey_modular_13 + ribet_level_lowering_26 |

Still not forall N and not Mathlib X0(26)(Q). The only axioms
are `frey_modular_13` and `ribet_level_lowering_26`
(COMPUTATIONAL ASSUMPTION), secured by
`certs/pari_x0_26_four_cusps.json`. No `sorry`. No `False.elim`.
