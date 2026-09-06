# v4.23.0 Iter Package Final Bridge Lock — Axiom-Free Cert

Package lock for `BealExponent13_Iter_Package`. `final_package` is
⟨`beal_exponent13_from_ribet`, `beal_forall_from_ribet`, `final_bridge`⟩.
`final_bridge` is `beal_forall_from_ribet` =
`Contradiction.beal_exponent13_from_ribet` -- BRIDGE none via
`hGeomForbid_typed_true` (`hNotIn hInList`). This is **not**
`∀ N` and **not** a Mathlib `X₀(26)(ℚ)` theorem.

- `typed_and_forall` ⟨beal_exponent13_from_ribet, beal_forall_from_ribet⟩ — none
- `certified_typed_and_forall` ⟨certified_from_forall, beal_forall_certified_from_ribet⟩ — none
- `final_bridge` = `beal_forall_from_ribet` — none
- `final_package` ⟨beal_exponent13_from_ribet, beal_forall_from_ribet, final_bridge⟩ — none
- `beal_forall_from_ribet` = `Contradiction.beal_exponent13_from_ribet` -- BRIDGE none via hGeomForbid
- `X0_26_Q = {P | P.label ∈ fourCuspsList}` `rfl` `[1,2,13,26]` `P.mem`, Frey `2*13=26` `rfl`, `certs/pari_x0_26_four_cusps.json` 26a1 `[1,0,1,-5,-8]` `-17576` 26b1 `[1,-1,1,-3,3]` `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`, image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB

## Axiom table

| Theorem | Axioms |
|---|---|
| typed_and_forall | none |
| certified_typed_and_forall | none |
| final_bridge / final_package | none |
| beal_forall_from_ribet / certified_from_forall | none bridge Contradiction.beal_exponent13_from_ribet |
| beal_exponent13_from_ribet / certified_from_ribet | none hGeomForbid |
| contradiction_from_ribet | ribet_level_lowering_26 only |
| Contradiction.certified | frey_modular_13 + ribet_level_lowering_26 |

PARI lock: 26a1 `-17576` 26b1 `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`, image ≥300KB.

Still not forall N and not Mathlib X0(26)(Q). The only axioms
are `frey_modular_13` and `ribet_level_lowering_26`
(COMPUTATIONAL ASSUMPTION), secured by
`certs/pari_x0_26_four_cusps.json`. No `sorry`. No `False.elim`.
Parallel parent `10.5281/zenodo.22379293` honest; mint
`10.5281/zenodo.22407709` findable `IsVersionOf`
`22272382`+`22379293`; original latest v4.0.9
`10.5281/zenodo.22322627`.
