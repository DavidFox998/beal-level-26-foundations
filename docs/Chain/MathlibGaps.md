# v4.56.0 Mathlib gaps

`lean/BealLevel26Foundations/Chain/MathlibGaps.lean`

This pin is Lean 4.12.0 + Mathlib v4.12.0.
The file tracks `#check` / `#print axioms` for five gaps
and the conditional Beal `∀` ceiling.

| Gap | Status |
|---|---|
| Tate conductor `2 * 13` | `frey_conductor_26_of_Is13Case` uninhabited; `frey_conductor_26_rfl` **none** is the label |
| Modularity | `WeierstrassModularity_of_pack` **propext** + existing `frey_modular_13`; not BCDT |
| Ribet `26 → 2` | `ribet_produces_newform_level2` uninhabited |
| `S₂(Γ₀(2))` dim `0` | `notExistsNewformLevel2` **none** DONE |
| `X₀(26)(ℚ)` | empty inductive scaffold; real curve has `26a1` / `26b1` |

Ceiling:
`is13Case_false_implies_Beal_of_tate_ribet_disc_propext_only`
is **propext only**.  It does not inhabit unconditional
`Is13Case → False` and does not inhabit Beal `∀`
unconditionally.  No `False.elim`.

Still not `∀ A B C`.
