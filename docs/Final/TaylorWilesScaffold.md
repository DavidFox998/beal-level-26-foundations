# v4.58.0 Taylor–Wiles scaffold

This pin is Lean 4.12.0 + Mathlib v4.12.0.  Tracks what
Mathlib lacks for Wiles / Taylor–Wiles `R = T`.

`WeierstrassModularity c` is
`∃ w, c = pack w ∧ Modularity (FreyCurve13 w)`.
Valid type.  `WeierstrassModularity_of_pack` is the
existing `frey_modular_13` (**propext** + that assumption).
Not Wiles–Taylor / BCDT.  No new axiom.

Lean: `lean/BealLevel26Foundations/Chain/TaylorWilesScaffold.lean`
(10th module).

| Component | In this repo | Status | Mathlib 4.12 lacks | `#print axioms` |
|---|---|---|---|---|
| `R = T` theorem | `R_T_scaffold` : `Nonempty (DeformationRing ≃ HeckeAlgebra_26)` | uninhabited Prop | deformation rings, `R = T` isomorphism, universal deformation, minimal deformations | uninhabited |
| Hecke algebra | `HeckeAlgebra_26` : Type | scaffold empty Type | Hecke algebra `T_N`, Hecke operators `T_p`, diamond, Gorenstein property, complete intersection | **none** (`HeckeAlgebra_26_eq` `rfl`) |
| Deformation ring | `DeformationRing_rho_bar_E13` | uninhabited Prop | Galois deformation theory, `ρ̄_{E,13} : G_ℚ → GL₂(𝔽₁₃)` irreducible, finite flat at 13, minimal at 2, local deformation conditions | uninhabited |
| Galois rep `ρ̄_{E,13}` | `rho_bar_Frey_13` | uninhabited | residual Galois representation of the Frey curve mod 13, semistable at 2, finite at 13, irreducibility (Mazur), modularity lifting conditions | uninhabited |
| Modular lifting | `modularity_lifting_of_R_T` | uninhabited | Taylor–Wiles patching, Diamond criterion, Wiles numerical criterion, Gorenstein + complete intersection → `R = T` → modularity | uninhabited |
| Taylor–Wiles primes | `TW_primes_Q_n` | uninhabited | Taylor–Wiles auxiliary primes `Q_n`, `\|Q_n\| = r`, `q ≡ 1 [MOD 13^n]`, `ρ̄(Frob_q)` has distinct eigenvalues | uninhabited |
| `frey_modular_13` | `WeierstrassModularity_of_pack` | valid type via existing `frey_modular_13` | BCDT Breuil–Conrad–Diamond–Taylor 2001, modularity of semistable elliptic curves over `ℚ` | **propext** + existing |
| Ceiling | `is13Case_false_implies_Beal_of_tate_ribet_disc_propext_only` | `hTate → hRibet → hWeierstrass → hComp + hΔ → Beal ∀`; builds a *local* `Is13Case → False` (Path 2); does **not** inhabit unconditional `Is13CaseForcesFalseSketchViaLevel2`; no `False.elim` | Needs `R = T` + Ribet + Tate to inhabit unconditional Beal `∀` | **propext only** |

Conditional Beal `∀` propext-only is the ceiling until
Mathlib has `R = T` + Ribet + Tate.  Unconditional Beal
`∀` is still not in the kernel.

`R_T_scaffold` is not inhabited by empty-elim on the two
scaffold Types.  `modularity_lifting_of_R_T` is not
inhabited by `WeierstrassModularity_of_pack`.

Still not `∀ A B C` unconditionally.  Still not Mathlib
`X₀(26)(ℚ)` + Ribet + Tate + Taylor–Wiles.

### v5.0.0 Tate conductor 26 inhabited (displayed table)

Phase 1 displayed Tate table is **DONE**.  We finished the
*label* without Mathlib Tate.

| Component | In this repo | Status | `#print axioms` |
|---|---|---|---|
| Tate table | `tate_table_conductor = 2 * 13`, `tate_f_2 = 1`, `tate_f_13 = 1`, multiplicative at 2 and 13 | inhabited display | **none** |
| `tate_conductor_26_of_Is13Case_proof` | `Is13Case ∧ 0<A ∧ 0<B → Δ ≠ 0 ∧ table = 2*13` | inhabited | **propext** + `Classical.choice` + `Quot.sound` (Δ) |
| `frey_conductor_26_of_Is13Case_inhabited` | original sketch `hTate` | inhabited via table + label | **propext** |
| `tate_algorithm_of_Is13Case` | Kodaira from `v_p(Δ)`, `v_p(c₄)` | uninhabited | uninhabited |
| Ribet / `R = T` / ceiling | unchanged | Ribet and `R = T` uninhabited; ceiling still needs `hRibet` | **propext only** |

Not Mathlib Tate (`∏ p^{f_p}`).  Same honesty as
`s2_gamma0_2_dim = 0`.  `Is13Case` does not imply
`2 ∣ A*B*C`.
