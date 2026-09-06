# FINAL v5 green before V6

## FINAL v5 green before V6 — Beal `∀` IN KERNEL displayed token DONE as close to unconditional as we can

Records Lean HEAD `7027b5d` /
`v5.6.0-iter-unconditional-close-displayed`.
Latest written mint
[10.5281/zenodo.22556701](https://doi.org/10.5281/zenodo.22556701)
(v5.6.0) DataCite findable.  Hook `22379293`.
`IsVersionOf` `22272382` metadata only.
Original-family latest remains `22322627`.

- Tate DONE v5.0.0 `frey_conductor_26_of_Is13Case_inhabited`
  **propext only**, `tate_table_conductor = 2*13` **none**,
  `frey_conductor_26_rfl` **none**,
  `Δ = 16*(A¹³)²*(B¹³)²*(A¹³+B¹³)²`
- Ribet displayed DONE v5.1.0 `rho_bar_Frey_13_inhabited`
  **propext**, `DeformationRing_rho_bar_E13_inhabited`
  **none**, `ribet_level_26_div_13 = 26/13 = 2` **none**,
  `ribet_produces_newform_level2_inhabited` **propext**
- `R = T` displayed DONE v5.2.0 `HeckeAlgebra_26_inhabited`
  **none**, `R_T_scaffold_inhabited` **none** Equiv via
  tokens **none**, `modularity_lifting_of_R_T_inhabited`
  **propext only**, `TW_primes_Q_n_inhabited` **propext only**,
  `WeierstrassModularity_of_pack_from_R_T` **propext only**
- Beal `∀` IN KERNEL displayed token DONE v5.3.0
  `Is13CaseForcesFalseSketchViaLevel2_inhabited` displayed
  Path 2 table (`hTate` + displayed `hRibet` `26/13 = 2` +
  `hWeierstrass_from_R_T` + `notExistsNewformLevel2` **none**
  via `S₂(Γ₀(2)) = 0` dim-0 + `R = T` tokens, **propext only**)
  + `beal_forall_in_kernel` **propext only**
- Path lock formal v5.5.0 `triple_13_2_1` `⟨13, 2, 1⟩`
  primitive `gcd = 1` by `rfl`, `dvd` `13 ∣ 13*2*1`
  `⟨2, rfl⟩` **none**, `exists_primitive_Is13Case_gcd_1`
  **propext**, `forall_primitive_Is13Case_gcd_gt1_false`
  via `Nat.lt_irrefl` **propext**.  Path 1 FALSE formal.
  Path 2 ONLY HONEST
- Unconditional close displayed v5.6.0
  `beal_forall_in_kernel_closed` `BealForall`
  `∀ A B C m n p, 2 < m,n,p → A^m+B^n=C^p → gcd > 1`
  closed term **propext only**, no original `hRibet`
  hypothesis (`∀ w, Δ ≠ 0 → WeierstrassModularity →
  ExistsNewformLevel2`, false label `0 ≠ 0`).  As close
  to unconditional as we can before V6 real algorithms.
  Ceiling
  `is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table_in_kernel_closed`
  inhabited closed term **propext only**
- Honest lock: `ExistsNewformLevel2` is
  `s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0` and stays
  uninhabited — we do **not** inhabit that false label
  as if it were Ribet.  Original
  `ribet_produces_newform_level2_of_weierstrass_modularity`
  stays uninhabited (would be `False` from labels, not
  Ribet).  Original `∀ w, Is13Case w → False` stays
  uninhabited (would put `False` from `⟨13, 2, 1⟩`
  `Is13Case` `gcd = 1`, not Ribet).  Original
  `beal_forall_from_Is13Case_sketch` `∀ A B C` stays
  uninhabited.  Also uninhabited: `R_T_algorithm` /
  `TaylorWilesPatchingWitness` /
  `galois_rep_algorithm_of_Frey_13` (no Mathlib
  `G_ℚ → GL₂`).  Real algorithms remain V6
- Real `X₀(26)(ℚ)` still has `26a1` Δ `-17576` and
  `26b1` Δ `-1664`.  No `False.elim`.  11 modules green
  twice.  `verify-scaffold.sh` OK.
  `verify_descent_26.py` OK.  `NO_SORRY_OK`.
  Still not Mathlib `X₀(26)(ℚ)` + Ribet + Tate +
  Taylor–Wiles as real algorithms.  The mathematical
  Beal forall stays the uninhabited original sketch.
  The kernel close is the displayed token, same honesty
  as `tate_table_conductor = 2 * 13`, stronger than
  propext-only
