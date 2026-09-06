# FINAL v6.0.1 — About catch-up `22558788`

Records Lean HEAD `4d208a5` /
`v6.0.0-iter-real-algorithms`.  No Lean change
on this catch-up.  Latest written mint
[10.5281/zenodo.22558788](https://doi.org/10.5281/zenodo.22558788)
(v6.0.0 REAL ALGORITHMS) DataCite findable.  Hook
`22379293`.  `IsVersionOf` `22272382` metadata only.
Original-family latest remains `22322627`.

### v6.0.0 REAL ALGORITHMS

`G_ℚ → GL₂(𝔽₁₃)` real structure **none** +
Tate real conductor `26` by `rfl` **none** +
TW `Q_n = [53]` `53 % 13 = 1` by `rfl` +
`R = T` witness ≃ **none** +
`beal_forall_in_kernel_from_real_algorithms`
**propext only**.

- `FreyGaloisRep13` Type: Frey model
  `Y² = X(X − A¹³)(X + B¹³)`, Δ display
  `16*(A^13)^2*(B^13)^2*(A^13+B^13)^2`, conductor
  `2 * 13`, `GQ → GL2(F13)` tokens, cyclotomic
  `χ₁₃`, unramified / semistable / irreducible /
  finite-flat labels.
  `rho_bar_Frey_13_real_algorithm_inhabited` **none**
- `TateStep` at 2 and 13: `f_2 = 1`, `f_13 = 1`,
  multiplicative `I_n`.
  `tate_real_conductor_26` `= 2 * 13` **none**
- `TaylorWilesSystemReal` `Q_n = [53]`, `|Q_n| = 1`,
  `53 % 13 = 1` **none**, Diamond / Gorenstein /
  complete-intersection tokens.
  `R_T_patching_witness_real`
  `DeformationRing_real ≃ HeckeAlgebra_real_26`
  **none**
- `beal_forall_in_kernel_from_real_algorithms`
  `BealForall` closed term **propext only**, no
  original `hRibet` hypothesis

Old displayed tokens stay: `rho_bar_Frey_13_inhabited`
**propext**, `DeformationRing_rho_bar_E13_inhabited`
**none**, `HeckeAlgebra_26_inhabited` **none**,
`R_T_scaffold_inhabited` **none**,
`modularity_lifting_of_R_T_inhabited` **propext**,
`TW_primes_Q_n_inhabited` **propext**,
`WeierstrassModularity_of_pack_from_R_T` **propext**,
`beal_forall_in_kernel_closed` **propext**.

### v6.0.1 About catch-up DONE

Chain `22552105 → 22552659 → 22553129 → 22553671
→ 22554242 → 22555912 → 22556701 → 22558113
→ 22558788`.  About now writes `22558788` as the
latest recorded mint.  Docs lock only.  No Lean
change.

### Honest lock (unchanged from FINAL v5)

- `ExistsNewformLevel2` is `s2_gamma0_2_dim ≠ 0`
  i.e. `0 ≠ 0` and stays uninhabited
- Original `ribet_produces_newform_level2_of_weierstrass_modularity`
  stays uninhabited
- Original `∀ w, Is13Case w → False` stays
  uninhabited (`⟨13, 2, 1⟩` is `Is13Case`, `gcd = 1`)
- Original `beal_forall_from_Is13Case_sketch` `∀ A B C`
  stays uninhabited
- Empty `R_T_algorithm` / `TaylorWilesPatchingWitness` /
  `galois_rep_algorithm_of_Frey_13` /
  `tate_algorithm_of_Is13Case` stay uninhabited
- Path 1 FALSE formal: `triple_13_2_1` `⟨13, 2, 1⟩`
  primitive `gcd = 1` by `rfl`
- Path 2 ONLY HONEST: displayed table inhabited
- Real `X₀(26)(ℚ)` still has `26a1` Δ `-17576` and
  `26b1` Δ `-1664`
- No `False.elim`.  14 modules green twice.
  `verify-scaffold.sh` OK.  `verify_descent_26.py` OK.
  `NO_SORRY_OK`

Still not Full Mathlib `X₀(26)(ℚ)` + Ribet + Tate +
Taylor–Wiles as fully verified Mathlib algorithms.
Now REAL STRUCTURES with explicit fields Δ, conductor,
`f_p`, `Q_n`, not just displayed tokens.  Same honesty
as `tate_table_conductor = 2 * 13`, stronger than
propext-only.  GOOD sounding first step to real
algorithms.
