# v8.18.0 RibetMazur TWAuxEllFixed product for every N≤10000 on the table

`lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed.lean`,
`TWAuxEllFixedCore.lean`, and `RibetMazur.lean`

`TWAuxEllFixed ℓ N` is inhabited for every
`N ≤ 10000` and every residual in
`InTWEll1000`, by transporting the
`N = 10000` witnesses (`Qᵢ > 10000 ≥ N`).
That is a function on the product, not a
1.66M-row `decide` table and not a
materialised `Finset.product`.
Not Dirichlet.  Not `Nat.Prime ℓ → 5 ≤ ℓ ≤ 1000`.
Does **not** import `X0_26_Model`.
Does **not** inhabit
`ExistsNewformLevel2` (`0 ≠ 0`).

| Name | Status |
|---|---|
| `TWAuxEllFixed.of_N_le` | transport `M`-witness to `N ≤ M` |
| `of_ℓ_N_product` / `TWAuxEllFixedExists_all_N_le_10000` | inhabited on `InTWEll1000` |
| `TWAuxEllFixed_inhabited_for_every_ell_le_1000_product` | `∀ ℓ ∈ primes_le_1000, ∀ N ∈ Icc 0 10000` |
| `product_all_mem` | pair predicate; not a 1.66M Finset |
| `find_next_prime_one_mod_gt_exists_product` | `∃ Q₁ > N`; not `Q₁ ≤ N + 21000` |
| `of5_26_gt` / `of7_26_gt` / `of13_26_gt` | `(31,101)` / `(29,197)` / `(53,677)` |
| `InTWEll1000_of_prime_5_100` | completeness on `[5, 100]` |
| `InTWEll1000_complete` | uninhabited; not `∀` primes `≤ 1000` |
| `TWAuxEllFixed_inhabited_for_every_ell_le_1000` | uninhabited Prime-quantified Prop |
| `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
