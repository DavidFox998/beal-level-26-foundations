# v8.17.0 RibetMazur TWAuxEllFixed at N=26 and N=10000

`lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed.lean`,
`TWAuxEllFixedCore.lean`, `TWPrimes.lean`, and `RibetMazur.lean`

`TWAuxEllFixed ℓ N` is inhabited at
`N = 26` and `N = 10000` for every
residual in `InTWEll1000`.  `Qᵢ > N`
implies `Qᵢ ∤ N`.  Not Dirichlet.
Not `∀ N ≤ 10000`.  Completeness
`Nat.Prime ℓ → 5 ≤ ℓ ≤ 1000` is
kernel-checked only on `[5, 100]`
via `Finset.filter`.  `ℓ = 941`
needs `Q₁ = 30113` (`N + 21000`).
Does **not** import `X0_26_Model`.
Does **not** inhabit
`ExistsNewformLevel2` (`0 ≠ 0`).

| Name | Status |
|---|---|
| `TWAuxEllFixedExists_26_all` | inhabited on `InTWEll1000` |
| `TWAuxEllFixedExists_10000_all` | inhabited on `InTWEll1000` |
| `of5_26_gt` / `of7_26_gt` / `of13_26_gt` | `(31,101)` / `(29,197)` / `(53,677)` |
| `of5_10000` / `of7_10000` / `of13_10000` | `Q₁ > 10000` |
| `next_Q1_gt_N` | search token; window `N + 21000` |
| `primes_le_1000` / `InTWEll1000_iff_mem` | Finset union of the ten tables |
| `InTWEll1000_of_prime_5_100` | completeness on `[5, 100]` |
| `InTWEll1000_complete` | uninhabited; not `∀` primes `≤ 1000` |
| `TWAuxEllFixed_inhabited_for_every_ell_le_1000` | uninhabited Prop |
| `exists_prime_one_mod_ell_sq_all` | v8.16.0 `Q₂` table, bound `10⁸` |
| `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
