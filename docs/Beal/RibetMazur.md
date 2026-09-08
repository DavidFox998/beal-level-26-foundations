# v8.16.0 RibetMazur finite Q₁ and Q₂ tables for residuals in [5, 1000]

`lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean`,
`TWPrimesPratt.lean`, and `RibetMazur.lean`

166-row tables `InTWEll1000` of primes
`Q₁ ≡ 1 [MOD ℓ]` (`Q₁ ≤ 20000`) and
`Q₂ ≡ 1 [MOD ℓ²]` (`Q₂ ≤ 10⁸`).
Not Dirichlet.  Not `Nat.Prime ℓ → 5 ≤ ℓ ≤ 1000`.
Not `∀ N ≤ 10000`.  Does **not** import
`X0_26_Model`.  Does **not** inhabit
`ExistsNewformLevel2` (`0 ≠ 0`).

| Name | Status |
|---|---|
| `InTWEll1000` / `exists_prime_one_mod_ell_all` | `Q₁` table membership |
| `exists_prime_one_mod_ell_sq_all` | `Q₂` table, bound `10⁸`, via Pratt |
| `prime_of_pratt` | order `n−1` in `(ℤ/nℤ)ˣ` |
| `q2_witness_919` | `59119271 % 844561 = 1` |
| `Q1_not_dvd_N_of_Q1_gt_N` | `0 < N < Q₁` implies `Q₁ ∤ N` |
| `TWAuxEllFixed.of5_26` / `of7_26` / `of13_26` | explicit `N < Qᵢ` |
| `find_next_prime_one_mod_gt_exists` | uninhabited; not `∀ N ≤ 10000` |
| `TWAuxEllFixed_inhabited_for_every_ell_le_1000` | uninhabited Prop |
| `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
