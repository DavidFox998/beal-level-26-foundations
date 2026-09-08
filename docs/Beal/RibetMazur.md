# v8.15.0 RibetMazur finite Q₁ table for residuals in [5, 1000]

`lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean`
and `RibetMazur.lean`

166-row table `InTWEll1000` of primes
`Q₁ ≡ 1 [MOD ℓ]` with `Q₁ ≤ 20000`.
Not Dirichlet.  Not `Nat.Prime ℓ → 5 ≤ ℓ ≤ 1000`.
Not `∀ N ≤ 10000`.  `Q₂ ≡ 1 [MOD ℓ²]` within
`5·10⁶` fails for 56 residuals.  Does **not**
import `X0_26_Model`.  Does **not** inhabit
`ExistsNewformLevel2` (`0 ≠ 0`).

| Name | Status |
|---|---|
| `InTWEll1000` / `exists_prime_one_mod_ell_all` | table membership, not Dirichlet |
| `Q1_not_dvd_N_of_Q1_gt_N` | `0 < N < Q₁` implies `Q₁ ∤ N` |
| `TWAuxEllFixed.of5_26` / `of7_26` / `of13_26` | explicit `N < Qᵢ` |
| `exists_prime_one_mod_ell_sq_all` | uninhabited; 56 miss `5·10⁶` |
| `find_next_prime_one_mod_gt_exists` | uninhabited; not `∀ N ≤ 10000` |
| `TWAuxEllFixed_inhabited_for_every_ell_le_1000` | uninhabited Prop |
| `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

Odd-`A` residues from v8.14.0 stay as before.

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
