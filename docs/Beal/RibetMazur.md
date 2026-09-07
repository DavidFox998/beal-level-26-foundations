# v8.12.0 RibetMazur Fermat n=4 + TW search at ℓ

`lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean`

Mathlib `fermatLastTheoremFour` closes a primitive
Beal triple whose exponents are all powers of 2 at
least `4`.  TW auxiliary primes are a search token
`Q₁ ≡ 1 [MOD ℓ]`, `Q₂ ≡ 1 [MOD ℓ²]`.  Does **not**
import `X0_26_Model`.  Does **not** inhabit
`ExistsNewformLevel2` (`0 ≠ 0`) and does **not**
prove `¬ PositiveBealTriple` in general.

| Name | Status |
|---|---|
| `fermat_four_lemma` | Mathlib `fermatLastTheoremFour` as `¬ ∃ A,B,C > 0, A⁴+B⁴=C⁴` |
| `FermatFourCase` / `beal_pow2_exponents` | all three exponents `2^e`, `e ≥ 2`; Beal holds by FLT4 |
| `not_FreyEllCase5_of_exp_four_reduced` | `m=4` and `n,p` powers of 2; `m=4` alone is not FLT4 |
| `FreyEllCase5Complete` | `FreyEllCase5 ∨ FermatFourCase`; not a cover (`4,13,13`) |
| `find_prime_congruent_one_mod` | computable search; may return `none` |
| `TWAuxEll` / `TWAuxEll_of_ell` | `Q₁ ≡ 1 [MOD ℓ]`, `Q₂ ≡ 1 [MOD ℓ²]`; `∀ N, ¬ Q₁ ∣ N` is false |
| `HeckeAction_N_real_ell_upgraded` | double-coset token plus `N·Q₁(ℓ)` / `N·Q₂(ℓ)` |
| `mazur_step_real_ell_upgraded` | requires `ℓ \| v_q(Δ)` and a `TWAuxEll` witness |
| `ribet_iterated_ell_upgraded` | `FreyEllCase5` pack; FLT4 branch is separate |
| `beal_from_ribet_ell_upgraded` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
