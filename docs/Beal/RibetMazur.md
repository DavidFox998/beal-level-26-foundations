# v8.13.0 RibetMazur mixed case + TWAuxEllFixed

`lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean`

A power-of-2 base plus two exponents with a prime
factor `ℓ ≥ 5` makes every odd `q | ABC` Mazur-eligible
(`13 | v_q(Δ)` in the displayed `4,13,13` case).
TW primes are relative to a conductor `N` via
`N < Qᵢ`.  Does **not** import `X0_26_Model`.
Does **not** inhabit `ExistsNewformLevel2` (`0 ≠ 0`).

| Name | Status |
|---|---|
| `FreyEllCase5Mixed` | `FreyEllCase5 ∨ FermatFourCase ∨ MixedPow2Case` |
| `mixed_covers_4_13_13` | `m=4,n=13,p=13` when `A=2^e` |
| `thirteen_dvd_Delta_of_mixed_pow2_A` | every odd `q` has `13 \| v_q(Δ)` in that case |
| `beal_pow2_base` | `rad(2^e) = 1` or `2` |
| `TWAuxEllFixed ℓ N` | `N < Qᵢ` implies `Qᵢ ∤ N`; not `∀ N` |
| `TWAuxEll.of5` / `of7` / `of13_26` | explicit pairs `11/101`, `29/197`, `53/677` |
| `exists_prime_one_mod_ell_listed` | `Q₁` for nine small `ℓ` only, not `∀ ℓ ≤ 1000` |
| `ribet_iterated_ell_mixed` | packed mixed iteration; not a newform |
| `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
