# v8.10.0 RibetMazur Frey a_q=±1 + 13|v_q(Δ) + ModSym token

`lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean`

Tate split/nonsplit sign `(-c₆/q) = ±1` at odd primes
of multiplicative reduction, the residual-unramified
criterion `13 ∣ v_q(Δ)`, and a packed `ModSym(Γ₀(N),2)`
token with double-coset `T_q`.  Does **not** import
`X0_26_Model`.  Does **not** inhabit
`ExistsNewformLevel2` (`0 ≠ 0`) and does **not** prove
`¬ PositiveBealTriple`.

| Name | Status |
|---|---|
| `frey_a_q_real` / `frey_a_q_is_pm1` | `(-c₆/q)=±1` because `q ∤ c₆`; not a Frey newform coefficient |
| `pm1_ne_pm_qplus1_mod13_at_3` | `1,12 ≠ 4,9` in `ZMod 13` by `decide` |
| `frey_rho_unramified_iff_13_dvd_vqDelta` | definitional iff with `UnramifiedAt13` |
| `J0_N_real` / `ModSym` | packed weight-2 `Γ₀(N)` token; cusps `[0],[∞]` |
| `HeckeAction_N_real` | double-coset token at `N·q`; TW at `N·53`/`N·677` |
| `mazur_step_real_fixed` | requires `13 ∣ v_q(Δ)`; not Mathlib modularity at `N/q` |
| `ribet_iterated_real_fixed` | iterates only those primes; quotient is **not** `2` unless `Frey13Case` |
| `N_div_Prod_eq_2_of_Frey13Case` | `N / ∏q = 2` under `Frey13Case` |
| `beal_from_ribet_real_fixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
