# v8.11.0 RibetMazur Frey-ℓ case

`lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean`

Each exponent of a primitive Beal triple may carry a
prime factor `ℓ ≥ 5`.  At an odd prime `q | ABC` the
matching residual then divides `v_q(Δ)`, so the Mazur
gate is no longer locked to `13`.  Does **not** import
`X0_26_Model`.  Does **not** inhabit
`ExistsNewformLevel2` (`0 ≠ 0`) and does **not** prove
`¬ PositiveBealTriple`.

| Name | Status |
|---|---|
| `FreyEllCase5` / `FreyEllWitness` | each of `m,n,p` has a prime factor `ℓ ≥ 5`; fails for `m = 4` |
| `ell_of_q` | `ℓ_m` if `q \| A`, `ℓ_n` if `q \| B`, else `ℓ_p` |
| `ell_of_q_dvd_vqDelta` | `ℓ(q) \| v_q(Δ)` from `v_q(Δ) = 2m v_q(A)` (or `n`/`p`) |
| `frey_a_q_real_ell` | same Tate sign `(-c₆/q)=±1` as v8.10 |
| `frey_rho_unramified_iff_ell_dvd_vqDelta` | packed Tate criterion at residual `ℓ` |
| `trace_eq_pm_qplus1_when_unramified` | packed traces `±(q+1)`, not `a_q = ±1` |
| `HeckeAction_N_real_ell` | double-coset token at residual `ℓ` |
| `TWAuxEll.of13` | `53 ≡ 1 [MOD 13]`, `677 ≡ 1 [MOD 169]`; not Dirichlet for general `ℓ` |
| `mazur_step_ell` | requires `ℓ \| v_q(Δ)`; not Mathlib modularity at `N/q` |
| `ribet_iterated_ell_case` | every odd `q` under `FreyEllCase5`; arithmetic `N / ∏q = 2` |
| `beal_from_ribet_ell_case` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
