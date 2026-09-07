# v8.8.0 RibetMazur HeckeAction_N + Mazur-step real pack

`lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean`

Integer ledger prefixes plus a TW `HeckeAction_N`
token and an iterated Mazur *pack*.
`mazur_step_real` / `ribet_iterated_real` give
`N / ∏q = 2`.  `ModularImpliesLevel2Newform_real`
and `beal_from_ribet_real` stay **from**
`ModularImpliesLevel2Newform`.
This file does **not** inhabit `ExistsNewformLevel2`
(`0 ≠ 0`) and does **not** prove `¬ PositiveBealTriple`.
The displayed `a₃(26a1) = 1` is **not** `±4` mod 13,
so `T_q ≡ ±(q+1)` fails on the level-26 ledger at
`q = 3`.  Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `q_expansion_26a1_int` / `26b1_int` | length 101; `a₀=0`; `a₁=1`; `T₃=1`/`-3` |
| `HeckeAction_N` | `T_q` formula + TW `R≃T` at `26·53`/`26·677` |
| `mazur_step_real` | Tate Steinberg + `(N/q)*q=N`, not Mathlib modularity at `N/q` |
| `ribet_iterated_real` | fold identity `N/∏q=2`, not `0 ≠ 0` |
| `ModularImpliesLevel2Newform_real` | equal to `ModularImpliesLevel2Newform` |
| `beal_from_ribet_real` | equal to `beal_from_ribet` (conditional) |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
