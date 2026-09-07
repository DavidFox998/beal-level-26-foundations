# v8.7.0 RibetMazur q-expansions + Mazur-step pack

`lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean`

Explicit 101-coeff `q_expansion_26a1` / `26b1` as
`List ℚ` from the LMFDB ledger, plus a Mazur/Ribet
*step* pack at odd `q | ABC`.
`ribet_iterated` iterates that pack and `N / ∏q = 2`.
`ribet_iterated_arrow` and `beal_from_ribet` stay
**from** `ModularImpliesLevel2Newform`.
This file does **not** inhabit `ExistsNewformLevel2`
(`0 ≠ 0`) and does **not** prove `¬ PositiveBealTriple`.
Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `q_expansion_26a1` / `26b1` | length 101; `a₁=1`; `a₃=1` / `-3` |
| `mazur_principle_step` | Tate Steinberg label + displayed `T₃,T₅,T₇` |
| `ribet_iterated` | pack with `N/∏q=2`, not `0 ≠ 0` |
| `ribet_iterated_arrow` | equal to `ModularImpliesLevel2Newform` |
| `beal_from_ribet` | equal to `beal_positive_bases` (conditional) |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
