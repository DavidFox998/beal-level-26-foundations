# v8.9.0 RibetMazur packed X0(N)/J0(N) + Frey Steinberg label

`lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean`

Packed modular-curve / Jacobian *tokens* at
`N = rad(ABC)`, plus the Frey Tate Steinberg label.
`X0_N_Model` / `J0_N_Model` are not Mathlib
`X₀(N)` / `J₀(N)` and are not a base change of
the affine `X0_26` model.  `frey_a_q_is_pm1` is
`v_q(c₄)=0 ∧ v_q(Δ)>0`, not a Frey Fourier
coefficient `a_q = ±1`.  Even if that eigenvalue
were `±1`, it is not `±(q+1)` mod 13 at `q = 3`.
`mazur_step_real_fixed` / `ribet_iterated_real_fixed`
give `N / ∏q = 2`.  `beal_from_ribet_real_fixed`
stays **from** `ModularImpliesLevel2Newform`.
This file does **not** inhabit `ExistsNewformLevel2`
(`0 ≠ 0`) and does **not** prove `¬ PositiveBealTriple`.
The displayed `a₃(26a1) = 1` is **not** `±4` mod 13,
so `T_q ≡ ±(q+1)` fails on the level-26 ledger at
`q = 3`.  Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `X0_N_Model` / `J0_N_Model` | level tokens at `N = rad(ABC)`; displayed cusps `[1,2,13,26]` |
| `HeckeAction_N_real` | same `T_q` formula as `HeckeAction_N` (not `End(J₀(N)[13])`) |
| `frey_a_q_is_pm1` | Tate Steinberg label, not Frey `a_q = ±1` |
| `mazur_step_real_fixed` | Frey-side pack + `(N/q)*q=N`, not Mathlib modularity at `N/q` |
| `ribet_iterated_real_fixed` | fold identity `N/∏q=2`, not `0 ≠ 0` |
| `beal_from_ribet_real_fixed` | equal to `beal_from_ribet_real` (conditional) |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
