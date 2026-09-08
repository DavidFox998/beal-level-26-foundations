# v8.19.0 RibetMazur genus of X₀(2) over ℚ; BealAArm split

`lean/BealLevel26Foundations/Beal/FullProof/X0_2_Genus.lean`
and `RibetMazur.lean`

Classical counts `μ=3`, `ν₂=1`, `ν₃=0`, `ν∞=2`
give `genus_X0_2_rat = 1 + 3/12 − 1/4 − 0 − 1 = 0`
over `ℚ`.  That is **not** a Mathlib
`ModularForm` space.  `ℕ` division would
send `3/12` and `1/4` to `0` and is not
this formula.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`¬ ExistsNewformLevel2` is already
`notExistsNewformLevel2`.  The genus
identity does **not** inhabit a level-2
newform and does **not** drop
`ModularImpliesLevel2Newform`.

`BealAArm.of_pos` splits a positive
`4,13,13` base (`pow2` / `odd_ge3` /
`even_not_pow2`).  Odd `A ≥ 3` is not
Mixed.  The mixed-pow2 → newform arrow
and the unconditional upside-down `∀`
stay uninhabited.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `genus_X0_2_rat_eq_zero` | `ℚ` identity |
| `s2_gamma0_2_dim_and_genus` | recorded dim `0` and genus `0` |
| `ExistsNewformLevel2_eq_zero_ne_zero` | lock: still `0 ≠ 0` |
| `not_ExistsNewformLevel2` | already inhabited via `rfl` |
| `BealAArm.of_pos` | splits positive `A` |
| `beal_odd_A_ge3_not_mixed` | inhabited for `4,13,13` |
| `beal_mixed_pow2_implies_level_2_newform` | uninhabited |
| `beal_from_ribet_upside_down` | uninhabited |
| `TWAuxEllFixedExists_all_N_le_10000` | v8.18.0 product transport |
| `of5_26_gt` / `of7_26_gt` / `of13_26_gt` | `(31,101)` / `(29,197)` / `(53,677)` |
| `InTWEll1000_complete` | uninhabited; not `∀` primes `≤ 1000` |
| `TWAuxEllFixed_inhabited_for_every_ell_le_1000` | uninhabited Prime-quantified Prop |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
