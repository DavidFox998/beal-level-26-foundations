# v8.19.6 RibetMazur B≤100 C∈{B+1,B+2} closed

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step6_B_le_100_closed.lean`
and `RibetMazur.lean`

`B ≤ 100` and `C ∈ {B+1, B+2}` closes
for odd `A` by `A ≥ 53`, `A ≥ B³`, and
the decide tables.

`C ≥ B+3` stays open.
`zsigmondy_13` stays inhabited.
v8.19.5 `p ≡ 1 [MOD 13]` / `A ≥ 53` stay.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `beal_odd_A_ge3_B_le_100_closed_C_le_B_plus_2` | inhabited |
| `beal_odd_A_ge3_B_le_100_C_ge_B_plus_3_closed` | uninhabited |
| `zsigmondy_13` | stays inhabited |
| `beal_odd_A_ge3_A_ge_53` | stays inhabited |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
