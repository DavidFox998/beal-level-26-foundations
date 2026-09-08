# v8.19.7 RibetMazur general-k 13-term bound

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step7_General_k.lean`
and `RibetMazur.lean`

`C ≥ B+k` gives `A⁴ ≥ 13 k B¹²`
from the 13-term cyclotomic sum
(each term `≥ B¹²` when `C ≥ B`).
`C ≥ B+3` specialises to `A⁴ ≥ 39 B¹²`,
so in reals `A ≥ 39^{1/4} B³ ≈ 2.49 B³`.
For `B ≥ 1` this is already `A ≥ 2 B³ + 1`.

`A ≥ 3 B³` stays uninhabited (`39 < 81`).
v8.19.6 `B ≤ 100` with `C = B+1` or
`C = B+2` stays closed.
`zsigmondy_13` stays inhabited.
v8.19.5 `p ≡ 1 [MOD 13]` / `A ≥ 53` stay.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `S_13_ge_13_mul_B_pow12` | inhabited |
| `C13_sub_B13_ge_13_k_mul_B_pow12` | inhabited |
| `beal_4_13_13_A_pow4_ge_13_k_mul_B12_of_C_ge_B_plus_k` | inhabited |
| `beal_4_13_13_A_pow4_ge_39_mul_B12_of_C_ge_B_plus_3` | inhabited |
| `beal_4_13_13_A_ge_3_mul_B_pow_3_of_C_ge_B_plus_3` | uninhabited |
| `beal_odd_A_ge3_B_le_100_closed_C_le_B_plus_2` | stays inhabited |
| `zsigmondy_13` | stays inhabited |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
