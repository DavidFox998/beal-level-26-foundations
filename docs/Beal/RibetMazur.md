# v8.19.8 RibetMazur k odd / coprime / A⁴ ≡ k¹³ mod B

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step8_k_odd_coprime.lean`
and `RibetMazur.lean`

Odd `A` forces `k = C−B` odd.
`Coprime C B` and `C ≥ B` give
`Coprime k B`.  `Coprime C B` plus
the equation give `Coprime A B`.
`A⁴ ≡ k¹³ [MOD B]`.

Without `C ≥ B`, `gcd(C−B, B) = 1`
is false (`C = 1`, `B = 2`).
v8.19.7 `A⁴ ≥ 13 k B¹²` / `39 B¹²` stay.
v8.19.6 `B ≤ 100` with `C = B+1` or
`C = B+2` stays closed.
`zsigmondy_13` stays inhabited.

`ExistsNewformLevel2` stays
`s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.

Does **not** import `X0_26_Model`.

| Name | Status |
|---|---|
| `beal_4_13_13_k_odd` | inhabited |
| `beal_4_13_13_gcd_k_B_eq_one` | inhabited with `C ≥ B` |
| `beal_4_13_13_gcd_A_B_eq_one` | inhabited |
| `beal_4_13_13_A_pow4_mod_B_eq_k_pow13` | inhabited |
| `beal_4_13_13_gcd_k_B_eq_one_of_coprime_only` | uninhabited |
| `beal_4_13_13_A_pow4_ge_39_mul_B12_of_C_ge_B_plus_3` | stays inhabited |
| `zsigmondy_13` | stays inhabited |
| `beal_from_ribet` / `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
