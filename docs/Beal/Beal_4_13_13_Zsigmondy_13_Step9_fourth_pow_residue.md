# v8.19.9 Zsigmondy Step 9 — fourth-power residue

`lean/BealLevel26Foundations/Beal_4_13_13_Zsigmondy_13_Step9_fourth_pow_residue.lean`

On `A⁴ + B¹³ = C¹³` write `k = C − B`.
v8.19.8 gives `A⁴ ≡ k¹³ [MOD B]`.

Odd `A` has `A⁴ ≡ 1 [MOD 4]` and
`A⁴ ≡ 1 [MOD 8]`.  Odd `k` has
`k¹³ ≡ k` at those moduli
(`k² ≡ 1 [MOD 8]`).

If `4 ∣ B` then the congruence
descends to mod 4, so `k ≡ 1 [MOD 4]`.
If `8 ∣ B` then `k ≡ 1 [MOD 8]`.

Without odd `A`, `A⁴ ≡ 0 [MOD 16]`
is possible and `k % 4 = 1` can fail.
The residue does not close the equation.

| Name | Status |
|---|---|
| `odd_fourth_mod4` / `odd_fourth_mod8` | inhabited |
| `odd_pow13_mod4` / `odd_pow13_mod8` | inhabited |
| `k_mod4_eq_1_of_fourth_pow_residue` | inhabited |
| `k_mod8_eq_1_of_fourth_pow_residue` | inhabited |
| `beal_4_13_13_k_mod4_eq_1_of_B_mod4_eq_0` | inhabited |
| `beal_4_13_13_k_mod8_eq_1_of_B_mod8_eq_0` | inhabited |
| `k_mod4_eq_1_of_B_mod4_eq_0_without_odd_A` | uninhabited |
| `beal_odd_A_ge3_closed_of_fourth_pow_residue` | uninhabited |
| `beal_4_13_13_k_odd` | stays inhabited (v8.19.8) |
| `zsigmondy_13` | stays inhabited (v8.19.3) |
| `ExistsNewformLevel2` | stays `0 ≠ 0` |

`RibetMazur` does **not** import `X0_26_Model`.
Track A About mint stays `22635221`.
No new Beal `∀` Zenodo.
