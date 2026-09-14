# MatveevThreeLogs — log-method no-go (not a `B ≤ 10⁶` close)

Lean: [`MatveevThreeLogs.lean`](../../MatveevThreeLogs.lean)
(root module; `Beal/Matveev/MatveevThreeLogs.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.MatveevThreeLogs`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `2a17664` (`v24-v24x-final-LLL-nogo-product`).
Padding `Λ = 4 log A − 13 log(B+3)` with a dummy `0 · log 2`
does not produce a three-log lower bound: `Lambda3 = Lambda`.
A Matveev-style exponential `exp(−C1 log A log(B+3))` beats
`B⁴/A⁴` at `B ≥ B0` only if `C1 < 1` (in fact
`C1 < 4 / log B0 < 1`). Every constant actually available —
`C1_floor`, the two-log jet `242`, even the ideal `C1 = 1` —
is too large, so the lower bound is strictly smaller than the
ratio and cannot cut off `B ≤ 10⁶`.

A four-factor jet `(L+1)(N1+1)(N2+1)(N3+1)` is cubic in the
`G_m` degrees; there is still no uniform `c` of shape `c L K`.
Philippon for `𝐆_a × 𝐆_m³` is not in Mathlib 4.12.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `Lambda3_eq_Lambda`: dummy third logarithm is identically `Λ`.
- `log_B0_gt_thirteen` / `four_div_log_B0_lt_one`:
  `13 < log B0`, so any cutoff would need `C1 < 1`.
- `baker_bound_gap3_nogo_logs`: for every `C1 ≥ 1`, on a gap-3
  solution with `B ≥ B0`,
  `exp(−C1 log A log(B+3)) < B⁴/A⁴`.
- `C1_floor_exp_lt_ratio` / `two_forty_two_exp_lt_ratio` /
  `one_exp_lt_ratio` / `matveev_lower_nogo_logs`: the displayed
  Bugeaud floor, the two-log jet `242`, and the ideal `C1 = 1`
  all lose to the ratio.
- `Lambda_upper_lt_inv_B0`: `|Λ| < 1/B0` whenever `B ≥ B0`
  (still `< 1/B` for every `B > 0`, so not a cutoff).
- `coeffCount3_zero_ten_ten_ten` / `coeffCount3_one_ten_ten_ten`:
  displayed four-factor jets `1331` and `2662`.
- `no_uniform_c_cubic_in_N`: no uniform `c` makes `c L K`
  dominate a cubic jet.

## What stays a def Prop

- `baker_bound_gap3` — unconditional `B ≤ 10⁶` on a gap-3
  solution. Not inhabited. The proved statement is that the
  log method cannot force it.
- `wuestholz_product_theorem_exp` / `wuestholz_subgroup_theorem`
  — uniform product / subgroup theorems (Philippon).
- `wuestholz_product_theorem_exp_Gm3` — the same on
  `𝐆_a × 𝐆_m³`.
- `baker_davenport_reduction` / `bugeaud_LLL_reduction_proof`.

Not a minted v25 tag.
