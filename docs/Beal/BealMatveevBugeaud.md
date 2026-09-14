# MatveevBugeaud — displayed-lattice Baker–Davenport no-go

Lean: [`MatveevBugeaud.lean`](../../MatveevBugeaud.lean)
(root module; `Beal/Matveev/MatveevBugeaud.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.MatveevBugeaud`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `c78b413` (`v24-v24x-final-LLL-svt-det`). This is the
honest Bugeaud / LLL *reduction proof* for the displayed
`C = 10^{30}` lattice: Baker–Davenport on `v = 4 b₁ − 13 b₂`
**cannot** inhabit `baker_bound_gap3`.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `LLL_C_div_B0_eq`: `C / B0 = 10^{24}`.
- `LLL_v_third_abs_lt_C_mul_abs_Lambda_add`: the floor-form
  error `|v₃ − C Λ| < 17` rearranges by the triangle inequality
  to `|v₃| < 17 + C|Λ|`, for every `A, B`.
- `bugeaud_third_lt_seventeen_add_C_div_B`: on a solution,
  `|Λ| < 1/B` upgrades that to `|v₃| < 17 + C/B` (all `B > 0`).
- `bugeaud_bd_lower_lt_abs_Lambda`: if `17 < r ≤ |v₃|` then
  `(r − 17)/C < |Λ|`. Usable Baker–Davenport on this `v` is
  strictly weaker than `|Λ|` itself, so it cannot contradict
  any upper bound on `|Λ|`.
- `bugeaud_bd_lower_lt_inv_B` / `bugeaud_bd_lower_lt_ratio`:
  therefore `(r − 17)/C < 1/B` and `(r − 17)/C < B⁴/A⁴`.
- `bugeaud_required_r`: beating `1/B` would need `r ≥ 17 + C/B`.
- `bugeaud_required_r_gt_eighteen_of_B_lt_C`: if `B < C` then
  that required witness already exceeds `18`.
- `exists_reduced_b1_lt_sixty_four`: on a solution with
  `B > 10⁶`, an LLL-reduced generating first vector is short
  (`‖b₁‖ ≤ 2 λ₁ < 64`).
- `bugeaud_naive_gs_lt_inv_B0`: even a naive `‖b₁‖ < 64` still
  gives `(‖b₁‖ − 17)/C < 1/B0`.
- `not_exists_reduced_b1_gt_required_r`: for
  `B0 < B < C/47`, no reduced generating first vector meets
  `17 + C/B`.

Raising `C` or swapping columns does not help: `v` stays short
by construction, so `λ₁ ≤ ‖v‖ < 32`. The uniform-`C` theorems
`floor_form_third_abs_lt`, `baker_davenport_reduction_nogo`,
`baker_davenport_no_witness_above_C_div_B0`, and
`bugeaud_LLL_method_fails` prove the same rearrangement for
**every** `C > 0`: no witness `r > 17 + C/B0` exists on a
solution with `B ≥ B0`. Wüstholz / `C1_floor` cannot close the
gap either (`exp(−C1 log A log B)` is far smaller than
`B⁴/A⁴`).

## What stays a def Prop

- `bugeaud_LLL_reduction_proof`
- `baker_davenport_reduction`
- `baker_bound_gap3_from_ratio`
- Level 26 `baker_bound_gap3`

Inhabiting any of those would be v25. This file proves the
displayed lattice cannot do it. Not a minted v25 tag.
