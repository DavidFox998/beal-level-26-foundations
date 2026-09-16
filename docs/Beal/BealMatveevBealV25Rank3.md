# Rank-3 Bugeaud–Laurent shape wrappers (not a v25 mint)

Lean: [`BealMatveevBealV25Rank3.lean`](../../BealMatveevBealV25Rank3.lean)
(root module only — there is **no** `Beal/Matveev/` stub, because
Lake `.submodules Beal.Matveev` would pull it into the default
`BealMatveevBeal` glob).
Namespace: `BealMatveevBeal.BealMatveevBealV25Rank3`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Separate Lake target `BealMatveevBealV25Rank3`. Default
`lake build BealMatveevBeal` does **not** compile this file.
Successor of `v24-v24x-final-lll-dirichlet-nogo`. This file
does **not** import `Beal.Matveev.MatveevThm14General`. It does
**not** fork Mathlib and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

## What is wrapped (0 sorry)

- `gap3_B_lt_A_of_sol` — on a gap-3 solution, `B < A`, via
  `PAdicLLL.A_gt_B_of_sol` / GapK. Fillable; does **not** inhabit
  `LLL_reduces_bound_to_B0`.
- `abs_Lambda_lt_inv_B` — `|4 log A − 13 log(B+3)| < 1/B`, via
  `MatveevLLL.abs_Lambda_le_inv_B`. The pc2 lemma
  `2(B+10)⁴ < (B+1)¹³` is `¬ A ≤ B+10`, not this log bound.
- `lll_short_vector_of_large_B` — rank-3 `v = 4 b₁ − 13 b₂`
  satisfies `‖v‖ < 32` and `v ≠ 0` on a solution with `B > B0`.
  This is `MatveevLLL.LLL_v_norm_lt_thirty_two`. Minkowski / LLL
  still *upper*-bound `λ₁`. Compatible with `|Λ| < 1/B`
  (`baker_davenport_no_cutoff`).
- `future_unconditional_shape` — the `by_cases B ≤ B0` implication.
  Neither branch is inhabited: `matveev_gap3_lower` is a lower
  bound on `|Λ|` when a solution exists and `B ≤ B0`, not `¬∃ A`;
  the `B > B0` side is `LLL_reduces_bound_to_B0`.

Placeholder `C = B0` is **not** the working lattice.
`MatveevLLL.LLL_C_nat = 10^30`. Shrinking `C` does not turn
`‖v‖ < 32` into a lower bound on `|Λ|`.

## What is not claimed

- Euclidean length `≥ B0` (`lll_euclidean_lower_bound_fails`:
  floor lattice `b1=(1,0)` has length `1 < B0`).
- `|u α + v| > exp(−B0)` (`lll_form_lower_bound_fails` by Dirichlet).
- `lll_lower_bound ≥ B0` or `≥ B0/C_LLL` (Euclidean length `1 < B0`,
  and `5e-17 < 1/B`).

## What stays `def Prop`

- `LLL_reduces_bound_to_B0`
- `LLL_reduces_bound_to_B0_future`
- `hGen`
- `hLLL`

Defining any of those as the constant true proposition is
forbidden. Darmon–Merel `(4,4,13)` is still
`BealTrueV25.darmon_merel_4413_axiom`, not Mathlib 4.12.

`#print axioms gap3_B_lt_A_of_sol` /
`abs_Lambda_lt_inv_B` / `lll_short_vector_of_large_B` /
`future_unconditional_shape` / `rank3_shape_nogo` are
`[propext, Classical.choice, Quot.sound]`.

Build: `lake build BealMatveevBealV25Rank3`.
v25 is not minted.
