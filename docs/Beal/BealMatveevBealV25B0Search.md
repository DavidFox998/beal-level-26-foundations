# Gap-3 `B ≤ B0` search slice (not a v25 mint)

Lean: [`BealMatveevBealV25B0Search.lean`](../../BealMatveevBealV25B0Search.lean)
(root module only — there is **no** `Beal/Matveev/` stub).
Namespace: `BealMatveevBeal.BealMatveevBealV25B0Search`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390`. `B0_nat = 1000000`.

Separate Lake target `BealMatveevBealV25B0Search`. Default
`lake build BealMatveevBeal` does **not** compile this file.
This file does **not** import `Beal.Matveev.MatveevThm14General`.
It does **not** rewrite `matveev_gap3_lower` and does **not**
re-introduce the false window `A ∈ [B, B+10]`. It does **not**
mint `v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

## What is closed (0 sorry)

- `fourth_pow_mod16` — `n⁴ % 16 ∈ {0,1}` (`[propext]`).
- `is_fourth_power_iff` — floor fourth root via two `Nat.sqrt`.
- `check_B` — `true` means no solution at that `B` (mod-16 reject
  or the difference is not a fourth power).
- `check_B_true_no_sol` — extracts the Bool checker to a Prop.
- `check_upto` / `check_upto_spec` — structural prefix checker
  (`check_upto 10000` overflows the kernel stack).
- `foldl_and_true` — foldl invariant: `foldl (· && p ·) b l = true`
  forces `b` and every `p x` (list induction, no `sorry`).
- `check_range` / `check_range_true_of_all` — shifted range via
  `List.range (hi-lo).foldl`, not an `hi`-deep recursive loop.
- `shard_0_100` … `shard_900_1000` — ten `native_decide` shards
  of 100 (each computes `100 · (B+3)¹³`, not one shard of 1000).
- `gap3_B_lt_1000_no_sol` — `∀ B < 1000, ∀ A, A⁴+B⁴ ≠ (B+3)¹³`
  (glues the ten shards; axiom `Lean.ofReduceBool`).
- `eps_le_inv_B_pow_nine` / `eps_lt_half` — `ε = B⁴/(B+3)¹³ ≤ 1/B⁹ < 1/2`
  for `B ≥ 100`.
- `abs_Lambda_eq_log_one_sub_eps` — Nat-to-Real cast
  `A⁴ = (B+3)¹³ − B⁴` plus `Real.log_pow`.
- `abs_Lambda_lt_two_eps` / `abs_Lambda_lt_two_div_B_pow_nine` —
  `|Λ| ≤ 2ε ≤ 2/B⁹` on a solution with `B ≥ 100`, strictly
  tighter than `|Λ| < 1/B` (`two_div_B_pow_nine_lt_inv_B`).

Popcount is defined but **not** used as a reject: fourth powers
are not characterized by popcount. One hundred shards through
`B < 10000` are **not** shipped (`(B+3)¹³ ≈ 10⁵²`).

## What stays `def Prop`

- `gap3_B_le_B0_no_solution` — `∀ B ≤ 10⁶, ∀ A, … ≠ …`.
  Two hundred `native_decide` shards of `(B+3)¹³` at `B ≈ 2·10⁵`
  are not an AMS close.
- `abs_Lambda_ge_inv_B_pow_eight` — LLL would need `|Λ| ≥ B⁻⁸`
  (reduce `C1` from `1.4·10¹¹` to `< 9`). Bugeaud–Laurent
  typically reaches `10²`–`10³`, not `< 9`.
- Root module [`LLLTargetB8.lean`](../../LLLTargetB8.lean)
  (same Lake target; **no** `Beal/Matveev/` stub):
  `abs_Lambda_ge_B_pow_neg_eight`, `LLL_reduces_C1_to_lt_nine`,
  and `LLL_reduces_bound_to_B0_v25` stay `def Prop`.
  `no_sol_of_abs_Lambda_ge_B_pow_neg_eight` is the implication
  `|Λ| ≥ B⁻⁸` + `|Λ| ≤ 2/B⁹` ⇒ `B ≤ 2` ⇒ not `B ≥ B0`.
  `future_v25_shape_of_B8_lift` is the `by_cases` packaging;
  neither branch is inhabited.
  Phase-lift lattice: `C_LLL = 10³⁰`, `b1 = (1,0)`,
  `b2 = (⌊C log(B+3)⌋, 1)`. Theorems: `lambda1_ge_one`,
  `v_short_mem_L`, `C_LLL_mul_inv_B_pow_eight_lt_half`
  (`C·B⁻⁸ < 1/2`), `C_LLL_mul_two_div_B_pow_nine_lt_one`.
  Nogo: `not_exists_nonzero_euc_lt_one` (`euc v < 1 ↔ v = 0`
  on `ℤ×ℤ`); `v_short` is a multiple of `b1`. The implication
  `LLL_lift_to_B8_of_short_vector` still needs `h_exists`.
  `LLL_reduces_bound_to_B0` / `hGen` / `hLLL` remain uninhabited
  on the Rank-3 target.

Build: `lake build BealMatveevBealV25B0Search`.
v25 is not minted.
