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
  Phase-lift lattices on `phase-lll-lift-b8`: old nogo
  `L` with `b1=(1,0)` still has `λ₁=1`. New `L'` with
  `C_LLL = 10⁴⁸ = B0⁸`, `b1'=(C, ⌊C log(B+3)⌋)`, `b2'=(0,C)`,
  `det = C²`, `λ₁ = C` (`lambda1_ge_C_div_two`,
  `not_exists_nonzero_euc_lt_C_div_two`). `(1,0) ∉ L'`.
  `C/B⁸ = 1` at `B=B0` and `C/B⁸ ≤ 1` for `B ≥ B0`
  (`C_LLL_div_B_pow_eight_le_one`); `C/B⁸ ≥ 1` only for
  `B ≤ B0`. `C·(2/B⁹) < C/2` on `B ≥ B0`. Candidate
  `v_short' = (4 kA − 13 cLog, 0)` has first coordinate
  `≈ C·Λ` of absolute value `< C` on `|Λ| < B⁻⁸`, so
  membership in `L'` forces `0`
  (`v_short'_mem_L'_of_Lambda_lt_imp_zero`).
  `v_short'_mem_L'` stays `def Prop`. 3-dim Bugeaud–Laurent `L3`
  (`ℤ×ℤ×ℤ`): `C_LLL_3 = 10³⁰`, `det = C₃`, `λ₁ = 1` because
  `(1,0,0) ∈ L3` (`L3_lambda1_ge`, `not_L3_lambda1_ge_ten`).
  Minkowski `C₃^{1/3} = 10¹⁰` is an upper-bound scale, not `λ₁`.
  Displayed `4·b3_3 − 13·b1_3` has length `≥ 4 C₃`
  (`v_combo3_euc_ge_four_C`). Need `C1' ≤ 8` for `|Λ| ≥ B⁻⁸`;
  typical `30`–`50` is still `> 8`; `C1' ≥ 9` does not beat
  `|Λ| ≤ 2/B⁹`. `LLL_reduces_C1_to_lt_nine` stays `def Prop`.
  The implication
  `LLL_lift_to_B8_of_short_vector_C48` still needs `h_exists`,
  which `not_exists_nonzero_euc_lt_C_div_two` refutes.
  `LLL_reduces_bound_to_B0` / `hGen` / `hLLL` remain uninhabited
  on the Rank-3 target.

Build: `lake build BealMatveevBealV25B0Search`.
Root [`Gap3B0Million.lean`](../../Gap3B0Million.lean) proves the
foldl wiring: if all 10k `check_range (i·100) ((i+1)·100)` Bools
are `true`, then there is no gap-3 solution with `B < B0`.
`allShardsTrue_eq_true` stays `def Prop`; the generator
[`scripts/gen_gap3_shards.py`](../../scripts/gen_gap3_shards.py)
refuses `Beal/Matveev/` (default glob) and does not commit
`native_decide` of `(B+3)¹³ ≈ 10⁷⁸`. The closed slice stays
`B < 1000`.

v25 is not minted.
