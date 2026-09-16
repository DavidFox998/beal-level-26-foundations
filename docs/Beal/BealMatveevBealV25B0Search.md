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

Popcount is defined but **not** used as a reject: fourth powers
are not characterized by popcount.

## What stays `def Prop`

- `gap3_B_le_B0_no_solution` — `∀ B ≤ 10⁶, ∀ A, … ≠ …`.
  Two hundred `native_decide` shards of `(B+3)¹³` at `B ≈ 2·10⁵`
  are not an AMS close. `LLL_reduces_bound_to_B0` / `hGen` /
  `hLLL` remain uninhabited on the Rank-3 target.

Build: `lake build BealMatveevBealV25B0Search`.
v25 is not minted.
