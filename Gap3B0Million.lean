/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Separate Lake target `BealMatveevBealV25B0Search`.
  Do **not** add `Beal/Matveev/Gap3Shards` or
  `Beal/Matveev/Gap3_B_le_B0.lean`: `.submodules Beal.Matveev`
  would pull them into the default glob. Do **not** import
  `Beal.Matveev.MatveevThm14General`.
-/
import BealMatveevBealV25B0Search

/-!
# Gap-3 `B < B0` foldl aggregator (not a v25 mint)

Same checker as `BealMatveevBealV25B0Search`: `check_range` is
`List.range.foldl` of `check_B`. Ten thousand shards of 100 would
cover `B < 10⁶`. This file proves the **wiring**:
if every shard is `true`, then there is no gap-3 solution with
`B < B0`. It does **not** `native_decide` those shards.
`(B+3)¹³` at `B ≈ 10⁶` is `≈ 10⁷⁸`; that is why the closed
computational slice stays `B < 1000` (`gap3_B_lt_1000_no_sol`)
and `gap3_B_le_B0_no_solution` stays `def Prop`.

`scripts/gen_gap3_shards.py` can emit `Gap3Shards/` at repo root
(never under `Beal/Matveev/`). Those files are not committed and
not in any Lake glob.

Does **not** mint v25. 0 sorry.
-/

namespace BealMatveevBeal.Gap3B0Million

open BealMatveevBeal.BealMatveevBealV25B0Search

def nShards : ℕ := 10000

def shardSize : ℕ := 100

theorem nShards_eq : nShards = 10000 := rfl

theorem shardSize_eq : shardSize = 100 := rfl

theorem nShards_mul_size : nShards * shardSize = 1000000 := by
  decide

def shardLo (i : ℕ) : ℕ := shardSize * i

def shardHi (i : ℕ) : ℕ := shardSize * (i + 1)

theorem shardHi_eq (i : ℕ) : shardHi i = shardLo i + shardSize := by
  unfold shardHi shardLo
  rw [Nat.mul_succ]

/-- Foldl of `check_range (i·100) ((i+1)·100)` over `i < 10000`.
    Evaluating this Bool is the million-`B` search; not `native_decide`'d. -/
def allShardsTrue : Bool :=
  (List.range nShards).foldl
    (fun acc i => acc && check_range (shardLo i) (shardHi i)) true

/-- Uninhabited: would require the 10k shard Bools. -/
def allShardsTrue_eq_true : Prop :=
  allShardsTrue = true

theorem B_div_shardSize_lt_nShards {B : ℕ} (hB : B < 1000000) :
    B / shardSize < nShards := by
  unfold shardSize nShards
  have hmul : B < 10000 * 100 := by
    have heq : (10000 : ℕ) * 100 = 1000000 := by decide
    rwa [heq]
  exact (Nat.div_lt_iff_lt_mul (by decide : (0 : ℕ) < 100)).mpr hmul

theorem shardLo_le {B : ℕ} : shardLo (B / shardSize) ≤ B := by
  unfold shardLo shardSize
  exact Nat.mul_div_le B 100

theorem B_lt_shardHi {B : ℕ} : B < shardHi (B / shardSize) := by
  unfold shardHi shardSize
  have hmod : B % 100 < 100 := Nat.mod_lt B (by decide : (0 : ℕ) < 100)
  calc
    B = 100 * (B / 100) + B % 100 := (Nat.div_add_mod B 100).symm
    _ < 100 * (B / 100) + 100 := Nat.add_lt_add_left hmod _
    _ = 100 * (B / 100 + 1) := (Nat.mul_succ 100 (B / 100)).symm

theorem allShardsTrue_spec (h : allShardsTrue = true) :
    ∀ i ∈ List.range nShards,
      check_range (shardLo i) (shardHi i) = true := by
  have hfold :=
    foldl_and_true (fun i => check_range (shardLo i) (shardHi i))
      (List.range nShards) true (by simpa [allShardsTrue] using h)
  exact hfold.2

theorem allShardsTrue_check_B (h : allShardsTrue = true)
    {B : ℕ} (hB : B < 1000000) : check_B B = true := by
  have hi : B / shardSize ∈ List.range nShards :=
    List.mem_range.mpr (B_div_shardSize_lt_nShards hB)
  have hsh := allShardsTrue_spec h (B / shardSize) hi
  exact check_range_spec hsh B shardLo_le B_lt_shardHi

/-- If the 10k foldl Bool is `true`, there is no gap-3 solution
    with `B < B0`. Does **not** inhabit `allShardsTrue = true`.
    Does **not** inhabit `gap3_B_le_B0_no_solution` (`B ≤ B0`
    still needs `B = B0`). -/
theorem gap3_B_lt_B0_of_allShardsTrue (h : allShardsTrue = true) :
    ∀ B < B0_nat, ∀ A, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro B hB A
  have hB' : B < 1000000 := by
    simpa [B0_nat_eq] using hB
  exact check_B_true_no_sol (allShardsTrue_check_B h hB') A

/-- Inclusive `B ≤ B0` needs the extra point `B = B0`. Still an
    implication: does **not** inhabit `gap3_B_le_B0_no_solution`. -/
theorem gap3_B_le_B0_of_allShardsTrue
    (h : allShardsTrue = true) (hB0 : check_B B0_nat = true) :
    ∀ B ≤ B0_nat, ∀ A, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro B hB A
  cases Nat.lt_or_eq_of_le hB with
  | inl hlt =>
    exact gap3_B_lt_B0_of_allShardsTrue h B hlt A
  | inr heq =>
    simpa [heq] using check_B_true_no_sol hB0 A

#check allShardsTrue
#check allShardsTrue_eq_true
#check gap3_B_lt_B0_of_allShardsTrue
#check gap3_B_le_B0_of_allShardsTrue
#print axioms gap3_B_lt_B0_of_allShardsTrue
#print axioms gap3_B_le_B0_of_allShardsTrue

end BealMatveevBeal.Gap3B0Million
