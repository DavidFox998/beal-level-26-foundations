/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Separate Lake target `BealMatveevBealV25B0Search`,
  **not** the default `BealMatveevBeal` glob. Do **not** import
  `Beal.Matveev.MatveevThm14General`. Do **not** add a
  `Beal/Matveev/` stub.
-/
import Mathlib

/-!
# Gap-3 `B ≤ B0` search slice (not a v25 mint)

Computable mod-16 reject plus floor fourth-root test for
`A⁴ = (B+3)¹³ − B⁴`. A **small** range is closed by
`native_decide` on **ten shards of 100**, not one recursive
`check_upto 1000`. The full statement
`∀ B ≤ B0, ¬∃ A, A⁴+B⁴=(B+3)¹³` stays `def Prop`:
`check_upto 10000` overflows, and a million 13th-power shards
is not an AMS close. Popcount is **not** a sound reject.
Closed slice: `B < 1000` from `shard_0_100` … `shard_900_1000`.

This does **not** rewrite `matveev_gap3_lower` (that theorem
is a lower bound on `|Λ|` when a solution exists and `B ≤ B0`,
not `¬∃ A`). It does **not** re-introduce the false window
`A ∈ [B, B+10]`. `LLL_reduces_bound_to_B0` / `hGen` / `hLLL`
stay uninhabited. Darmon–Merel `(4,4,13)` is still an extra
axiom in `BealTrueV25`. This file does **not** fork Mathlib
and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.
0 sorry. `C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

namespace BealMatveevBeal.BealMatveevBealV25B0Search

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

/-! ## Mod-16 fourth-power residues -/

theorem fourth_pow_mod16 (n : ℕ) :
    n ^ 4 % 16 = 0 ∨ n ^ 4 % 16 = 1 := by
  have hlt : n % 16 < 16 := Nat.mod_lt n (by decide)
  rw [Nat.pow_mod]
  interval_cases n % 16
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)
  · exact Or.inl (by decide)
  · exact Or.inr (by decide)

/-- Floor fourth root via two `Nat.sqrt`. -/
def fourth_root_floor (n : ℕ) : ℕ := Nat.sqrt (Nat.sqrt n)

def is_fourth_power (n : ℕ) : Bool :=
  decide (fourth_root_floor n ^ 4 = n)

theorem sqrt_sq (k : ℕ) : Nat.sqrt (k * k) = k :=
  Nat.sqrt_eq k

theorem fourth_root_floor_of_fourth (k : ℕ) :
    fourth_root_floor (k ^ 4) = k := by
  unfold fourth_root_floor
  have hsq : k ^ 4 = k ^ 2 * k ^ 2 := by
    rw [pow_two, pow_succ, pow_succ, pow_two]
    ring
  rw [hsq, sqrt_sq, pow_two, sqrt_sq]

theorem is_fourth_power_iff (n : ℕ) :
    is_fourth_power n = true ↔ ∃ k : ℕ, k ^ 4 = n := by
  unfold is_fourth_power
  constructor
  · intro h
    refine ⟨fourth_root_floor n, ?_⟩
    simpa using of_decide_eq_true h
  · intro ⟨k, hk⟩
    subst hk
    rw [fourth_root_floor_of_fourth]
    simp

/-! ## One-`B` checker -/

/-- `true` means “no solution at this `B`”. `false` means the
    difference is a fourth power (a candidate solution). -/
def check_B (B : ℕ) : Bool :=
  let rhs := (B + 3) ^ 13
  let b4 := B ^ 4
  if rhs < b4 then
    true
  else
    let diff := rhs - b4
    let d16 := diff % 16
    if d16 != 0 && d16 != 1 then
      true
    else
      !is_fourth_power diff

theorem add_eq_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    B ^ 4 ≤ (B + 3) ^ 13 ∧ A ^ 4 = (B + 3) ^ 13 - B ^ 4 := by
  have hle : B ^ 4 ≤ (B + 3) ^ 13 := by
    have : B ^ 4 ≤ A ^ 4 + B ^ 4 := Nat.le_add_left _ _
    exact this.trans_eq hsol
  refine ⟨hle, ?_⟩
  have hsub := congrArg (fun n => n - B ^ 4) hsol
  simpa [Nat.add_sub_cancel] using hsub

theorem check_B_true_no_sol {B : ℕ} (h : check_B B = true) (A : ℕ) :
    A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro hsol
  have hparts := add_eq_of_sol hsol
  have hrhs : ¬ (B + 3) ^ 13 < B ^ 4 := not_lt.mpr hparts.1
  have hA4 : A ^ 4 = (B + 3) ^ 13 - B ^ 4 := hparts.2
  have hfp : is_fourth_power ((B + 3) ^ 13 - B ^ 4) = true :=
    (is_fourth_power_iff _).mpr ⟨A, hA4⟩
  have hd16 : ((B + 3) ^ 13 - B ^ 4) % 16 = 0 ∨
      ((B + 3) ^ 13 - B ^ 4) % 16 = 1 := by
    rw [← hA4]
    exact fourth_pow_mod16 A
  unfold check_B at h
  simp [hrhs] at h
  revert h
  cases hd16 with
  | inl h0 =>
    simp [h0, hfp]
  | inr h1 =>
    simp [h1, hfp]

/-! ## Prefix checker (structural recursion, no `let rec`) -/

def check_upto : ℕ → Bool
  | 0 => true
  | n + 1 => check_upto n && check_B n

theorem check_upto_spec :
    ∀ n, check_upto n = true → ∀ B < n, check_B B = true := by
  intro n hn B hB
  induction n with
  | zero =>
    exact (Nat.not_lt_zero B hB).elim
  | succ n ih =>
    have hboth : check_upto n = true ∧ check_B n = true := by
      simpa [check_upto, Bool.and_eq_true] using hn
    have hle : B ≤ n := Nat.lt_succ_iff.mp hB
    cases Nat.lt_or_eq_of_le hle with
    | inl hlt =>
      exact ih hboth.1 hlt
    | inr heq =>
      simpa [heq] using hboth.2

theorem check_upto_no_sol {n : ℕ} (h : check_upto n = true) :
    ∀ B < n, ∀ A, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro B hB A
  exact check_B_true_no_sol (check_upto_spec n h B hB) A

/-- Foldl invariant: `foldl (· && p ·) b l = true` forces `b`
    and every `p x`. No recursion on `hi`. -/
theorem foldl_and_true {α} (p : α → Bool) :
    ∀ (l : List α) (b : Bool),
      l.foldl (fun acc x => acc && p x) b = true →
        b = true ∧ ∀ x ∈ l, p x = true := by
  intro l
  induction l with
  | nil =>
    intro b hb
    simp only [List.foldl_nil] at hb
    exact ⟨hb, by simp⟩
  | cons a l ih =>
    intro b hb
    simp only [List.foldl_cons] at hb
    have hpair := ih (b && p a) hb
    have hb' : (b && p a) = true := hpair.1
    have hbtrue : b = true := by
      cases b
      · simp at hb'
      · rfl
    have hpa : p a = true := by
      rw [hbtrue] at hb'
      simpa using hb'
    refine ⟨hbtrue, ?_⟩
    intro x hx
    rw [List.mem_cons] at hx
    cases hx with
    | inl hxa => simpa [hxa] using hpa
    | inr hxl => exact hpair.2 x hxl

/-- Shifted range via `foldl`, not an `hi`-deep recursive loop
    (`check_upto 10000` overflows). -/
def check_range (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).foldl (fun acc i => acc && check_B (lo + i)) true

theorem check_range_spec {lo hi : ℕ} (h : check_range lo hi = true) :
    ∀ B, lo ≤ B → B < hi → check_B B = true := by
  intro B hlo hhi
  have hlt : B - lo < hi - lo := by omega
  have hmem : B - lo ∈ List.range (hi - lo) := List.mem_range.mpr hlt
  have hfold :=
    foldl_and_true (fun i => check_B (lo + i)) (List.range (hi - lo)) true
      (by simpa [check_range] using h)
  have := hfold.2 (B - lo) hmem
  simpa [Nat.add_sub_of_le hlo] using this

/-- User-facing name for the foldl extraction. -/
theorem check_range_true_of_all {lo hi : ℕ}
    (h : check_range lo hi = true) :
    ∀ B, lo ≤ B → B < hi → check_B B = true :=
  check_range_spec h

theorem check_range_no_sol {lo hi : ℕ} (h : check_range lo hi = true) :
    ∀ B, lo ≤ B → B < hi → ∀ A, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro B hlo hhi A
  exact check_B_true_no_sol (check_range_spec h B hlo hhi) A

/-- Heuristic only. Fourth powers are not characterized by
    popcount; this is **not** used as a reject. Lean 4.12 has
    no `Nat.popCount`. -/
def popcount (n : ℕ) : ℕ :=
  if n = 0 then
    0
  else
    popcount (n / 2) + if n.testBit 0 then 1 else 0
termination_by n
decreasing_by
  exact Nat.div_lt_self (Nat.pos_of_ne_zero ‹n ≠ 0›) (by decide)

/-! ## Closed small range. Ten shards of 100. Not `B ≤ B0`. -/

theorem shard_0_100 : check_range 0 100 = true := by native_decide
theorem shard_100_200 : check_range 100 200 = true := by native_decide
theorem shard_200_300 : check_range 200 300 = true := by native_decide
theorem shard_300_400 : check_range 300 400 = true := by native_decide
theorem shard_400_500 : check_range 400 500 = true := by native_decide
theorem shard_500_600 : check_range 500 600 = true := by native_decide
theorem shard_600_700 : check_range 600 700 = true := by native_decide
theorem shard_700_800 : check_range 700 800 = true := by native_decide
theorem shard_800_900 : check_range 800 900 = true := by native_decide
theorem shard_900_1000 : check_range 900 1000 = true := by native_decide

theorem gap3_B_lt_1000_no_sol :
    ∀ B < 1000, ∀ A, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro B hB A
  rcases lt_or_le B 100 with h | h
  · exact check_range_no_sol shard_0_100 B (Nat.zero_le B) h A
  rcases lt_or_le B 200 with h2 | h2
  · exact check_range_no_sol shard_100_200 B h h2 A
  rcases lt_or_le B 300 with h3 | h3
  · exact check_range_no_sol shard_200_300 B h2 h3 A
  rcases lt_or_le B 400 with h4 | h4
  · exact check_range_no_sol shard_300_400 B h3 h4 A
  rcases lt_or_le B 500 with h5 | h5
  · exact check_range_no_sol shard_400_500 B h4 h5 A
  rcases lt_or_le B 600 with h6 | h6
  · exact check_range_no_sol shard_500_600 B h5 h6 A
  rcases lt_or_le B 700 with h7 | h7
  · exact check_range_no_sol shard_600_700 B h6 h7 A
  rcases lt_or_le B 800 with h8 | h8
  · exact check_range_no_sol shard_700_800 B h7 h8 A
  rcases lt_or_le B 900 with h9 | h9
  · exact check_range_no_sol shard_800_900 B h8 h9 A
  exact check_range_no_sol shard_900_1000 B h9 hB A

theorem gap3_B_lt_16_no_sol :
    ∀ B < 16, ∀ A, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro B hB A
  exact check_range_no_sol shard_0_100 B (Nat.zero_le B)
    (lt_trans hB (by decide : (16 : ℕ) < 100)) A

theorem gap3_B_lt_64_no_sol :
    ∀ B < 64, ∀ A, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro B hB A
  exact check_range_no_sol shard_0_100 B (Nat.zero_le B)
    (lt_trans hB (by decide : (64 : ℕ) < 100)) A

theorem gap3_B_lt_256_no_sol :
    ∀ B < 256, ∀ A, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 :=
  fun B hB A => gap3_B_lt_1000_no_sol B (lt_trans hB (by decide : (256 : ℕ) < 1000)) A

/-- Full Baker `B ≤ 10⁶` search. Uninhabited: the closed slice
    is `B < 1000` from ten foldl shards of 100. -/
def gap3_B_le_B0_no_solution : Prop :=
  ∀ B ≤ B0_nat, ∀ A : ℕ, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13

#check C1_floor_eq
#check B0_nat_eq
#check fourth_pow_mod16
#check is_fourth_power_iff
#check check_B_true_no_sol
#check check_upto_spec
#check gap3_B_lt_16_no_sol
#check gap3_B_lt_64_no_sol
#check gap3_B_lt_256_no_sol
#check check_range_true_of_all
#check foldl_and_true
#check shard_0_100
#check shard_900_1000
#check gap3_B_lt_1000_no_sol
#check gap3_B_le_B0_no_solution
#print axioms fourth_pow_mod16
#print axioms is_fourth_power_iff
#print axioms check_B_true_no_sol
#print axioms foldl_and_true
#print axioms check_range_true_of_all
#print axioms gap3_B_lt_16_no_sol
#print axioms gap3_B_lt_1000_no_sol

end BealMatveevBeal.BealMatveevBealV25B0Search
