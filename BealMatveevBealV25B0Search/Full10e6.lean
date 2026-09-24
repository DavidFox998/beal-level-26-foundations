/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import BealMatveevBealV25B0Search.Forward
import BealMatveevBealV25B0Search.ChunkBlocks.Block00
import BealMatveevBealV25B0Search.ChunkBlocks.Block01
import BealMatveevBealV25B0Search.ChunkBlocks.Block02
import BealMatveevBealV25B0Search.ChunkBlocks.Block03
import BealMatveevBealV25B0Search.ChunkBlocks.Block04
import BealMatveevBealV25B0Search.ChunkBlocks.Block05
import BealMatveevBealV25B0Search.ChunkBlocks.Block06
import BealMatveevBealV25B0Search.ChunkBlocks.Block07
import BealMatveevBealV25B0Search.ChunkBlocks.Block08
import BealMatveevBealV25B0Search.ChunkBlocks.Block09
import BealMatveevBealV25B0Search.ChunkBlocks.Block10
import BealMatveevBealV25B0Search.ChunkBlocks.Block11
import BealMatveevBealV25B0Search.ChunkBlocks.Block12
import BealMatveevBealV25B0Search.ChunkBlocks.Block13
import BealMatveevBealV25B0Search.ChunkBlocks.Block14
import BealMatveevBealV25B0Search.ChunkBlocks.Block15
import BealMatveevBealV25B0Search.ChunkBlocks.Block16
import BealMatveevBealV25B0Search.ChunkBlocks.Block17
import BealMatveevBealV25B0Search.ChunkBlocks.Block18
import BealMatveevBealV25B0Search.ChunkBlocks.Block19

/-!
# Full 10^6 search: conditional Lean interface and external evidence

The exact-integer checkpoint is not a proof input. The proof below uses
separately compiled modular certificates for every 500-value interval.
This does not establish the general Beal theorem.
-/

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Full10e6

open Chunked10e6

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Dispatch to one of twenty blocks, each of which dispatches to ten groups
of ten separately checked 500-value intervals. No large Boolean conjunction
is reduced here. -/
private theorem checked_chunk (n : ℕ) (hn : n < 2000) :
    checkRange (500 * n) (500 * (n + 1)) = true := by
  have blocks : ∀ b < 20, ∀ g < 10, ∀ i < 10,
      checkRange (500 * (100 * b + 10 * g + i))
        (500 * (100 * b + 10 * g + i + 1)) = true := by
    intro b hb g hg i hi
    by_cases h00 : b = 0
    · subst b; exact block_00 g i hg hi
    by_cases h01 : b = 1
    · subst b; exact block_01 g i hg hi
    by_cases h02 : b = 2
    · subst b; exact block_02 g i hg hi
    by_cases h03 : b = 3
    · subst b; exact block_03 g i hg hi
    by_cases h04 : b = 4
    · subst b; exact block_04 g i hg hi
    by_cases h05 : b = 5
    · subst b; exact block_05 g i hg hi
    by_cases h06 : b = 6
    · subst b; exact block_06 g i hg hi
    by_cases h07 : b = 7
    · subst b; exact block_07 g i hg hi
    by_cases h08 : b = 8
    · subst b; exact block_08 g i hg hi
    by_cases h09 : b = 9
    · subst b; exact block_09 g i hg hi
    by_cases h10 : b = 10
    · subst b; exact block_10 g i hg hi
    by_cases h11 : b = 11
    · subst b; exact block_11 g i hg hi
    by_cases h12 : b = 12
    · subst b; exact block_12 g i hg hi
    by_cases h13 : b = 13
    · subst b; exact block_13 g i hg hi
    by_cases h14 : b = 14
    · subst b; exact block_14 g i hg hi
    by_cases h15 : b = 15
    · subst b; exact block_15 g i hg hi
    by_cases h16 : b = 16
    · subst b; exact block_16 g i hg hi
    by_cases h17 : b = 17
    · subst b; exact block_17 g i hg hi
    by_cases h18 : b = 18
    · subst b; exact block_18 g i hg hi
    by_cases h19 : b = 19
    · subst b; exact block_19 g i hg hi
    omega
  have hcert := blocks (n / 100) (by omega) ((n % 100) / 10)
    (by omega) (n % 10) (by omega)
  have hrep : n = 100 * (n / 100) + 10 * ((n % 100) / 10) + n % 10 := by omega
  rw [← hrep] at hcert
  exact hcert

/-- Inclusive bound: the 2,000 intervals cover `B < 1,000,000`, and the
endpoint is independently kernel-checked. -/
theorem full10e6_no_solution_forward :
    BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution := by
  intro B hB A hsol
  have hnum : B ≤ 1000000 := by
    simpa [BealMatveevBealV25B0Search.B0_nat_eq] using hB
  rcases Nat.lt_or_eq_of_le hnum with hlt | heq
  · have hchunk := checked_chunk (B / 500) (by omega)
    exact chunk_no_solution hchunk B (by omega) (by omega) A hsol
  · subst B
    have hend : check_B_mod_union 1000000 = true := by decide
    rw [check_B_mod_union_of_solution hsol] at hend
    cases hend

#print axioms full10e6_no_solution_forward

/-- The actual pinned Matveev numerals, not a bound on every solution. -/
structure MatveevBoundCert : Prop where
  matveevC1 : BealMatveevBealV25B0Search.C1_floor = 143186215390
  bakerB0 : BealMatveevBealV25B0Search.B0_nat = 1000000

theorem matveev_bound_cert : MatveevBoundCert :=
  ⟨BealMatveevBealV25B0Search.C1_floor_eq,
    BealMatveevBealV25B0Search.B0_nat_eq⟩

/-- Level-26 and small-search evidence. The numerical component is still an
explicit hypothesis: displayed numbers do not construct a Néron model. -/
structure Level26EliminationCert : Prop where
  level26 : Forward.Level26SearchData
  below1000 : ∀ B < 1000, ∀ A : ℕ,
    A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13

/-- The full-search projection is now unconditional for the bounded equation. -/
theorem B0_10e6_search_forward :
    BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution :=
  full10e6_no_solution_forward

/-- The numerical search is unconditional; the level-26 input still contains
separate mathematical assumptions and is not a general Beal theorem. -/
theorem beal_10e6_inhabited_forward
    (bound : MatveevBoundCert)
    (level26 : Level26EliminationCert) :
    MatveevBoundCert ∧ Level26EliminationCert ∧
      BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution :=
  ⟨bound, level26, B0_10e6_search_forward⟩

#print axioms matveev_bound_cert
#print axioms B0_10e6_search_forward
#print axioms beal_10e6_inhabited_forward

end BealMatveevBeal.BealMatveevBealV25B0Search.Full10e6