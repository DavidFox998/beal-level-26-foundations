/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import BealMatveevBealV25B0Search.MaskSound

/-!
The modular check is sound only because each mask has a kernel-checked
soundness lemma. The bounded check below is separate from the external JSON
checkpoint; no digest is used as a proof.
-/

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6

open MaskSound

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- `true` excludes a solution at `B` by at least one sound modulus. -/
def check_B_mod_union (B : ℕ) : Bool :=
  ! ((0x4864 : ℕ).testBit (B % 17) &&
     (0x417120584c : ℕ).testBit (B % 41) &&
     (0x5094c4926005402182 : ℕ).testBit (B % 73) &&
     (0x1408402189053208807d18418 : ℕ).testBit (B % 97) &&
     (0xc51080848432812d02d000180880 : ℕ).testBit (B % 113) &&
     (0xd4602104004810081841d4c60480080300 : ℕ).testBit (B % 137) &&
     (0x16582af0810004018c25020042940c8022090d01241320841 : ℕ).testBit (B % 193) &&
     (0xf020001c85622a61110001c400e10a50002bc1308581130c4a1200f42c20 : ℕ).testBit (B % 241) &&
     (0xe241004040a2040a2035000010a2548651a0818000650032b220c250e0a000b4 : ℕ).testBit (B % 257) &&
     (0x4c00340400709a0081cc6010aa30820280184182c8020424801b2029001718d602212e : ℕ).testBit (B % 281))

theorem check_B_mod_union_of_solution {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    check_B_mod_union B = false := by
  simp only [check_B_mod_union, mask_sound_17 hsol, mask_sound_41 hsol,
    mask_sound_73 hsol, mask_sound_97 hsol, mask_sound_113 hsol,
    mask_sound_137 hsol, mask_sound_193 hsol, mask_sound_241 hsol,
    mask_sound_257 hsol, mask_sound_281 hsol, Bool.true_and, Bool.not_true]

/-- Exact Boolean interval check, with exclusive upper endpoint. -/
def checkRange (lo hi : ℕ) : Bool :=
  (List.range (hi - lo)).all (fun i => check_B_mod_union (lo + i))

theorem chunk_no_solution {lo hi : ℕ} (h : checkRange lo hi = true) :
    ∀ B, lo ≤ B → B < hi → ∀ A : ℕ,
      A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 := by
  intro B hlo hhi A hsol
  have hlt : B - lo < hi - lo := by omega
  have hmem : B - lo ∈ List.range (hi - lo) := List.mem_range.mpr hlt
  have hcheck := (List.all_eq_true.mp h) (B - lo) hmem
  have hB : check_B_mod_union B = true := by
    simpa [checkRange, Nat.add_sub_of_le hlo] using hcheck
  rw [check_B_mod_union_of_solution hsol] at hB
  cases hB

def groupCheck (group : ℕ) : Bool :=
  (List.range 20).all fun i =>
    checkRange (500 * (20 * group + i)) (500 * (20 * group + i + 1))

def BealCandidate (B : ℕ) : Prop :=
  ∃ A : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13

/-- A representative kernel-checked interval. The full 2,000 intervals
remain to be checked and composed; this is not the million-case theorem. -/
theorem sample_chunk : checkRange 100000 100500 = true := by decide

#print axioms chunk_no_solution
#print axioms sample_chunk

end BealMatveevBeal.BealMatveevBealV25B0Search.Chunked10e6