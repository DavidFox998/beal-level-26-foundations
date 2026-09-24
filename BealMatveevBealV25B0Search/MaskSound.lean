/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import BealMatveevBealV25B0Search

/-!
The masks are finite modular certificates, not hashes of an external search.
Bit `b` means that a fourth-power residue can satisfy the equation at `B ≡ b`.
Each validity check is reduced by the Lean kernel, without native evaluation.
-/

namespace BealMatveevBeal.BealMatveevBealV25B0Search.MaskSound

set_option maxRecDepth 4096
set_option maxHeartbeats 0

/-- Check all pairs of residues; an omitted bit must be impossible for a
solution modulo `p`. -/
def maskValid (p mask : ℕ) : Bool :=
  (List.range p).all fun b =>
    (List.range p).all fun a =>
      if (a ^ 4 + b ^ 4) % p == ((b + 3) ^ 13) % p then
        mask.testBit b
      else true

theorem mask_sound {p mask A B : ℕ} (hp : 0 < p)
    (hvalid : maskValid p mask = true)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    mask.testBit (B % p) = true := by
  have hB : B % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt B hp)
  have hA : A % p ∈ List.range p := List.mem_range.mpr (Nat.mod_lt A hp)
  have hrow := (List.all_eq_true.mp hvalid) (B % p) hB
  have hcell := (List.all_eq_true.mp hrow) (A % p) hA
  have hmod : ((A % p) ^ 4 + (B % p) ^ 4) % p =
      (((B % p) + 3) ^ 13) % p := by
    calc
      ((A % p) ^ 4 + (B % p) ^ 4) % p =
          (A ^ 4 + B ^ 4) % p := by simp [Nat.add_mod, Nat.pow_mod]
      _ = ((B + 3) ^ 13) % p := congrArg (· % p) hsol
      _ = (((B % p) + 3) ^ 13) % p := by simp [Nat.add_mod, Nat.pow_mod]
  simpa [maskValid, hmod] using hcell

theorem mask_sound_17 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0x4864 : ℕ).testBit (B % 17) = true :=
  mask_sound (by decide) (by decide) hsol

theorem mask_sound_41 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0x417120584c : ℕ).testBit (B % 41) = true :=
  mask_sound (by decide) (by decide) hsol

theorem mask_sound_73 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0x5094c4926005402182 : ℕ).testBit (B % 73) = true :=
  mask_sound (by decide) (by decide) hsol

theorem mask_sound_97 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0x1408402189053208807d18418 : ℕ).testBit (B % 97) = true :=
  mask_sound (by decide) (by decide) hsol

theorem mask_sound_113 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0xc51080848432812d02d000180880 : ℕ).testBit (B % 113) = true :=
  mask_sound (by decide) (by decide) hsol

theorem mask_sound_137 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0xd4602104004810081841d4c60480080300 : ℕ).testBit (B % 137) = true :=
  mask_sound (by decide) (by decide) hsol

theorem mask_sound_193 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0x16582af0810004018c25020042940c8022090d01241320841 : ℕ).testBit (B % 193) = true :=
  mask_sound (by decide) (by decide) hsol

theorem mask_sound_241 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0xf020001c85622a61110001c400e10a50002bc1308581130c4a1200f42c20 : ℕ).testBit (B % 241) = true :=
  mask_sound (by decide) (by decide) hsol

theorem mask_sound_257 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0xe241004040a2040a2035000010a2548651a0818000650032b220c250e0a000b4 : ℕ).testBit (B % 257) = true :=
  mask_sound (by decide) (by decide) hsol

theorem mask_sound_281 {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) :
    (0x4c00340400709a0081cc6010aa30820280184182c8020424801b2029001718d602212e : ℕ).testBit (B % 281) = true :=
  mask_sound (by decide) (by decide) hsol

#print axioms mask_sound_17
#print axioms mask_sound_281

end BealMatveevBeal.BealMatveevBealV25B0Search.MaskSound