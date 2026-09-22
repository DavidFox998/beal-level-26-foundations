/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.LevelLowering
import Level32Table
import Ribet_928_to_32_Numerical

/-!
# Level-32 newform exclusion boundary

The recorded level-32 space has dimension one and the recorded newform list
contains `32a1`. These table numerals do not construct the eigenform
produced by level lowering and do not prove a trace mismatch for every
gap-3 residue class.
-/

namespace BealMatveevBeal.RibetCurve

/-- Complete Kraus-style trace-mismatch target for every positive gap-3
solution. Uninhabited. -/
def level_32_no_newform_for_Frey_gap3 : Prop :=
  ∀ A B : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13 → 0 < B →
    ∃ l : ℕ, Nat.Prime l ∧ l ≠ 2 ∧ l ≠ 13 ∧
      ¬ l ∣ A ∧ ¬ l ∣ B ∧ ¬ l ∣ B + 3 ∧
      some (BealMatveevBeal.Level32Table.frey_ap l (A % l) (B % l)) ≠
        BealMatveevBeal.Level32Table.newform_32a1_ap l

/-- Level-32 exclusion alias. Still uninhabited. -/
def level_32_no_newform : Prop :=
  level_32_no_newform_for_Frey_gap3

/-- Residual level-32 exclusion alias. Still uninhabited. -/
def no_newforms_at_32_mod13 : Prop :=
  level_32_no_newform

#check level_32_no_newform_for_Frey_gap3
#check level_32_no_newform
#check no_newforms_at_32_mod13

end BealMatveevBeal.RibetCurve