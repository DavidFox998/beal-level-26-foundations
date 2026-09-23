/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.LevelLowering
import Level32Table
import Ribet_928_to_32_Numerical

/-!
# Identification and exclusion at level `32`

The dimension-one and one-entry table theorems are concrete.  They do not
identify a residual eigenform produced by level lowering with `32a1`; that
identification is stated separately before the Kraus exclusion target.
-/

namespace BealMatveevBeal.RibetCurve

/-- The residual coefficient table attached to the recorded `32a1`
coefficients. -/
def newform32a1CoefficientMod13 (l : ℕ) : Option (ZMod 13) :=
  (BealMatveevBeal.Level32Table.newform_32a1_ap l).map
    (fun a : ℤ => (a : ZMod 13))

/-- Exact identification required between a produced residual eigenform and
the recorded `32a1` coefficient table. -/
def ResidualEigenformAtLevel32.Is32a1
    (f : ResidualEigenformAtLevel32) : Prop :=
  ∀ l : ℕ, f.coefficientMod13 l = newform32a1CoefficientMod13 l

/-- Dimension one plus the missing modular-form construction and
multiplicity/normalization arguments should prove this identification. -/
def level_32_eigenform_is_32a1 : Prop :=
  ∀ f : ResidualEigenformAtLevel32, f.Is32a1

/-- Complete Kraus-style trace-mismatch target for every positive gap-3
solution.  This remains uninhabited. -/
def level_32_no_newform_for_Frey_gap3 : Prop :=
  ∀ A B : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13 → 0 < B →
    ∃ l : ℕ, Nat.Prime l ∧ l ≠ 2 ∧ l ≠ 13 ∧
      ¬ l ∣ A ∧ ¬ l ∣ B ∧ ¬ l ∣ B + 3 ∧
      some (BealMatveevBeal.Level32Table.frey_ap l (A % l) (B % l)) ≠
        BealMatveevBeal.Level32Table.newform_32a1_ap l

/-- Level-32 exclusion alias. -/
def level_32_no_newform : Prop :=
  level_32_no_newform_for_Frey_gap3

/-- Residual level-32 exclusion alias. -/
def no_newforms_at_32_mod13 : Prop :=
  level_32_no_newform

#check newform32a1CoefficientMod13
#check ResidualEigenformAtLevel32.Is32a1
#check level_32_eigenform_is_32a1
#check level_32_no_newform_for_Frey_gap3
#check level_32_no_newform
#check no_newforms_at_32_mod13

end BealMatveevBeal.RibetCurve