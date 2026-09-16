/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Separate Lake target `BealMatveevBealV25B0Search`.
  Do **not** add `Beal/Matveev/Serre_Large_vs_CM_Small.lean`:
  `.submodules Beal.Matveev` would pull it into the default glob.
  Do **not** import `Beal.Matveev.MatveevThm14General` or
  `BealTrueV25`. Do **not** add a Serre/image axiom.
-/
import BealMatveevBealV25B0Search
import DarmonMerelFrey4413
import SerreImage13
import SerreImageFull
import LLLTargetB8_C1_lower_bound

/-!
# Gap 4: Serre large image vs `32a1` CM small

Inhabited: `32a1` has `j=1728`; `|SL₂(𝔽₁₃)|=2184`; `48 < 2184`.
`card(im ρ_{32a1,13}) ≤ 48` and Serre 1972 open image stay
`def Prop`. `48 < 2184` is not `False` by itself: that needs
an isomorphism `ρ_Frey ≅ ρ_{32a1}` after Ribet, which is Gap 3.

Does **not** mint v25. 0 sorry. 0 new axioms.
-/

namespace BealMatveevBeal.Serre_Large_vs_CM_Small

open BealMatveevBeal.BealMatveevBealV25B0Search
open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.SerreImage13
open BealMatveevBeal.SerreImageFull
open BealMatveevBeal.LLLTargetB8
open BealMatveevBeal.LLLTargetB8C1LowerBound
open Nat

theorem card_SL2_F13_eq_2184 : card_SL2_F13 = 2184 :=
  SerreImageFull.card_SL2_F13_eq_2184

theorem forty_eight_lt_2184 : 48 < 2184 :=
  SerreImageFull.forty_eight_lt_2184

theorem E32a1_j_eq_1728 : curve32a1_j = 1728 :=
  SerreImageFull.E32a1_j_eq_1728

/-- `card(im ρ_{32a1,13}) ≤ 48`. Uninhabited. Numerics
    `j=1728` and `48 < 2184` are theorems. -/
def card_32a1_le_48 : Prop :=
  image_32a1_mod13_small_full

/-- Serre 1972 open image for Frey. Uninhabited. **Not** an axiom. -/
def serre_large_Frey : Prop :=
  serre_large_image_13_full

/-- Image contradiction after a putative `ρ_Frey ≅ ρ_{32a1}`.
    Uninhabited: `omega` on `48 < 2184` does not produce
    `False` without the Galois isomorphism. -/
def contradiction_48_lt_2184 : Prop :=
  card_32a1_le_48 → serre_large_Frey →
    DarmonMerelFrey4413.level_32_no_newform

theorem LLL_and_DarmonMerel_separate :
    LLL_reduces_C1_to_lt_nine ↔
      ∀ {A B : ℕ}, B0_nat ≤ B → A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 :=
  LLL_reduces_C1_to_lt_nine_iff_no_sol_ge_B0

#check card_SL2_F13_eq_2184
#check forty_eight_lt_2184
#check card_32a1_le_48
#check serre_large_Frey
#check contradiction_48_lt_2184
#print axioms forty_eight_lt_2184
#print axioms LLL_and_DarmonMerel_separate

end BealMatveevBeal.Serre_Large_vs_CM_Small
