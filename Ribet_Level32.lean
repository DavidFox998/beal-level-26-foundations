/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Separate Lake target `BealMatveevBealV25B0Search`.
  Do **not** add `Beal/Matveev/Ribet_Level32.lean`:
  `.submodules Beal.Matveev` would pull it into the default glob.
  Do **not** import `Beal.Matveev.MatveevThm14General` or
  `BealTrueV25`. Do **not** add modularity / Ribet axioms on
  this target or on default `BealTrueV25`.
-/
import BealMatveevBealV25B0Search
import DarmonMerelFrey4413
import Tate_I29_Inertia
import SerreImageFull
import LLLTargetB8_C1_lower_bound

/-!
# Gap 3: Wiles modularity + Ribet `29·32 → 32`

Both stay `def Prop`. Mathlib 4.12 has no Wiles modularity of
the semistable Frey curve and no Ribet level-lowering. No
`axiom ribet_level_lowering_29_to_32` and no new axiom on
`BealTrueV25`. `main` stays `6247c63`.

Does **not** mint v25. 0 sorry. 0 new axioms.
-/

namespace BealMatveevBeal.Ribet_Level32

open BealMatveevBeal.BealMatveevBealV25B0Search
open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.SerreImageFull
open BealMatveevBeal.LLLTargetB8
open BealMatveevBeal.LLLTargetB8C1LowerBound
open Nat

/-- Wiles: Frey is modular. Alias of displayed
    `modularity_Frey_semistable`. **Not** an axiom. -/
def modular_Frey : Prop :=
  modularity_Frey_semistable

/-- Ribet: unramified at `29` mod `13` ⇒ residual level `32`.
    Uninhabited. **Not** an axiom. -/
def ribet_level_lowering_29_to_32 : Prop :=
  inertia_trivial_mod13_when_13_dvd_v → ribet_lowers_Frey_to_level_32

def modularity_and_ribet_to_32 : Prop :=
  modular_Frey ∧ ribet_level_lowering_29_to_32

theorem LLL_nogo_persists_after_Ribet_Level32 :
    LLL_reduces_C1_to_lt_nine ↔
      ∀ {A B : ℕ}, B0_nat ≤ B → A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 :=
  LLL_reduces_C1_to_lt_nine_iff_no_sol_ge_B0

#check modular_Frey
#check ribet_level_lowering_29_to_32
#print axioms LLL_nogo_persists_after_Ribet_Level32

end BealMatveevBeal.Ribet_Level32
