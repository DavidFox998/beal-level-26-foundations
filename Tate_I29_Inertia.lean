/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Separate Lake target `BealMatveevBealV25B0Search`.
  Do **not** add `Beal/Matveev/Tate_I29_Inertia.lean`:
  `.submodules Beal.Matveev` would pull it into the default glob.
  Do **not** import `Beal.Matveev.MatveevThm14General` or
  `BealTrueV25`. Do **not** add a Tate/inertia axiom: the only
  Darmon–Merel axiom remains
  `BealTrueV25.darmon_merel_4413_axiom` on the default target.
-/
import BealMatveevBealV25B0Search
import DarmonMerelFrey4413
import MazurIrreducibility13
import Inertia29Unramified
import TateGalois
import LLLTargetB8_C1_lower_bound

/-!
# Gap 2: Tate `I₂₉` inertia stays `def Prop`

Numerics from `9030063` / `TateGalois`: `v₂₉(c₄)=0`,
`v₂₉(Δ)=26k`. Mathlib 4.12 has no Tate curve
`E(ℚ̄_ℓ) ≅ ℚ̄_ℓˣ / q^ℤ` and no `InertiaGroup`. No
`axiom inertia_via_cyclo`.

Does **not** mint v25. 0 sorry. 0 new axioms.
-/

namespace BealMatveevBeal.Tate_I29_Inertia

open BealMatveevBeal.BealMatveevBealV25B0Search
open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.MazurIrreducibility13
open BealMatveevBeal.Inertia29Unramified
open BealMatveevBeal.TateGalois
open BealMatveevBeal.LLLTargetB8
open BealMatveevBeal.LLLTargetB8C1LowerBound
open Nat

theorem v29_c4_eq_0_thm {A B : ℕ}
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    padicValInt 29 (frey_c4 A B) = 0 :=
  v29_c4_zero_when_29_nmid_AB hA hB

theorem v29_Delta_26k_thm {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    padicValNat 29 (freyDiscNat A B) =
      26 * padicValNat 29 (B + 3) :=
  v29_Delta_eq_26_vC hsol hBpos hA hB

/-- Intended Mathlib object: Tate uniformisation
    `E(ℚ̄_ℓ) ≅ ℚ̄_ℓˣ / q^ℤ` with `v_ℓ(q)=v_ℓ(Δ)`.
    Not a stub `∃ q, factorization`. **Not** an axiom. -/
def Tate_uniformization : Prop :=
  tate_curve_at_29

/-- Inertia via `χ_cyc^{v(q)}`. Uninhabited. **Not** an axiom. -/
def inertia_via_cyclo : Prop :=
  inertia_via_cyclotomic

/-- `13 ∣ v₂₉(Δ)` ⇒ `ρ_{E,13}(I_{29})=1`. Uninhabited. -/
def inertia_trivial_mod13_when_13_dvd_v : Prop :=
  inertia_at_29_trivial_mod13_full

theorem LLL_nogo_persists_after_Tate_I29 :
    LLL_reduces_C1_to_lt_nine ↔
      ∀ {A B : ℕ}, B0_nat ≤ B → A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 :=
  LLL_reduces_C1_to_lt_nine_iff_no_sol_ge_B0

#check v29_c4_eq_0_thm
#check v29_Delta_26k_thm
#check Tate_uniformization
#check inertia_trivial_mod13_when_13_dvd_v
#print axioms v29_c4_eq_0_thm
#print axioms LLL_nogo_persists_after_Tate_I29

end BealMatveevBeal.Tate_I29_Inertia
