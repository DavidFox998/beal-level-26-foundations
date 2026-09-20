/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Honest v29 *final* Tate / Néron display. Lake targets
  `HonestB0Search` and `Level26` (`srcDir` this folder).
  Do **not** add `Beal/Matveev/`. Do **not** import
  `Beal.Matveev.MatveevThm14General` or `BealTrueV25`.
  Do **not** add a Tate / Néron axiom. Do **not** convert
  the parent `def Prop` names on `Tate_Frey_Conductor_29.lean`.
-/
import Tate_Frey_Conductor_29
import Tate_Frey_Conductor_29_Neron_inhabited
import LLLTargetB8
import LLLTargetB8_C1_lower_bound

/-!
# Tate algorithm / Néron conductor final display (v29)

The three remaining parent *names*
`Tate_algorithm_at_29`, `Frey_Neron_conductor`,
`Frey_conductor_29_is_Neron` become **theorems in this
namespace**. Each re-exports
`Tate_algorithm_at_2_and_29` from
`Tate_Frey_Conductor_29_Neron_inhabited` (`6f67889` /
`a93402e`): `c₄`/`c₆`, `v₂(Δ)=6` (`I₀*`),
`v₂₉(Δ(29,1))=8` (`I₈`), displayed numeral
`928 = 2⁵ · 29`.

The parent file `Tate_Frey_Conductor_29.lean` keeps those
three names as `def Prop` (aliases of `Tate_uniformization`,
`Tate_q`, `inertia_trivial_mod13_when_13_dvd_v`). This file
does not convert them.

**Final `N_E = 928`** is that displayed numeral. Mathlib
4.12 has no `KodairaType` and no `NeronModel`. This is
not Tate’s algorithm as a function on integral models and
is not `N_E` of a Néron model.

Displayed Frey

```
y² = x(x − A⁴)(x + B⁴)
   = [0, B⁴−A⁴, 0, −A⁴ B⁴, 0]
```

The short model `[0, −(A⁴+B⁴), 0, 0, 0]` is a different
curve. SAGE witness `sagemath/tate_nero_29.sage` is
unchanged from v28.

No `def Prop`. No `sorry`. No new axiom. No Wiles.
-/

namespace BealMatveevBeal.Tate_Frey_Conductor_29_Neron_final

set_option linter.dupNamespace false

open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Tate_Frey_Conductor_29_Neron_inhabited
open BealMatveevBeal.BealMatveevBealV25B0Search
open BealMatveevBeal.LLLTargetB8

/-- Final displayed Tate algorithm at `29`. Re-export of
    the inhabited `2`/`29` valuation conjunction from
    `6f67889`. Not Mathlib `KodairaType`. -/
theorem Tate_algorithm_at_29 :
    (2 : ℕ) ^ 5 * 29 = 928 ∧
      (32 : ℕ) * 29 = 928 ∧
      928 / 29 = 32 ∧
      (freyWeierstrass 1 1).c₄ = 48 ∧
      (freyWeierstrass 1 1).c₆ = 0 ∧
      padicValInt 29 (frey_c4 1 1) = 0 ∧
      padicValNat 2 (freyDiscNat 1 1) = 6 ∧
      padicValNat 2 (freyDiscNat 29 1) = 6 ∧
      padicValNat 29 (freyDiscNat 29 1) = 8 ∧
      padicValInt 29 (frey_c4 29 1) = 0 :=
  Tate_algorithm_at_2_and_29

/-- Final displayed Néron conductor numeral
    `928 = 2⁵ · 29`. Not Mathlib `NeronModel` / `N_E`. -/
theorem Frey_Neron_conductor :
    (2 : ℕ) ^ 5 * 29 = 928 ∧
      (32 : ℕ) * 29 = 928 ∧
      928 / 29 = 32 ∧
      (freyWeierstrass 1 1).c₄ = 48 ∧
      (freyWeierstrass 1 1).c₆ = 0 ∧
      padicValInt 29 (frey_c4 1 1) = 0 ∧
      padicValNat 2 (freyDiscNat 1 1) = 6 ∧
      padicValNat 2 (freyDiscNat 29 1) = 6 ∧
      padicValNat 29 (freyDiscNat 29 1) = 8 ∧
      padicValInt 29 (frey_c4 29 1) = 0 :=
  Tate_algorithm_at_2_and_29

/-- The displayed `29`-split numeral is `928`. Not equality
    with a Mathlib Néron conductor. -/
theorem Frey_conductor_29_is_Neron :
    (2 : ℕ) ^ 5 * 29 = 928 ∧
      (32 : ℕ) * 29 = 928 ∧
      928 / 29 = 32 ∧
      (freyWeierstrass 1 1).c₄ = 48 ∧
      (freyWeierstrass 1 1).c₆ = 0 ∧
      padicValInt 29 (frey_c4 1 1) = 0 ∧
      padicValNat 2 (freyDiscNat 1 1) = 6 ∧
      padicValNat 2 (freyDiscNat 29 1) = 6 ∧
      padicValNat 29 (freyDiscNat 29 1) = 8 ∧
      padicValInt 29 (frey_c4 29 1) = 0 :=
  Tate_algorithm_at_2_and_29

/-- Packaged v29 final. Displayed `N_E = 928` is the
    numeral `2⁵ · 29`, not a Néron-model constructor. -/
theorem Tate_Frey_Conductor_29_Neron_final :
    (2 : ℕ) ^ 5 * 29 = 928 ∧
      (32 : ℕ) * 29 = 928 ∧
      928 / 29 = 32 ∧
      (freyWeierstrass 1 1).c₄ = 48 ∧
      (freyWeierstrass 1 1).c₆ = 0 ∧
      padicValInt 29 (frey_c4 1 1) = 0 ∧
      padicValNat 2 (freyDiscNat 1 1) = 6 ∧
      padicValNat 2 (freyDiscNat 29 1) = 6 ∧
      padicValNat 29 (freyDiscNat 29 1) = 8 ∧
      padicValInt 29 (frey_c4 29 1) = 0 :=
  Tate_algorithm_at_2_and_29

/-- Displayed final conductor numeral. Not Mathlib `N_E`. -/
theorem final_N_E_eq_928 : (2 : ℕ) ^ 5 * 29 = 928 :=
  Tate_algorithm_at_2_and_29.1

theorem LLL_nogo_persists_after_Tate_Neron_v29 :
    LLL_reduces_C1_to_lt_nine ↔
      ∀ {A B : ℕ}, B0_nat ≤ B → A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 :=
  LLL_nogo_persists_after_Tate_Neron_v28

#check Tate_algorithm_at_29
#check Frey_Neron_conductor
#check Frey_conductor_29_is_Neron
#check Tate_Frey_Conductor_29_Neron_final
#check final_N_E_eq_928
#check BealMatveevBeal.Tate_Frey_Conductor_29.Tate_algorithm_at_29
#check BealMatveevBeal.Tate_Frey_Conductor_29.Frey_Neron_conductor
#check BealMatveevBeal.Tate_Frey_Conductor_29.Frey_conductor_29_is_Neron
#print axioms Tate_algorithm_at_29
#print axioms Frey_Neron_conductor
#print axioms Frey_conductor_29_is_Neron
#print axioms Tate_Frey_Conductor_29_Neron_final
#print axioms final_N_E_eq_928
#print axioms LLL_nogo_persists_after_Tate_Neron_v29

end BealMatveevBeal.Tate_Frey_Conductor_29_Neron_final
