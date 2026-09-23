/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Conditional32Newform.Bridge
import MazurCurve.X0_13FreyJBorel
import TateCurve.Neron32_928InertiaQ13
import RibetCurve.Ribet32a1KrausA29
import KolyvaginCurve.KolyvaginL_OmegaSel2Fintype

/-!
# Forward Conditional-32 bridge

This module closes the Conditional-32 interface in construction order:

1. point-level `X₀(13)`/Borel evidence and the Frey-specific exclusion supply
   the Mazur hypothesis;
2. Tate uniformization, Tate's algorithm, the identified Néron conductor,
   `q^(1/13)` inertia, and mod-`13` unramifiedness supply the Tate hypothesis;
3. residual `32a1` data and complete Kraus elimination supply the Ribet
   hypothesis;
4. exactly those three hypotheses inhabit `HasNewformAtLevel32`.

The displayed discriminant, valuation, group-order, coefficient,
`L/Ω`, and two-Selmer numerals remain a separate proved surface. No numeral
constructs geometric, Galois, automorphic, analytic, or finite-type data.
-/

namespace BealMatveevBeal.Conditional32Newform

open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.J0_26_BSD_26a1_26b1
open BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical
open BealMatveevBeal.Level928Table
open BealMatveevBeal.MazurCurve
open BealMatveevBeal.Mazur_X0_13_No_Isogeny
open BealMatveevBeal.Ribet_Level_Lowering_29_to_32
open BealMatveevBeal.Tate_Frey_Conductor_29
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.TwoDescent_26a1_26

/-- The three construction boundaries needed by the original conditional
bridge. Each field remains explicit and uninhabited. -/
structure Conditional32BridgeData : Prop where
  mazurBorel : BealMatveevBeal.MazurCurve.BorelReducibilityForward
  mazurExclusion :
    BealMatveevBeal.MazurCurve.no_t_gives_Frey_j_when_29_dvd_C
  mazurBridge :
    BealMatveevBeal.MazurCurve.mazur_irreducible_13_theorem →
      frey_no_rational_13_isogeny
  tateBoundary : BealMatveevBeal.TateCurve.TateNeron32_928InertiaQ13
  tateBridge :
    BealMatveevBeal.TateCurve.Frey_conductor_29_is_Neron →
      Frey_conductor_29_is_Neron
  ribetBoundary : BealMatveevBeal.RibetCurve.Ribet32a1KrausA29
  ribetBridge :
    BealMatveevBeal.RibetCurve.ribet_level_lowering_29_to_32 →
      Ribet_928_to_32

/-- An actual result of the old three-assumption bridge. -/
structure HasNewformAtLevel32Data (A B : ℕ) : Prop where
  evidence : HasNewformAtLevel32 A B

/-- Complete forward package: construction boundaries followed by the
resulting conditional level-`32` evidence. -/
structure BridgeForwardData (A B : ℕ) : Prop where
  inputs : Conditional32BridgeData
  output : HasNewformAtLevel32Data A B

/-- The Frey-specific Mazur hypothesis follows only from the exact
Borel/Fricke theorem and the global exclusion. -/
theorem frey_no_rational_13_isogeny_forward
    (data : Conditional32BridgeData) :
    frey_no_rational_13_isogeny :=
  data.mazurBridge
    (BealMatveevBeal.MazurCurve.frey_no_rational_13_isogeny_forward
      data.mazurBorel data.mazurExclusion)

/-- The Tate/Néron hypothesis is projected from the full Tate construction
boundary, not from valuation or level arithmetic. -/
theorem Frey_conductor_29_is_Neron_forward
    (data : Conditional32BridgeData) :
    Frey_conductor_29_is_Neron :=
  data.tateBridge data.tateBoundary.2.1

/-- Ribet lowering is projected from the full residual-`32a1` and Kraus
boundary, not from `928 / 29 = 32`. -/
theorem Ribet_928_to_32_forward
    (data : Conditional32BridgeData) :
    Ribet_928_to_32 :=
  data.ribetBridge data.ribetBoundary.2.2.2.2.2.2.1

/-- The three hypotheses of the original bridge, obtained in forward order
from their explicit construction boundaries. -/
theorem three_hypotheses_forward (data : Conditional32BridgeData) :
    frey_no_rational_13_isogeny ∧
      Frey_conductor_29_is_Neron ∧ Ribet_928_to_32 :=
  ⟨frey_no_rational_13_isogeny_forward data,
    Frey_conductor_29_is_Neron_forward data,
    Ribet_928_to_32_forward data⟩

/-- Forward wrapper around the original theorem. Its final three arguments
are the projected Mazur, Tate, and Ribet hypotheses, in that order. -/
theorem has_newform_at_level_32_of_assumptions_forward {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3)
    (hMazur : frey_no_rational_13_isogeny)
    (hTate : Frey_conductor_29_is_Neron)
    (hRibet : Ribet_928_to_32) :
    HasNewformAtLevel32Data A B :=
  ⟨has_newform_at_level_32_of_assumptions
    hsol hBpos hA hB hC hMazur hTate hRibet⟩

/-- Complete forward bridge from the three construction boundaries to the
conditional level-`32` evidence record. -/
theorem conditional_32_bridge_forward {A B : ℕ}
    (data : Conditional32BridgeData)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    BridgeForwardData A B := by
  rcases three_hypotheses_forward data with ⟨hMazur, hTate, hRibet⟩
  exact ⟨data,
    has_newform_at_level_32_of_assumptions_forward
      hsol hBpos hA hB hC hMazur hTate hRibet⟩

/-- Complete numerical surface consumed by this release. It combines only
already-proved numerical theorems and remains independent of every
construction field in `Conditional32BridgeData`. -/
theorem conditional_32_numerical_surface {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    freyDiscNat A B =
        16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2 ∧
      Padic.valuation (freyDisc_in_Qp29 A B) =
        26 * (padicValNat 29 (B + 3) : ℤ) ∧
      (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B) ∧
      (928 : ℕ) / 29 = 32 ∧ (32 : ℕ) * 29 = 928 ∧
      (928 : ℕ) ≠ 32 ∧ ¬ (29 : ℕ) ∣ 32 ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧ 48 < 2184 ∧
      BealMatveevBeal.RibetCurve.newform_32a1_ap 29 = some (-10) ∧
      L_over_Omega_26a1 = (1 / 3 : ℚ) ∧
      L_over_Omega_26b1 = (1 / 7 : ℚ) ∧
      Sel2_card_26a1 = 1 ∧ Sel2_card_26b1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26a1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26b1 = 1 := by
  have hr :=
    BealMatveevBeal.RibetCurve.ribet_32a1_kraus_numerical_surface
      hsol hBpos hA hB hC
  have hk :=
    BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.kolyvagin_mw_rank0_numerical_surface
  exact ⟨hr.1, hr.2.1, hr.2.2.1, hr.2.2.2.1, hr.2.2.2.2.1,
    hr.2.2.2.2.2.1, hr.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.1,
    hr.2.2.2.2.2.2.2.2.1, hr.2.2.2.2.2.2.2.2.2,
    hk.1, hk.2.1, hk.2.2.2.2.1, hk.2.2.2.2.2.1,
    hk.2.2.2.2.2.2.1, hk.2.2.2.2.2.2.2.1⟩

#check Conditional32BridgeData
#check HasNewformAtLevel32Data
#check BridgeForwardData
#check conditional_32_bridge_forward
#check has_newform_at_level_32_of_assumptions_forward
#check three_hypotheses_forward
#check frey_no_rational_13_isogeny_forward
#check Frey_conductor_29_is_Neron_forward
#check Ribet_928_to_32_forward
#check conditional_32_numerical_surface

#print axioms conditional_32_bridge_forward
#print axioms has_newform_at_level_32_of_assumptions_forward
#print axioms three_hypotheses_forward
#print axioms frey_no_rational_13_isogeny_forward
#print axioms Frey_conductor_29_is_Neron_forward
#print axioms Ribet_928_to_32_forward
#print axioms conditional_32_numerical_surface

end BealMatveevBeal.Conditional32Newform