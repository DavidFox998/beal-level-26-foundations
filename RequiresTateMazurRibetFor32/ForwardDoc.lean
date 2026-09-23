/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import TateCurve.ClosureContinued
import TateCurve.Neron32_928InertiaQ13
import MazurCurve.X0_13FreyJBorel
import RibetCurve.Ribet32a1KrausA29
import KolyvaginCurve.KolyvaginL_OmegaSel2Fintype
import Conditional32Newform.BridgeForward
import RequiresTateMazurRibetFor32.Doc

/-!
# Integrated forward dependency table for level `32`

This module records the six completed interfaces in their valid construction
order.  Its data remain explicit: no discriminant, valuation, level,
group-order, coefficient, normalized-`L`-value, or Selmer numeral constructs
any of the geometric, local, Galois, automorphic, analytic, or finite-type
boundaries.

The final Conditional-32 step deliberately retains typed conversion functions
from the concrete Mazur, Tate, and Ribet conclusions to the older abstract
bridge propositions.  Those propositions are not definitionally identical.
-/

namespace BealMatveevBeal.RequiresTateMazurRibetFor32

open BealMatveevBeal.Conditional32Newform

/-- The exact six-stage dependency table for the integrated forward close.
Every field is a genuine construction boundary; no inhabitant is manufactured
from the numerical surface. -/
structure RequiresTateMazurRibetForwardData : Prop where
  tateClosure : BealMatveevBeal.TateCurve.TateClosureContinued
  tateNeronInertia :
    BealMatveevBeal.TateCurve.TateNeron32_928InertiaQ13
  mazurX0FreyJBorel :
    BealMatveevBeal.MazurCurve.MazurX0_13FreyJBorel
  ribet32a1Kraus :
    BealMatveevBeal.RibetCurve.Ribet32a1KrausA29
  kolyvaginLValueSelmerFintype :
    BealMatveevBeal.KolyvaginCurve.KolyvaginL_OmegaSel2Fintype
  conditional32 : Conditional32BridgeData

/-- The original bridge hypotheses, in Mazur--Tate--Ribet order, obtained
through the three explicit typed conversions in `Conditional32BridgeData`. -/
theorem three_hypotheses_typed_conversion_forward
    (data : RequiresTateMazurRibetForwardData) :
    BealMatveevBeal.Mazur_X0_13_No_Isogeny.frey_no_rational_13_isogeny ∧
      BealMatveevBeal.Tate_Frey_Conductor_29.Frey_conductor_29_is_Neron ∧
      BealMatveevBeal.Ribet_Level_Lowering_29_to_32.Ribet_928_to_32 :=
  three_hypotheses_forward data.conditional32

/-- Exact dependency table, exposed as a theorem so downstream audits can
inspect the six boundaries without relying on structure projection order. -/
theorem requires_forward_exact_dependency_table
    (data : RequiresTateMazurRibetForwardData) :
    BealMatveevBeal.TateCurve.TateClosureContinued ∧
      BealMatveevBeal.TateCurve.TateNeron32_928InertiaQ13 ∧
      BealMatveevBeal.MazurCurve.MazurX0_13FreyJBorel ∧
      BealMatveevBeal.RibetCurve.Ribet32a1KrausA29 ∧
      BealMatveevBeal.KolyvaginCurve.KolyvaginL_OmegaSel2Fintype ∧
      Conditional32BridgeData :=
  ⟨data.tateClosure, data.tateNeronInertia, data.mazurX0FreyJBorel,
    data.ribet32a1Kraus, data.kolyvaginLValueSelmerFintype,
    data.conditional32⟩

/-- Integrated forward close.  The first five fields preserve the exact
dependency ledger; only the sixth field is passed to the old three-hypothesis
bridge, and only after its explicit typed conversions have been applied. -/
theorem requires_tate_mazur_ribet_forward_doc {A B : ℕ}
    (data : RequiresTateMazurRibetForwardData)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    (BealMatveevBeal.TateCurve.TateClosureContinued ∧
      BealMatveevBeal.TateCurve.TateNeron32_928InertiaQ13 ∧
      BealMatveevBeal.MazurCurve.MazurX0_13FreyJBorel ∧
      BealMatveevBeal.RibetCurve.Ribet32a1KrausA29 ∧
      BealMatveevBeal.KolyvaginCurve.KolyvaginL_OmegaSel2Fintype ∧
      Conditional32BridgeData) ∧ BridgeForwardData A B := by
  rcases three_hypotheses_typed_conversion_forward data with
    ⟨hMazur, hTate, hRibet⟩
  exact ⟨requires_forward_exact_dependency_table data,
    ⟨data.conditional32,
      has_newform_at_level_32_of_assumptions_forward
        hsol hBpos hA hB hC hMazur hTate hRibet⟩⟩

/-- The full displayed numerical surface, integrated only as a parallel
proved result.  It is never used backwards to construct any field of
`RequiresTateMazurRibetForwardData`. -/
theorem numerical_surface_integrated {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    BealMatveevBeal.DarmonMerelFrey4413.freyDiscNat A B =
        16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2 ∧
      Padic.valuation
          (BealMatveevBeal.Tate_I29_Inertia.freyDisc_in_Qp29 A B) =
        26 * (padicValNat 29 (B + 3) : ℤ) ∧
      (13 : ℤ) ∣ Padic.valuation
        (BealMatveevBeal.Tate_I29_Inertia.freyDisc_in_Qp29 A B) ∧
      (928 : ℕ) / 29 = 32 ∧ (32 : ℕ) * 29 = 928 ∧
      (928 : ℕ) ≠ 32 ∧ ¬ (29 : ℕ) ∣ 32 ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧ 48 < 2184 ∧
      BealMatveevBeal.RibetCurve.newform_32a1_ap 29 = some (-10) ∧
      BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26a1 =
        (1 / 3 : ℚ) ∧
      BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26b1 =
        (1 / 7 : ℚ) ∧
      BealMatveevBeal.TwoDescent_26a1_26.Sel2_card_26a1 = 1 ∧
      BealMatveevBeal.TwoDescent_26a1_26.Sel2_card_26b1 = 1 ∧
      (2 : ℕ) ^
          BealMatveevBeal.TwoDescent_26a1_26.Sel2_F2_dim_26a1 =
        1 ∧
      (2 : ℕ) ^
          BealMatveevBeal.TwoDescent_26a1_26.Sel2_F2_dim_26b1 =
        1 :=
  conditional_32_numerical_surface hsol hBpos hA hB hC

#check RequiresTateMazurRibetForwardData
#check three_hypotheses_typed_conversion_forward
#check requires_tate_mazur_ribet_forward_doc
#check requires_forward_exact_dependency_table
#check numerical_surface_integrated

#print axioms three_hypotheses_typed_conversion_forward
#print axioms requires_tate_mazur_ribet_forward_doc
#print axioms requires_forward_exact_dependency_table
#print axioms numerical_surface_integrated

end BealMatveevBeal.RequiresTateMazurRibetFor32