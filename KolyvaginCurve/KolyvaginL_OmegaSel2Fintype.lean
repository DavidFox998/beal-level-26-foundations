/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.KatoKolyvagin
import KolyvaginCurve.TwoDescent
import RibetCurve.Ribet32a1KrausA29

/-!
# Kolyvagin `L/Ω`, two-Selmer, and finite-point boundary

This module records the final Kolyvagin line in forward order. Constructed
`L`-functions and periods are identified with the displayed normalized
values; analytic nonvanishing feeds an explicit Kato--Kolyvagin boundary;
constructed two-Selmer exact sequences and their cardinality identifications
feed an explicit two-descent boundary; and actual `Fintype` witnesses supply
the intended finite Mordell--Weil endpoint.

The displayed values `1/3`, `1/7`, `Sel₂_card = 1`, and `2^dim = 1`, together
with the earlier Tate, Mazur, and Ribet numerics, remain an independent
surface. None is used backwards to construct an analytic function, period,
Galois representation, exact sequence, finite-generation theorem, or
`Fintype` witness.
-/

namespace BealMatveevBeal.KolyvaginCurve

open BealMatveevBeal.BSD_MordellWeil
open BealMatveevBeal.J0_26_BSD_26a1_26b1
open BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.TwoDescent_26a1_26

/-- Curve-attached analytic data and the explicit Kato--Kolyvagin and
finite-generation boundaries. -/
structure KolyvaginL_OmegaData where
  L26a1 : L_26a1
  L26b1 : L_26b1
  period26a1 : RealPeriod curve26a1_Q
  period26b1 : RealPeriod curve26b1_Q
  identified26a1 :
    LOverOmegaIdentification L26a1 period26a1 displayedLOverOmega26a1
  identified26b1 :
    LOverOmegaIdentification L26b1 period26b1 displayedLOverOmega26b1
  sha26a1 : TateShafarevichGroup.{0} curve26a1_Q
  sha26b1 : TateShafarevichGroup.{0} curve26b1_Q
  katoKolyvagin : Kolyvagin_L_nonzero_imp_MW_rank_zero
  finiteGeneration26a1 : MordellWeil_26a1_finitely_generated
  finiteGeneration26b1 : MordellWeil_26b1_finitely_generated

/-- Constructed two-Selmer sequences, exact cardinality identifications, and
the forward singleton-Selmer theorem. -/
structure Sel2CardData where
  identified26a1 :
    SelmerCardinalityIdentification curve26a1_Q Sel2_card_26a1
  identified26b1 :
    SelmerCardinalityIdentification curve26b1_Q Sel2_card_26b1
  singletonForward : singleton_twoSelmer_implies_MW_finite

/-- Actual finite-type witnesses for both rational-point groups. They are
data, not consequences of the displayed cardinality numerals alone. -/
structure FintypeWitnessData where
  witness26a1 : Fintype (ProjectMordellWeilGroup curve26a1_Q)
  witness26b1 : Fintype (ProjectMordellWeilGroup curve26b1_Q)

/-- Complete uninhabited boundary for the normalized-value, Selmer, and
finite Mordell--Weil closure. -/
def KolyvaginL_OmegaSel2Fintype : Prop :=
  Nonempty KolyvaginL_OmegaData ∧
    Nonempty Sel2CardData ∧
    Nonempty FintypeWitnessData

/-- The two exact normalized-value identifications imply formal analytic
nonvanishing. The displayed nonzero rationals are used only after the
analytic functions, periods, and identifications have been constructed. -/
theorem kolyvagin_L_Omega_forward (data : KolyvaginL_OmegaData) :
    L_26a1_ne_zero data.L26a1 ∧ L_26b1_ne_zero data.L26b1 :=
  ⟨nonzeroAtOne_of_identified_normalized_value
      data.identified26a1 displayedLOverOmega26a1_ne_zero,
    nonzeroAtOne_of_identified_normalized_value
      data.identified26b1 displayedLOverOmega26b1_ne_zero⟩

/-- Kato--Kolyvagin and finite generation projected in forward order from
constructed analytic identifications and explicit theorem data. -/
theorem kato_kolyvagin_finite_generation_forward
    (data : KolyvaginL_OmegaData) :
    MordellWeil_26a1_finitely_generated ∧
      MordellWeil_26b1_finitely_generated ∧
      MW_rank_zero_26a1_fintype ∧
      MW_rank_zero_26b1_fintype ∧
      data.sha26a1.IsFinite ∧ data.sha26b1.IsFinite := by
  have hL26a1 : L_26a1_ne_zero data.L26a1 :=
    (kolyvagin_L_Omega_forward data).1
  have hL26b1 : L_26b1_ne_zero data.L26b1 :=
    (kolyvagin_L_Omega_forward data).2
  have hKolyvagin :=
    data.katoKolyvagin data.L26a1 data.L26b1 data.sha26a1 data.sha26b1
      hL26a1 hL26b1
  exact ⟨data.finiteGeneration26a1, data.finiteGeneration26b1,
    hKolyvagin.1, hKolyvagin.2.1, hKolyvagin.2.2.1, hKolyvagin.2.2.2⟩

/-- Constructed Selmer exact sequences and actual finite-type witnesses are
projected separately from their numerical cardinalities. -/
theorem selmer_exact_Fintype_witness_forward
    (selmer : Sel2CardData) (finite : FintypeWitnessData) :
    Nonempty (TwoSelmerExactSequence.{0, 0} curve26a1_Q) ∧
      Nonempty (TwoSelmerExactSequence.{0, 0} curve26b1_Q) ∧
      MW_rank_zero_26a1_fintype ∧ MW_rank_zero_26b1_fintype :=
  ⟨⟨selmer.identified26a1.sequence⟩,
    ⟨selmer.identified26b1.sequence⟩,
    ⟨finite.witness26a1⟩, ⟨finite.witness26b1⟩⟩

/-- The constructed `26a1` normalized value equals the displayed `1/3`. -/
theorem L_over_Omega_one_third_forward (data : KolyvaginL_OmegaData) :
    analyticLOverOmega data.L26a1 data.period26a1 =
      ((1 / 3 : ℚ) : ℂ) := by
  rw [data.identified26a1.normalized_eq,
    displayedLOverOmega26a1_eq_one_third]

/-- The constructed `26b1` normalized value equals the displayed `1/7`. -/
theorem L_over_Omega_one_seventh_forward (data : KolyvaginL_OmegaData) :
    analyticLOverOmega data.L26b1 data.period26b1 =
      ((1 / 7 : ℚ) : ℂ) := by
  rw [data.identified26b1.normalized_eq,
    displayedLOverOmega26b1_eq_one_seventh]

/-- Exact cardinality one for both constructed formal two-Selmer groups. -/
theorem Sel2_card_one_forward (data : Sel2CardData) :
    data.identified26a1.sequence.sel2Card = 1 ∧
      data.identified26b1.sequence.sel2Card = 1 :=
  ⟨data.identified26a1.card_eq_displayed.trans
      sel2_card_26a1_one_numerical,
    data.identified26b1.card_eq_displayed.trans
      sel2_card_26b1_one_numerical⟩

/-- The displayed two-Selmer dimensions satisfy `2^dim = 1`. This remains
numerical and does not construct either formal Selmer group. -/
theorem two_pow_dim_one_forward :
    (2 : ℕ) ^ Sel2_F2_dim_26a1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26b1 = 1 :=
  two_pow_sel2_dimensions_one_numerical

/-- Actual finite-type witnesses coexist with the proved failure of the
older `Subsingleton` encoding of rank zero. -/
theorem Nonempty_Fintype_EQ_forward (data : FintypeWitnessData) :
    MW_rank_zero_26a1_fintype ∧ MW_rank_zero_26b1_fintype ∧
      ¬ MordellWeilGroup.IsRankZero curve26a1_Q ∧
      ¬ MordellWeilGroup.IsRankZero curve26b1_Q :=
  ⟨⟨data.witness26a1⟩, ⟨data.witness26b1⟩,
    not_subsingleton_rank_zero_26a1,
    not_subsingleton_rank_zero_26b1⟩

/-- The Selmer exact-sequence argument reaches finite Mordell--Weil groups
only through the explicit forward theorem and finite-generation inputs. -/
theorem Selmer_rank_zero_forward
    (analytic : KolyvaginL_OmegaData) (selmer : Sel2CardData) :
    MW_rank_zero_26a1_fintype ∧ MW_rank_zero_26b1_fintype := by
  exact selmer.singletonForward
    selmer.identified26a1.sequence selmer.identified26b1.sequence
    (Sel2_card_one_forward selmer).1 (Sel2_card_one_forward selmer).2
    analytic.finiteGeneration26a1 analytic.finiteGeneration26b1

/-- Complete proved numerical surface. The two conjuncts are independent of
all analytic, Selmer, and finite-type construction data above. -/
theorem kolyvagin_L_Omega_Sel2_numerical_surface {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    (L_over_Omega_26a1 = (1 / 3 : ℚ) ∧
      L_over_Omega_26b1 = (1 / 7 : ℚ) ∧
      L_over_Omega_26a1 ≠ 0 ∧ L_over_Omega_26b1 ≠ 0 ∧
      Sel2_card_26a1 = 1 ∧ Sel2_card_26b1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26a1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26b1 = 1 ∧
      certified_mwrank_26a1 = 0 ∧ certified_mwrank_26b1 = 0 ∧
      TorsionOrder_26a1 * TorsionOrder_26b1 = 21 ∧
      curve26a1.Δ = -17576 ∧ curve26b1.Δ = -1664 ∧
      ¬ MordellWeilGroup.IsRankZero curve26a1_Q ∧
      ¬ MordellWeilGroup.IsRankZero curve26b1_Q) ∧
    (BealMatveevBeal.DarmonMerelFrey4413.freyDiscNat A B =
        16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2 ∧
      Padic.valuation (freyDisc_in_Qp29 A B) =
        26 * (padicValNat 29 (B + 3) : ℤ) ∧
      (13 : ℤ) ∣ Padic.valuation
        (freyDisc_in_Qp29 A B) ∧
      (928 : ℕ) / 29 = 32 ∧ (32 : ℕ) * 29 = 928 ∧
      (928 : ℕ) ≠ 32 ∧ ¬ (29 : ℕ) ∣ 32 ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧ 48 < 2184 ∧
      BealMatveevBeal.RibetCurve.newform_32a1_ap 29 = some (-10)) :=
  ⟨kolyvagin_mw_rank0_numerical_surface,
    BealMatveevBeal.RibetCurve.ribet_32a1_kraus_numerical_surface
      hsol hBpos hA hB hC⟩

#check KolyvaginL_OmegaData
#check Sel2CardData
#check FintypeWitnessData
#check KolyvaginL_OmegaSel2Fintype
#check kolyvagin_L_Omega_forward
#check kato_kolyvagin_finite_generation_forward
#check selmer_exact_Fintype_witness_forward
#check L_over_Omega_one_third_forward
#check L_over_Omega_one_seventh_forward
#check Sel2_card_one_forward
#check two_pow_dim_one_forward
#check Nonempty_Fintype_EQ_forward
#check Selmer_rank_zero_forward
#check kolyvagin_L_Omega_Sel2_numerical_surface

#print axioms kolyvagin_L_Omega_forward
#print axioms kato_kolyvagin_finite_generation_forward
#print axioms selmer_exact_Fintype_witness_forward
#print axioms L_over_Omega_one_third_forward
#print axioms L_over_Omega_one_seventh_forward
#print axioms Sel2_card_one_forward
#print axioms two_pow_dim_one_forward
#print axioms Nonempty_Fintype_EQ_forward
#print axioms Selmer_rank_zero_forward
#print axioms kolyvagin_L_Omega_Sel2_numerical_surface

end BealMatveevBeal.KolyvaginCurve