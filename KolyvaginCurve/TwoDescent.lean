/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.SelmerExactSequence
import Kolyvagin_MW_Rank0_Numerical

/-!
# Two-descent endpoint

The equalities `Sel2_card_26a1 = 1` and `Sel2_card_26b1 = 1` are proved
displayed numerals.  The endpoint below requires those numerals to be
identified with cardinalities of constructed Selmer groups before deriving
finite Mordell--Weil groups.
-/

namespace BealMatveevBeal.KolyvaginCurve

open BealMatveevBeal.TwoDescent_26a1_26

/-- Identification between the displayed two-descent cardinality and a
constructed formal Selmer group. -/
structure SelmerCardinalityIdentification
    (E : WeierstrassCurve ℚ) (displayed : ℕ) where
  sequence : TwoSelmerExactSequence.{0, 0} E
  card_eq_displayed : sequence.sel2Card = displayed

/-- Forward-only two-descent implication for both curves.  The exact
sequences, cardinality identifications, and Mordell--Weil finite generation
are all explicit prerequisites. -/
def TwoDescent_implies_MW_rank_zero_fintype : Prop :=
  ∀
    (d26a1 : SelmerCardinalityIdentification
      BealMatveevBeal.BSD_MordellWeil.curve26a1_Q Sel2_card_26a1)
    (d26b1 : SelmerCardinalityIdentification
      BealMatveevBeal.BSD_MordellWeil.curve26b1_Q Sel2_card_26b1),
    d26a1.sequence.sel2Card = Sel2_card_26a1 →
    d26b1.sequence.sel2Card = Sel2_card_26b1 →
    Sel2_card_26a1 = 1 →
    Sel2_card_26b1 = 1 →
    MordellWeil_26a1_finitely_generated →
    MordellWeil_26b1_finitely_generated →
      MW_rank_zero_26a1_fintype ∧ MW_rank_zero_26b1_fintype

#check SelmerCardinalityIdentification
#check TwoDescent_implies_MW_rank_zero_fintype

end BealMatveevBeal.KolyvaginCurve