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
displayed numerals. They do not construct Selmer groups or `Fintype`
instances for rational points.
-/

namespace BealMatveevBeal.KolyvaginCurve

open BealMatveevBeal.TwoDescent_26a1_26

/-- The missing implication from displayed singleton Selmer cardinalities
to finite Mordell–Weil groups. Uninhabited. -/
def TwoDescent_implies_MW_rank_zero_fintype : Prop :=
  (Sel2_card_26a1 = 1 → MW_rank_zero_26a1_fintype) ∧
    (Sel2_card_26b1 = 1 → MW_rank_zero_26b1_fintype)

#check TwoDescent_implies_MW_rank_zero_fintype

end BealMatveevBeal.KolyvaginCurve