/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.FiniteGeneration
import Kolyvagin_MW_Rank0_Numerical
import Mathlib.Data.Fintype.Basic

/-!
# Finite Mordell--Weil groups

For these curves, algebraic rank zero together with finite generation means
that the rational-point group is finite, not that it is a subsingleton.
The existing nonzero torsion points formally refute the older
`IsRankZero := Subsingleton` predicate.
-/

namespace BealMatveevBeal.KolyvaginCurve

open BealMatveevBeal.BSD_MordellWeil

/-- Intended algebraic rank-zero endpoint: a finite type of rational points. -/
def MW_rank_zero_fintype {K : Type*} [Field K]
    (E : WeierstrassCurve K) : Prop :=
  Nonempty (Fintype (ProjectMordellWeilGroup E))

def MW_rank_zero_26a1_fintype : Prop :=
  MW_rank_zero_fintype curve26a1_Q

def MW_rank_zero_26b1_fintype : Prop :=
  MW_rank_zero_fintype curve26b1_Q

def MW_rank_zero_26a1_26b1_fintype : Prop :=
  MW_rank_zero_26a1_fintype ∧ MW_rank_zero_26b1_fintype

theorem not_subsingleton_rank_zero_26a1 :
    ¬ MordellWeilGroup.IsRankZero curve26a1_Q :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.not_subsingleton_rank_zero_26a1

theorem not_subsingleton_rank_zero_26b1 :
    ¬ MordellWeilGroup.IsRankZero curve26b1_Q :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.not_subsingleton_rank_zero_26b1

#check MW_rank_zero_fintype
#check MW_rank_zero_26a1_fintype
#check MW_rank_zero_26b1_fintype
#check MW_rank_zero_26a1_26b1_fintype
#check not_subsingleton_rank_zero_26a1
#check not_subsingleton_rank_zero_26b1

end BealMatveevBeal.KolyvaginCurve