/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.MordellWeilFintype
import TwoDescent_26a1_26
import Mathlib.Algebra.Homology.ShortComplex.Basic

/-!
# Two-Selmer exact-sequence boundary

The current `Sel2_card_*` values are displayed natural numbers, not
cardinalities of formal Selmer-group objects. The missing layer must
construct

`0 → E(ℚ)/2E(ℚ) → Sel₂(E) → Sha(E)[2] → 0`

and connect its cardinalities to Mordell–Weil finiteness.
-/

namespace BealMatveevBeal.KolyvaginCurve

/-- Construction and exactness of the two-Selmer sequence for both
displayed curves. Uninhabited. -/
def twoSelmer_exact_sequence : Prop :=
  BealMatveevBeal.Kolyvagin_MW_Rank0_26a1_26b1.TwoDescent_implies_MW_rank_zero_fintype

/-- Missing bridge from a singleton formal two-Selmer group to finite
Mordell–Weil groups. -/
def singleton_twoSelmer_implies_MW_finite : Prop :=
  twoSelmer_exact_sequence

#check twoSelmer_exact_sequence
#check singleton_twoSelmer_implies_MW_finite

end BealMatveevBeal.KolyvaginCurve