/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.LFunction
import KolyvaginCurve.MordellWeilFintype

/-!
# Kato–Kolyvagin rank-zero boundary

The missing theorem must connect formal analytic nonvanishing
`L(E,1) ≠ 0` to algebraic rank zero and the relevant finiteness statement
for Tate–Shafarevich. A nonzero displayed rational `L/Ω` value is not that
theorem.
-/

namespace BealMatveevBeal.KolyvaginCurve

/-- Kato/Kolyvagin implication for both curves. Uninhabited. -/
def Kolyvagin_L_nonzero_imp_MW_rank_zero : Prop :=
  (L_26a1_ne_zero → MW_rank_zero_26a1_fintype) ∧
    (L_26b1_ne_zero → MW_rank_zero_26b1_fintype)

/-- Missing finiteness conclusion for the relevant Tate–Shafarevich
groups. Kept separate from Mordell–Weil finiteness. -/
def Kolyvagin_TateShafarevich_finite : Prop :=
  BealMatveevBeal.J0_26_BSD_26a1_26b1.Kolyvagin_rank0_of_L_ne_zero

#check Kolyvagin_L_nonzero_imp_MW_rank_zero
#check Kolyvagin_TateShafarevich_finite

end BealMatveevBeal.KolyvaginCurve