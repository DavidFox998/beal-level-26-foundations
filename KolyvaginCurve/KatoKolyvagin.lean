/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.Periods
import KolyvaginCurve.MordellWeilFintype

/-!
# Kato--Kolyvagin rank-zero boundary

The theorem below starts from formal analytic nonvanishing `L(E,1) ≠ 0`.
It does not use a displayed rational as a substitute.  Mordell--Weil
finiteness and Tate--Shafarevich finiteness are separate conclusions.
-/

namespace BealMatveevBeal.KolyvaginCurve

/-- Typed Tate--Shafarevich group data for a displayed elliptic curve. -/
structure TateShafarevichGroup (E : WeierstrassCurve ℚ) where
  group : AddCommGrp

/-- Finiteness of a constructed Tate--Shafarevich group. -/
def TateShafarevichGroup.IsFinite {E : WeierstrassCurve ℚ}
    (sha : TateShafarevichGroup E) : Prop :=
  Nonempty (Fintype sha.group)

/-- Kato/Kolyvagin specialized to both curves.  The function objects and
Tate--Shafarevich groups are explicit inputs, and every conclusion is
forward from analytic nonvanishing. -/
def Kolyvagin_L_nonzero_imp_MW_rank_zero : Prop :=
  ∀ (L26a1 : L_26a1) (L26b1 : L_26b1)
    (sha26a1 : TateShafarevichGroup.{0}
      BealMatveevBeal.BSD_MordellWeil.curve26a1_Q)
    (sha26b1 : TateShafarevichGroup.{0}
      BealMatveevBeal.BSD_MordellWeil.curve26b1_Q),
    L_26a1_ne_zero L26a1 →
    L_26b1_ne_zero L26b1 →
      MW_rank_zero_26a1_fintype ∧
      MW_rank_zero_26b1_fintype ∧
      sha26a1.IsFinite ∧
      sha26b1.IsFinite

/-- Separate projection of the Tate--Shafarevich finiteness conclusion. -/
def Kolyvagin_TateShafarevich_finite : Prop :=
  ∀ (L26a1 : L_26a1) (L26b1 : L_26b1)
    (sha26a1 : TateShafarevichGroup.{0}
      BealMatveevBeal.BSD_MordellWeil.curve26a1_Q)
    (sha26b1 : TateShafarevichGroup.{0}
      BealMatveevBeal.BSD_MordellWeil.curve26b1_Q),
    L_26a1_ne_zero L26a1 →
    L_26b1_ne_zero L26b1 →
      sha26a1.IsFinite ∧ sha26b1.IsFinite

#check TateShafarevichGroup
#check TateShafarevichGroup.IsFinite
#check Kolyvagin_L_nonzero_imp_MW_rank_zero
#check Kolyvagin_TateShafarevich_finite

end BealMatveevBeal.KolyvaginCurve