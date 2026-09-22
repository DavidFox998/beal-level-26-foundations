/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.LFunction
import KolyvaginCurve.Periods
import KolyvaginCurve.KatoKolyvagin
import KolyvaginCurve.FiniteGeneration
import KolyvaginCurve.SelmerExactSequence
import KolyvaginCurve.MordellWeilFintype
import KolyvaginCurve.TwoDescent
import Kolyvagin_MW_Rank0_Numerical

/-!
# Kolyvagin-library scaffold boundary at baseline `43735b3`

The pinned project proves displayed rational `L/Ω` values, their rational
nonvanishing, displayed two-Selmer cardinalities and dimensions, certified
mwrank values, torsion-order arithmetic, discriminants, and the existence
of nonzero rational torsion points.

It does not construct elliptic-curve `L`-functions, real periods, formal
Selmer groups, a Selmer exact sequence, Mordell–Weil finite generation, a
Kato/Kolyvagin theorem, or `Fintype` instances for either rational point
group.

The nonzero torsion points are important: they refute the project's older
`IsRankZero := Subsingleton` predicate while remaining fully compatible
with algebraic rank zero.
-/

namespace BealMatveevBeal.KolyvaginCurve

open BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical
open BealMatveevBeal.TwoDescent_26a1_26
open BealMatveevBeal.BSD_MordellWeil
open BealMatveevBeal.J0_26_BSD_26a1_26b1

/-- Complete already-proved numerical and point-theoretic surface. No
analytic, Selmer, finite-generation, or `Fintype` boundary is used. -/
theorem kolyvagin_numerical_layer_uses_only_proved :
    BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26a1 = (1 / 3 : ℚ) ∧
      BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26b1 = (1 / 7 : ℚ) ∧
      BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26a1 ≠ 0 ∧
      BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26b1 ≠ 0 ∧
      Sel2_card_26a1 = 1 ∧ Sel2_card_26b1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26a1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26b1 = 1 ∧
      certified_mwrank_26a1 = 0 ∧ certified_mwrank_26b1 = 0 ∧
      TorsionOrder_26a1 * TorsionOrder_26b1 = 21 ∧
      curve26a1.Δ = -17576 ∧ curve26b1.Δ = -1664 ∧
      ¬ MordellWeilGroup.IsRankZero curve26a1_Q ∧
      ¬ MordellWeilGroup.IsRankZero curve26b1_Q :=
  kolyvagin_mw_rank0_numerical_surface

#check L_26a1
#check L_26a1_ne_zero
#check L_over_Omega_26a1_eq_one_third
#check MordellWeil_finitely_generated
#check Kolyvagin_L_nonzero_imp_MW_rank_zero
#check twoSelmer_exact_sequence
#check MW_rank_zero_fintype
#check TwoDescent_implies_MW_rank_zero_fintype
#check kolyvagin_numerical_layer_uses_only_proved

#print axioms kolyvagin_numerical_layer_uses_only_proved

end BealMatveevBeal.KolyvaginCurve