/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Kolyvagin_MW_Rank0_26a1_26b1

/-!
# Numerical surface for the displayed Kolyvagin / rank-zero branch

This file packages only theorem terms already supported by the pinned
Lean 4.12 / Mathlib surface:

* the displayed rational `L/Ω` values and their nonvanishing;
* the displayed two-Selmer cardinalities and dimensions;
* the displayed certified mwrank values;
* the torsion-order product;
* the displayed discriminants; and
* the formal refutation of the project's `IsRankZero`, which means
  `Subsingleton`, on both curves.

It does not construct an elliptic-curve `L`-function, apply Kato or
Kolyvagin, prove Mordell--Weil finite generation, construct a Selmer exact
sequence, or inhabit `Nonempty (Fintype (MordellWeilGroup E))`.
-/

namespace BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical

open BealMatveevBeal.TwoDescent_26a1_26
open BealMatveevBeal.BSD_MordellWeil
open BealMatveevBeal.J0_26_BSD_26a1_26b1
open BealMatveevBeal.Kolyvagin_MW_Rank0_26a1_26b1

theorem l_over_omega_26a1_one_third_numerical :
    L_over_Omega_26a1 = (1 / 3 : ℚ) :=
  L_over_Omega_26a1_eq_one_third

theorem l_over_omega_26b1_one_seventh_numerical :
    L_over_Omega_26b1 = (1 / 7 : ℚ) :=
  L_over_Omega_26b1_eq_one_seventh

theorem l_over_omega_26a1_nonzero_numerical :
    L_over_Omega_26a1 ≠ 0 :=
  L_over_Omega_26a1_ne_zero_reexport

theorem l_over_omega_26b1_nonzero_numerical :
    L_over_Omega_26b1 ≠ 0 :=
  L_over_Omega_26b1_ne_zero_reexport

theorem sel2_card_26a1_one_numerical :
    Sel2_card_26a1 = 1 :=
  Sel2_card_26a1_eq

theorem sel2_card_26b1_one_numerical :
    Sel2_card_26b1 = 1 :=
  Sel2_card_26b1_eq

theorem sel2_cards_both_one_numerical :
    Sel2_card_26a1 = 1 ∧ Sel2_card_26b1 = 1 :=
  Sel2_card_both_one

theorem two_pow_sel2_dimensions_one_numerical :
    (2 : ℕ) ^ Sel2_F2_dim_26a1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26b1 = 1 :=
  two_pow_sel2_is_one

theorem certified_mwrank_values_zero_numerical :
    certified_mwrank_26a1 = 0 ∧ certified_mwrank_26b1 = 0 :=
  certified_mwrank_display_zero

theorem torsion_orders_product_twenty_one_numerical :
    TorsionOrder_26a1 * TorsionOrder_26b1 = 21 :=
  torsion_3_mul_7_eq_21

theorem curve26a1_discriminant_numerical :
    curve26a1.Δ = -17576 :=
  curve26a1_Δ_reexport

theorem curve26b1_discriminant_numerical :
    curve26b1.Δ = -1664 :=
  curve26b1_Δ_reexport

/-- The rational `26a1` point type is not a subsingleton.
This is compatible with algebraic rank zero and nontrivial torsion. -/
theorem not_subsingleton_rank_zero_26a1 :
    ¬ MordellWeilGroup.IsRankZero curve26a1_Q :=
  not_IsRankZero_26a1_reexport

/-- The rational `26b1` point type is not a subsingleton.
This is compatible with algebraic rank zero and nontrivial torsion. -/
theorem not_subsingleton_rank_zero_26b1 :
    ¬ MordellWeilGroup.IsRankZero curve26b1_Q :=
  not_IsRankZero_26b1_reexport

/-- Package of the inhabited numerical and point-theoretic surface.
It does not inhabit either `MW_rank_zero_26a1_fintype` or
`MW_rank_zero_26b1_fintype`. -/
theorem kolyvagin_mw_rank0_numerical_surface :
    L_over_Omega_26a1 = (1 / 3 : ℚ) ∧
      L_over_Omega_26b1 = (1 / 7 : ℚ) ∧
      L_over_Omega_26a1 ≠ 0 ∧
      L_over_Omega_26b1 ≠ 0 ∧
      Sel2_card_26a1 = 1 ∧
      Sel2_card_26b1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26a1 = 1 ∧
      (2 : ℕ) ^ Sel2_F2_dim_26b1 = 1 ∧
      certified_mwrank_26a1 = 0 ∧
      certified_mwrank_26b1 = 0 ∧
      TorsionOrder_26a1 * TorsionOrder_26b1 = 21 ∧
      curve26a1.Δ = -17576 ∧
      curve26b1.Δ = -1664 ∧
      ¬ MordellWeilGroup.IsRankZero curve26a1_Q ∧
      ¬ MordellWeilGroup.IsRankZero curve26b1_Q :=
  ⟨l_over_omega_26a1_one_third_numerical,
    l_over_omega_26b1_one_seventh_numerical,
    l_over_omega_26a1_nonzero_numerical,
    l_over_omega_26b1_nonzero_numerical,
    sel2_card_26a1_one_numerical,
    sel2_card_26b1_one_numerical,
    two_pow_sel2_dimensions_one_numerical.1,
    two_pow_sel2_dimensions_one_numerical.2,
    certified_mwrank_values_zero_numerical.1,
    certified_mwrank_values_zero_numerical.2,
    torsion_orders_product_twenty_one_numerical,
    curve26a1_discriminant_numerical,
    curve26b1_discriminant_numerical,
    not_subsingleton_rank_zero_26a1,
    not_subsingleton_rank_zero_26b1⟩

#check l_over_omega_26a1_one_third_numerical
#check l_over_omega_26b1_one_seventh_numerical
#check l_over_omega_26a1_nonzero_numerical
#check l_over_omega_26b1_nonzero_numerical
#check sel2_cards_both_one_numerical
#check two_pow_sel2_dimensions_one_numerical
#check certified_mwrank_values_zero_numerical
#check torsion_orders_product_twenty_one_numerical
#check curve26a1_discriminant_numerical
#check curve26b1_discriminant_numerical
#check not_subsingleton_rank_zero_26a1
#check not_subsingleton_rank_zero_26b1
#check kolyvagin_mw_rank0_numerical_surface

#print axioms l_over_omega_26a1_one_third_numerical
#print axioms sel2_cards_both_one_numerical
#print axioms two_pow_sel2_dimensions_one_numerical
#print axioms not_subsingleton_rank_zero_26a1
#print axioms kolyvagin_mw_rank0_numerical_surface

end BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical