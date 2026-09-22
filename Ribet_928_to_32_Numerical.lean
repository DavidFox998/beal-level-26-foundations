/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Ribet_Level_Lowering_29_to_32

/-!
# Numerical surface for the displayed Ribet `928 → 32` branch

This file packages only theorem terms supported by the pinned project:

* the arithmetic relation between `928`, `29`, and `32`;
* the displayed `32` / `928` branch selector;
* the recorded level-32 dimension and one-entry `32a1` list;
* the recorded `a₂₉(32a1) = -10`;
* the arithmetic used in the displayed Sturm-bound calculation; and
* the cardinality of an explicitly empty finite candidate set.

The project has no formal level-16 modular-form space or Sturm-bound object.
Accordingly, the level-16 and Sturm statements below are explicitly only
numeral identities. Nothing here proves modularity, unramifiedness,
level lowering, existence of a residual level-32 newform, or its exclusion.
-/

namespace BealMatveevBeal.Ribet_928_to_32_Numerical

open BealMatveevBeal.Level32Table
open BealMatveevBeal.Level928Table
open BealMatveevBeal.Ribet_Level_Lowering_29_to_32

theorem nine_twenty_eight_div_twenty_nine_numerical :
    (928 : ℕ) / 29 = 32 :=
  nine_twenty_eight_div_twenty_nine_reexport

theorem thirty_two_mul_twenty_nine_numerical :
    (32 : ℕ) * 29 = 928 :=
  thirty_two_mul_twenty_nine_reexport

theorem nine_twenty_eight_ne_thirty_two_numerical :
    (928 : ℕ) ≠ 32 :=
  nine_twenty_eight_ne_thirty_two_reexport

theorem twenty_nine_nmid_thirty_two_numerical :
    ¬ 29 ∣ (32 : ℕ) :=
  twenty_nine_nmid_thirty_two_reexport

/-- Displayed selector value when `29` divides neither `A` nor `B`.
This is not a residual-conductor theorem. -/
theorem displayed_residual_selector_eq_32 {A B : ℕ}
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    level_after_ribet_29 A B = 32 :=
  conductor_display_32_of_29_nmid_AB hA hB

/-- Displayed selector value when `29 ∣ A` or `29 ∣ B`.
This is not a residual-conductor theorem. -/
theorem displayed_residual_selector_eq_928 {A B : ℕ}
    (h : 29 ∣ A ∨ 29 ∣ B) :
    level_after_ribet_29 A B = 928 :=
  conductor_display_928_of_29_dvd_AB h

/-- Recorded LMFDB full-space dimension numeral at level `32`.
This is not a Mathlib modular-form dimension computation. -/
theorem level_32_full_dimension_one_numerical :
    S2_Gamma0_32_dim = 1 :=
  S2_Gamma0_32_dim_eq_one

/-- The recorded level-32 newform-name list has one entry, `32a1`. -/
theorem level_32_newform_list_length_one_numerical :
    S2_Gamma0_32_newforms.length = 1 := by
  rw [S2_Gamma0_32_newforms_length, S2_Gamma0_32_dim_eq_one]

/-- The recorded level-32 table consists of the one-dimensional display
and a one-entry newform-name list. -/
theorem level_32_full_and_new_dimensions_numerical :
    S2_Gamma0_32_dim = 1 ∧ S2_Gamma0_32_newforms.length = 1 :=
  level_32_table_lmfdb_numerals

/-- Recorded LMFDB coefficient for `32a1`. -/
theorem lmfdb_32a1_a29_numerical :
    newform_32a1_ap 29 = some (-10) :=
  newform_32a1_ap_29

/-- Displayed level-16 dimension numeral. There is no level-16
modular-form-space object in this pinned branch. -/
theorem displayed_level_16_dimension_zero_numeral :
    (0 : ℕ) = 0 :=
  rfl

/-- Numerator arithmetic in the displayed level-32 Sturm calculation. -/
theorem displayed_sturm_index_numerator_numerical :
    (32 : ℕ) * 3 / 2 = 48 := by
  decide

/-- Final arithmetic in the displayed weight-2 Sturm calculation.
This is not an application of a formal Sturm theorem. -/
theorem displayed_sturm_bound_eight_numerical :
    (2 : ℕ) * 48 / 12 = 8 := by
  decide

/-- An explicitly empty finite candidate set has cardinality zero.
This does not prove that the level-32 residual-newform table is empty. -/
theorem explicit_empty_candidate_set_card_zero :
    (∅ : Finset ℕ).card = 0 :=
  rfl

/-- Package of the inhabited Ribet numerical surface. -/
theorem ribet_928_to_32_numerical_surface :
    (928 : ℕ) / 29 = 32 ∧
      (32 : ℕ) * 29 = 928 ∧
      (928 : ℕ) ≠ 32 ∧
      ¬ 29 ∣ (32 : ℕ) ∧
      S2_Gamma0_32_dim = 1 ∧
      S2_Gamma0_32_newforms.length = 1 ∧
      newform_32a1_ap 29 = some (-10) ∧
      (32 : ℕ) * 3 / 2 = 48 ∧
      (2 : ℕ) * 48 / 12 = 8 ∧
      (∅ : Finset ℕ).card = 0 :=
  ⟨nine_twenty_eight_div_twenty_nine_numerical,
    thirty_two_mul_twenty_nine_numerical,
    nine_twenty_eight_ne_thirty_two_numerical,
    twenty_nine_nmid_thirty_two_numerical,
    level_32_full_dimension_one_numerical,
    level_32_newform_list_length_one_numerical,
    lmfdb_32a1_a29_numerical,
    displayed_sturm_index_numerator_numerical,
    displayed_sturm_bound_eight_numerical,
    explicit_empty_candidate_set_card_zero⟩

#check nine_twenty_eight_div_twenty_nine_numerical
#check thirty_two_mul_twenty_nine_numerical
#check nine_twenty_eight_ne_thirty_two_numerical
#check twenty_nine_nmid_thirty_two_numerical
#check displayed_residual_selector_eq_32
#check displayed_residual_selector_eq_928
#check level_32_full_dimension_one_numerical
#check level_32_newform_list_length_one_numerical
#check level_32_full_and_new_dimensions_numerical
#check lmfdb_32a1_a29_numerical
#check displayed_level_16_dimension_zero_numeral
#check displayed_sturm_index_numerator_numerical
#check displayed_sturm_bound_eight_numerical
#check explicit_empty_candidate_set_card_zero
#check ribet_928_to_32_numerical_surface

#print axioms nine_twenty_eight_div_twenty_nine_numerical
#print axioms displayed_residual_selector_eq_32
#print axioms level_32_full_and_new_dimensions_numerical
#print axioms lmfdb_32a1_a29_numerical
#print axioms ribet_928_to_32_numerical_surface

end BealMatveevBeal.Ribet_928_to_32_Numerical