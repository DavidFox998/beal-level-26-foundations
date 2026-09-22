/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Mazur_X0_13_No_Isogeny

/-!
# Numerical surface for the Mazur / `X₀(13)` branch

This file packages only theorem terms already proved at the pinned
Lean 4.12 / Mathlib surface:

* the displayed genus and cusp-count numerals;
* the displayed order `13 * 12 * 14 = 2184`;
* the sum-of-two-squares identity for `13`;
* the split-Cartan normalizer numeral `288`;
* `48 < 2184`; and
* `288 / 48 = 6`.

These arithmetic facts do not construct `X₀(13)` as a moduli object, attach
a rational cyclic `13`-isogeny to a Frey curve, define its mod-`13` Galois
representation, or prove that its image is non-Borel.
-/

namespace BealMatveevBeal.Mazur_X0_13_Numerical

open BealMatveevBeal.Mazur_X0_13_No_Isogeny
open BealMatveevBeal.Serre_Large_vs_CM_Small

/-- Displayed genus numeral. This is not a modular-curve genus theorem. -/
theorem x0_13_genus_zero_numerical :
    X0_13_genus_nat = 0 :=
  X0_13_genus_nat_eq

/-- Displayed count of the two standard cusps. This does not classify
`X₀(13)(ℚ)`, which is infinite. -/
theorem x0_13_cusp_count_two_numerical :
    X0_13_cusp_count = 2 :=
  X0_13_cusp_count_eq

theorem x0_13_genus_zero_and_two_cusps_numerical :
    X0_13_genus_nat = 0 ∧ X0_13_cusp_count = 2 :=
  X0_13_genus_zero_and_two_cusps_numerals

/-- Displayed order formula for `SL₂(𝔽₁₃)`. -/
theorem card_sl2_f13_numerical :
    (13 : ℕ) * 12 * 14 = 2184 :=
  card_SL2_F13_numeral

/-- Arithmetic witness that `13` is a sum of two squares. -/
theorem thirteen_sum_two_squares_numerical :
    (2 : ℤ) ^ 2 + 3 ^ 2 = 13 :=
  thirteen_is_sum_of_two_squares

/-- Displayed split-Cartan normalizer order at `13`. -/
theorem split_cartan_normalizer_order_numerical :
    2 * (13 - 1) ^ 2 = 288 :=
  card_normalizer_split_Cartan_13

/-- Numerical inequality only; it is not a theorem about the Frey image. -/
theorem forty_eight_lt_sl2_f13_order_numerical :
    48 < 2184 :=
  forty_eight_lt_2184_reexport

theorem split_cartan_index_six_numerical :
    288 / 48 = 6 :=
  two_eighty_eight_div_forty_eight_reexport

/-- Package of the inhabited numerical surface. -/
theorem mazur_x0_13_numerical_surface :
    X0_13_genus_nat = 0 ∧ X0_13_cusp_count = 2 ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧
      (2 : ℤ) ^ 2 + 3 ^ 2 = 13 ∧
      2 * (13 - 1) ^ 2 = 288 ∧
      48 < 2184 ∧ 288 / 48 = 6 :=
  ⟨x0_13_genus_zero_numerical,
    x0_13_cusp_count_two_numerical,
    card_sl2_f13_numerical,
    thirteen_sum_two_squares_numerical,
    split_cartan_normalizer_order_numerical,
    forty_eight_lt_sl2_f13_order_numerical,
    split_cartan_index_six_numerical⟩

#check x0_13_genus_zero_numerical
#check x0_13_cusp_count_two_numerical
#check x0_13_genus_zero_and_two_cusps_numerical
#check card_sl2_f13_numerical
#check thirteen_sum_two_squares_numerical
#check split_cartan_normalizer_order_numerical
#check forty_eight_lt_sl2_f13_order_numerical
#check split_cartan_index_six_numerical
#check mazur_x0_13_numerical_surface

#print axioms x0_13_genus_zero_numerical
#print axioms card_sl2_f13_numerical
#print axioms thirteen_sum_two_squares_numerical
#print axioms forty_eight_lt_sl2_f13_order_numerical
#print axioms mazur_x0_13_numerical_surface

end BealMatveevBeal.Mazur_X0_13_Numerical