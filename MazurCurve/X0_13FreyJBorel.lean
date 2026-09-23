/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import MazurCurve.GaloisRepresentation
import TateCurve.Neron32_928InertiaQ13

/-!
# `X₀(13)`, Frey `j`, and the Borel boundary

This module records the Mazur step in its valid forward order.  Point-level
`X₀(13)` data, the exact Fricke function, curve-attached Frey `j`, and a
constructed Borel/Fricke equivalence must precede the Frey-specific global
exclusion.  The proved cardinal, genus, cusp, discriminant, valuation, and
`32`/`928` numerals do not construct any of those geometric inputs.
-/

namespace BealMatveevBeal.MazurCurve

open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Mazur_X0_13_No_Isogeny
open BealMatveevBeal.Mazur_X0_13_Numerical
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.Tate_Frey_Conductor_29_Numerical
open BealMatveevBeal.TateCurve

set_option genInjectivity false

/-- The two Fricke cusps, kept distinct from the infinitely many rational
points on the genus-zero affine parameter line. -/
inductive FrickeCusp where
  | zero
  | infinity
  deriving DecidableEq, Fintype

/-- Exact cuspidal table for the Fricke coordinate. -/
theorem fricke_cuspidal_table : Fintype.card FrickeCusp = 2 :=
  rfl

/-- Concrete point-level moduli data together with a noncuspidal Fricke
parameter.  This is not a construction of the modular curve. -/
structure X0_13_Moduli_Data where
  point : X0_13_Point ℚ
  frickeParameter : ℚ
  noncuspidal : frickeParameter ≠ 0
  frickeJ :
    j_of_X0_13 frickeParameter =
      (frickeParameter ^ 2 + 5 * frickeParameter + 13) *
        (frickeParameter ^ 4 + 7 * frickeParameter ^ 3 +
          20 * frickeParameter ^ 2 + 19 * frickeParameter + 1) ^ 3 /
            frickeParameter

/-- Frey `j` data attached to point-level `X₀(13)` data. -/
structure FreyJInvariantData (A B : ℕ) where
  moduli : X0_13_Moduli_Data
  j_eq_c4_cubed_over_discriminant :
    frey_j A B = (frey_c4 A B : ℚ) ^ 3 / (freyDiscNat A B : ℚ)

/-- Exact forward Borel/reducibility-to-Fricke-image boundary. -/
def BorelReducibilityForward : Prop :=
  reducible_13_iff_j_in_image

/-- Complete uninhabited boundary for the Frey-specific Mazur step. -/
def MazurX0_13FreyJBorel : Prop :=
  X0_13_has_genus_zero ∧
    BorelReducibilityForward ∧
    no_t_gives_Frey_j_when_29_dvd_C

/-- Point-level moduli and the exact Fricke formula are projected from
constructed data, never from genus or cusp numerals. -/
theorem mazur_x0_13_moduli_forward (data : X0_13_Moduli_Data) :
    Fintype.card FrickeCusp = 2 ∧
      Nonempty (X0_13_Point ℚ) ∧ data.frickeParameter ≠ 0 ∧
      j_of_X0_13 data.frickeParameter =
        (data.frickeParameter ^ 2 + 5 * data.frickeParameter + 13) *
          (data.frickeParameter ^ 4 + 7 * data.frickeParameter ^ 3 +
            20 * data.frickeParameter ^ 2 +
              19 * data.frickeParameter + 1) ^ 3 /
                data.frickeParameter :=
  ⟨fricke_cuspidal_table, ⟨data.point⟩, data.noncuspidal, data.frickeJ⟩

/-- The displayed Frey formula is a field of curve-attached data. -/
theorem frey_j_c4_cubed_over_Delta_forward {A B : ℕ}
    (data : FreyJInvariantData A B) :
    frey_j A B = (frey_c4 A B : ℚ) ^ 3 / (freyDiscNat A B : ℚ) :=
  data.j_eq_c4_cubed_over_discriminant

/-- Once the Borel/Fricke theorem and the Frey-specific global exclusion have
been constructed, absence of a rational cyclic `13`-isogeny follows forward.
No image-cardinality numeral proves either hypothesis. -/
theorem frey_no_rational_13_isogeny_forward
    (hborel : BorelReducibilityForward)
    (hexclude : no_t_gives_Frey_j_when_29_dvd_C) :
    mazur_irreducible_13_theorem :=
  mazur_inputs_imply_irreducible hborel hexclude

/-- Proved arithmetic surface kept separate from the geometric boundary. -/
theorem mazur_X0_13_frey_j_numerical_surface {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    freyDiscNat A B =
        16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2 ∧
      Padic.valuation (freyDisc_in_Qp29 A B) =
        26 * (padicValNat 29 (B + 3) : ℤ) ∧
      (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B) ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧
      48 < 2184 ∧ 288 / 48 = 6 ∧
      (2 : ℤ) ^ 2 + 3 ^ 2 = 13 ∧
      X0_13_genus_nat = 0 ∧ X0_13_cusp_count = 2 ∧
      (928 : ℕ) / 29 = 32 ∧ (32 : ℕ) * 29 = 928 := by
  refine ⟨frey_discriminant_nat_formula A B,
    valuation_discriminant_at_29 hsol hBpos hA hB,
    thirteen_dvd_valuation_discriminant_at_29 hsol hBpos hA hB hC,
    card_sl2_f13_numerical,
    forty_eight_lt_sl2_f13_order_numerical,
    split_cartan_index_six_numerical,
    thirteen_sum_two_squares_numerical,
    x0_13_genus_zero_numerical,
    x0_13_cusp_count_two_numerical,
    nine_twenty_eight_div_twenty_nine_numerical,
    thirty_two_mul_twenty_nine_numerical⟩

#check X0_13_Moduli_Data
#check FrickeCusp
#check fricke_cuspidal_table
#check FreyJInvariantData
#check BorelReducibilityForward
#check MazurX0_13FreyJBorel
#check mazur_x0_13_moduli_forward
#check frey_j_c4_cubed_over_Delta_forward
#check frey_no_rational_13_isogeny_forward
#check mazur_X0_13_frey_j_numerical_surface

#print axioms mazur_x0_13_moduli_forward
#print axioms frey_j_c4_cubed_over_Delta_forward
#print axioms frey_no_rational_13_isogeny_forward
#print axioms mazur_X0_13_frey_j_numerical_surface

end BealMatveevBeal.MazurCurve