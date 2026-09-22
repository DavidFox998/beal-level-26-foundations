/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import Tate_Frey_Conductor_29_Numerical
import Mazur_X0_13_Numerical
import Ribet_928_to_32_Numerical
import Kolyvagin_MW_Rank0_Numerical

/-!
# Final honest numerical bridge at baseline `43735b3`

The bridge begins with the proved displayed Frey discriminant

`Δ = 16 A⁸ B⁸ (A⁴ + B⁴)²`

and packages the actual theorem terms from the four numerical surfaces.
Its level-`32` conclusion is conditional. The exact remaining assumptions are:

* `hMazur : frey_no_rational_13_isogeny`;
* `hTate : Frey_conductor_29_is_Neron`; and
* `hRibet : Ribet_928_to_32`.

`HasNewformAtLevel32` below is an honest proposition-valued evidence record.
It stores these assumptions, the displayed level arithmetic, and the recorded
one-entry level-`32` newform-name table. It is not a Mathlib modular-form
existence theorem, does not inhabit any of the three assumptions, and does not
claim an unconditional level-`32` newform.

Numerical dependencies used here:

* `frey_discriminant_formula`, `valuation_discriminant_at_29`,
  `thirteen_dvd_valuation_discriminant_at_29`, and `displayed_level_eq_32`;
* `nine_twenty_eight_div_twenty_nine_numerical` and
  `thirty_two_mul_twenty_nine_numerical`;
* `x0_13_genus_zero_numerical`, `card_sl2_f13_numerical`, and
  `forty_eight_lt_sl2_f13_order_numerical`;
* `displayed_residual_selector_eq_32`,
  `level_32_full_dimension_one_numerical`,
  `level_32_newform_list_length_one_numerical`,
  `displayed_sturm_bound_eight_numerical`, and
  `explicit_empty_candidate_set_card_zero`; and
* `l_over_omega_26a1_one_third_numerical`,
  `sel2_card_26a1_one_numerical`, and
  `not_subsingleton_rank_zero_26a1`.

Requested build roots:

* `lake exe cache get`;
* `lake build BealMatveevBealV25B0Search`; and
* `bash scripts/verify-matveev-beal.sh`.
-/

namespace BealMatveevBeal.Bridge_43735b3_Honest_Numerical

open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Level928Table
open BealMatveevBeal.Level32Table
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.Mazur_X0_13_No_Isogeny
open BealMatveevBeal.Tate_Frey_Conductor_29
open BealMatveevBeal.Ribet_Level_Lowering_29_to_32
open BealMatveevBeal.TwoDescent_26a1_26
open BealMatveevBeal.BSD_MordellWeil
open BealMatveevBeal.J0_26_BSD_26a1_26b1

namespace TateNum

open BealMatveevBeal.Tate_Frey_Conductor_29_Numerical

/-- The displayed Frey discriminant followed by its proved `29`-adic
valuation and divisibility facts. -/
theorem frey_discriminant_to_valuation_numerical {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    (freyWeierstrass A B).Δ =
        (16 : ℤ) * (A : ℤ) ^ 8 * (B : ℤ) ^ 8 *
          ((A : ℤ) ^ 4 + (B : ℤ) ^ 4) ^ 2 ∧
      Padic.valuation (freyDisc_in_Qp29 A B) =
        26 * (padicValNat 29 (B + 3) : ℤ) ∧
      (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B) :=
  ⟨frey_discriminant_formula A B,
    valuation_discriminant_at_29 hsol hBpos hA hB,
    thirteen_dvd_valuation_discriminant_at_29 hsol hBpos hA hB hC⟩

end TateNum

namespace RibetNum

open BealMatveevBeal.Ribet_928_to_32_Numerical

/-- The displayed `928 = 32 * 29` arithmetic. This theorem does not identify
`928` with a Néron conductor. -/
theorem displayed_928_to_32_numerical :
    (32 : ℕ) * 29 = 928 ∧
      (928 : ℕ) / 29 = 32 ∧
      (928 : ℕ) ≠ 32 ∧
      ¬ 29 ∣ (32 : ℕ) :=
  ⟨thirty_two_mul_twenty_nine_numerical,
    nine_twenty_eight_div_twenty_nine_numerical,
    nine_twenty_eight_ne_thirty_two_numerical,
    twenty_nine_nmid_thirty_two_numerical⟩

end RibetNum

namespace SurfaceNum

open BealMatveevBeal.Mazur_X0_13_Numerical
open BealMatveevBeal.Ribet_928_to_32_Numerical
open BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical

/-- Cross-surface numerical evidence. None of these numerals discharges
Mazur, Tate, Ribet, or Kolyvagin. -/
theorem mazur_ribet_kolyvagin_numerical_evidence :
    X0_13_genus_nat = 0 ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧
      48 < 2184 ∧
      S2_Gamma0_32_dim = 1 ∧
      S2_Gamma0_32_newforms.length = 1 ∧
      (2 : ℕ) * 48 / 12 = 8 ∧
      (∅ : Finset ℕ).card = 0 ∧
      L_over_Omega_26a1 = (1 / 3 : ℚ) ∧
      Sel2_card_26a1 = 1 ∧
      ¬ MordellWeilGroup.IsRankZero curve26a1_Q :=
  ⟨x0_13_genus_zero_numerical,
    card_sl2_f13_numerical,
    forty_eight_lt_sl2_f13_order_numerical,
    level_32_full_dimension_one_numerical,
    level_32_newform_list_length_one_numerical,
    displayed_sturm_bound_eight_numerical,
    explicit_empty_candidate_set_card_zero,
    l_over_omega_26a1_one_third_numerical,
    sel2_card_26a1_one_numerical,
    not_subsingleton_rank_zero_26a1⟩

end SurfaceNum

/-- Conditional evidence record for the final bridge.

The name records the intended endpoint of the conditional chain. The fields
make explicit that this is not an unconditional construction of a modular
form: all three library-scale assumptions remain inputs. -/
structure HasNewformAtLevel32 (A B : ℕ) : Prop where
  frey_discriminant :
    (freyWeierstrass A B).Δ =
      (16 : ℤ) * (A : ℤ) ^ 8 * (B : ℤ) ^ 8 *
        ((A : ℤ) ^ 4 + (B : ℤ) ^ 4) ^ 2
  valuation_at_29 :
    Padic.valuation (freyDisc_in_Qp29 A B) =
      26 * (padicValNat 29 (B + 3) : ℤ)
  thirteen_dvd_valuation :
    (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B)
  displayed_level_32 :
    level_after_ribet_29 A B = 32
  displayed_928_div_29 :
    (928 : ℕ) / 29 = 32
  x0_13_genus_zero :
    X0_13_genus_nat = 0
  card_sl2_f13 :
    (13 : ℕ) * 12 * 14 = 2184
  image_order_inequality :
    48 < 2184
  hMazur :
    frey_no_rational_13_isogeny
  hTate :
    Frey_conductor_29_is_Neron
  hRibet :
    Ribet_928_to_32
  level_32_dimension_one :
    S2_Gamma0_32_dim = 1
  level_32_named_newform_count_one :
    S2_Gamma0_32_newforms.length = 1
  l_over_omega_26a1 :
    L_over_Omega_26a1 = (1 / 3 : ℚ)
  sel2_card_26a1 :
    Sel2_card_26a1 = 1
  rank_zero_subsingleton_refuted_26a1 :
    ¬ MordellWeilGroup.IsRankZero curve26a1_Q

/-- The final bridge is conditional on exactly the three named open
obligations. In particular, this theorem cannot be applied without terms for
Mazur irreducibility, the Néron-conductor identification, and Ribet lowering. -/
theorem has_newform_at_level_32_of_assumptions {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3)
    (hMazur : frey_no_rational_13_isogeny)
    (hTate : Frey_conductor_29_is_Neron)
    (hRibet : Ribet_928_to_32) :
    HasNewformAtLevel32 A B := by
  have hFrey :=
    TateNum.frey_discriminant_to_valuation_numerical
      hsol hBpos hA hB hC
  exact
    { frey_discriminant := hFrey.1
      valuation_at_29 := hFrey.2.1
      thirteen_dvd_valuation := hFrey.2.2
      displayed_level_32 :=
        BealMatveevBeal.Tate_Frey_Conductor_29_Numerical.displayed_level_eq_32
          hA hB
      displayed_928_div_29 := RibetNum.displayed_928_to_32_numerical.2.1
      x0_13_genus_zero :=
        BealMatveevBeal.Mazur_X0_13_Numerical.x0_13_genus_zero_numerical
      card_sl2_f13 :=
        BealMatveevBeal.Mazur_X0_13_Numerical.card_sl2_f13_numerical
      image_order_inequality :=
        BealMatveevBeal.Mazur_X0_13_Numerical.forty_eight_lt_sl2_f13_order_numerical
      hMazur := hMazur
      hTate := hTate
      hRibet := hRibet
      level_32_dimension_one :=
        BealMatveevBeal.Ribet_928_to_32_Numerical.level_32_full_dimension_one_numerical
      level_32_named_newform_count_one :=
        BealMatveevBeal.Ribet_928_to_32_Numerical.level_32_newform_list_length_one_numerical
      l_over_omega_26a1 :=
        BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.l_over_omega_26a1_one_third_numerical
      sel2_card_26a1 :=
        BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.sel2_card_26a1_one_numerical
      rank_zero_subsingleton_refuted_26a1 :=
        BealMatveevBeal.Kolyvagin_MW_Rank0_Numerical.not_subsingleton_rank_zero_26a1 }

#check TateNum.frey_discriminant_to_valuation_numerical
#check RibetNum.displayed_928_to_32_numerical
#check SurfaceNum.mazur_ribet_kolyvagin_numerical_evidence
#check HasNewformAtLevel32
#check has_newform_at_level_32_of_assumptions

#print axioms TateNum.frey_discriminant_to_valuation_numerical
#print axioms RibetNum.displayed_928_to_32_numerical
#print axioms SurfaceNum.mazur_ribet_kolyvagin_numerical_evidence
#print axioms has_newform_at_level_32_of_assumptions

end BealMatveevBeal.Bridge_43735b3_Honest_Numerical