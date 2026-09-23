/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import MazurCurve.X0_13_Moduli
import MazurCurve.FreyJInvariant
import MazurCurve.GaloisRepresentation
import Mazur_X0_13_Numerical

/-!
# Mazur-library boundary at baseline `43735b3`

The pinned environment proves the displayed numerical data: genus `0`, two
cusps, `|SL₂(𝔽₁₃)| = 2184`, `13 = 2² + 3²`, the split-Cartan normalizer
order `288`, `48 < 2184`, and `288 / 48 = 6`.

The library constructs the honest subgroup
`C ≤ E(ℚ)[13]` at the level of Mathlib affine points.  It does not construct
the scheme-theoretic geometric subgroup or a modular curve representing its
point functor.  Consequently the genus numeral is not rebranded as a genus
theorem.  Moreover, genus zero does not say that the two cusps are all
rational points: `X₀(13)` has infinitely many rational points and a rational
Fricke parameter.

Forward development order:

1. promote the point-level `(E,C)` data to a geometric subgroup scheme;
2. construct a modular curve representing that moduli problem and prove its
   genus and cusp theorems;
3. connect the explicit Fricke `j`-map to rational cyclic `13`-isogenies;
4. construct `ρ̄_{E,13}` as the Galois action on geometric torsion;
5. identify reducibility with Borel containment and the Fricke image;
6. prove the Frey-specific global exclusion of all rational parameters; and
7. conclude irreducibility and absence of a rational `13`-isogeny.

The inequality `48 < 2184` cannot replace steps 3–5: it compares displayed
cardinals but does not identify either cardinal with the Frey image.
-/

namespace BealMatveevBeal.MazurCurve

open BealMatveevBeal.Mazur_X0_13_No_Isogeny
open BealMatveevBeal.Mazur_X0_13_Numerical

/-- Complete already-proved numerical surface. No modular-curve or Galois
placeholder is used in its proof. -/
theorem mazur_numerical_layer_uses_only_proved :
    X0_13_genus_nat = 0 ∧ X0_13_cusp_count = 2 ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧
      (2 : ℤ) ^ 2 + 3 ^ 2 = 13 ∧
      2 * (13 - 1) ^ 2 = 288 ∧
      48 < 2184 ∧ 288 / 48 = 6 :=
  mazur_x0_13_numerical_surface

/-- Requested core conjunction, projected from the proved numerical
surface rather than postulated. -/
theorem mazur_core_numerics_use_only_proved :
    X0_13_genus_nat = 0 ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧
      48 < 2184 :=
  ⟨x0_13_genus_zero_numerical,
    card_sl2_f13_numerical,
    forty_eight_lt_sl2_f13_order_numerical⟩

#check X0_13_Point
#check X0_13_RationalPoints
#check torsion13
#check X0_13_ModuliCurve
#check X0_13_has_genus_zero
#check j_of_X0_13
#check frey_j
#check FreyReducibleMod13
#check reducible_13_iff_j_in_image
#check no_t_gives_Frey_j_when_29_dvd_C
#check Mod13GaloisRepresentation
#check Mod13GaloisRepresentation.IsBorelContained
#check FreyMod13Representation
#check rho_Frey_mod13_irreducible
#check mazur_irreducible_13_via_X0_13
#check mazur_inputs_imply_irreducible
#check mazur_numerical_layer_uses_only_proved

#print axioms mazur_numerical_layer_uses_only_proved
#print axioms mazur_core_numerics_use_only_proved

end BealMatveevBeal.MazurCurve