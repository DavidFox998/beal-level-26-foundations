/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import TateCurve.TateParameter
import TateCurve.TateUniformization
import TateCurve.NeronConductor
import TateCurve.InertiaRepresentation
import Tate_Frey_Conductor_29_Numerical

/-!
# Tate-library scaffold boundary at baseline `43735b3`

This root module records the forward development order:

1. construct a curve-attached Tate parameter `Tate_q`;
2. construct the Tate uniformization and identify the full `j(q)` series;
3. run Tate's algorithm and construct the Néron conductor;
4. construct `ρ̄_{E,13}` and prove the cyclotomic inertia formula;
5. derive the local unramified-at-`29` conclusion; and
6. separately handle every odd prime dividing `A * B` before claiming the
   global `residualOddEstimate A B ∣ 32`.

The reverse implication is invalid: an assumed conductor or inertia
conclusion does not construct Tate uniformization.

The displayed expression `q⁻¹ + 744 + 196884q` is only
`tateJTruncation`. It is not a parameter attached to the Frey curve. The
missing construction must define the convergent full Tate `j`-series, invert
it on the `29`-adic open unit disc, build the Weierstrass model of the quotient
`ℚ_29ˣ / q^ℤ`, and prove the resulting curve is isomorphic to the Frey base
change.

Likewise, the displayed Kodaira target `I_(26k)` is not Tate's algorithm.
One must construct an integral minimal model, prove `v₂₉(c₄)=0` in that model,
run the algorithm, and identify the Néron conductor. Only then may the
cyclotomic inertia formula be applied to a constructed residual
representation.

Finally, local theory at `29` cannot prove
`residualOddEstimate A B ∣ 32`: that expression contains every odd prime
dividing `A * B`. Removing those primes needs separate global level-lowering
arguments or a proof that no relevant solution exists.

The numerical theorem below consumes only already-proved facts. It does not
inhabit `tate_curve_at_29`, `Frey_Neron_conductor`,
`inertia_at_29_trivial_mod13_full`, or
`ribet_unramified_at_29_of_dvd_C`.
-/

namespace BealMatveevBeal.TateCurve

open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Level928Table
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.Tate_Frey_Conductor_29_Numerical

/-- The proved local numerical layer, with all hypotheses explicit. -/
theorem tate_numerical_layer_uses_only_proved {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    (freyWeierstrass A B).Δ =
        (16 : ℤ) * (A : ℤ) ^ 8 * (B : ℤ) ^ 8 *
          ((A : ℤ) ^ 4 + (B : ℤ) ^ 4) ^ 2 ∧
      Padic.valuation (freyDisc_in_Qp29 A B) =
        26 * (padicValNat 29 (B + 3) : ℤ) ∧
      (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B) ∧
      level_after_ribet_29 A B = 32 ∧
      (928 : ℕ) / 29 = 32 :=
  ⟨frey_discriminant_formula A B,
    valuation_discriminant_at_29 hsol hBpos hA hB,
    thirteen_dvd_valuation_discriminant_at_29 hsol hBpos hA hB hC,
    displayed_level_eq_32 hA hB,
    nine_twenty_eight_div_twenty_nine_numerical⟩

/-- The proved `928` branch selector, kept separate because its hypothesis
is disjoint from the `29 ∤ A`, `29 ∤ B` hypotheses above. -/
theorem displayed_level_928_uses_only_proved {A B : ℕ}
    (hAB : 29 ∣ A ∨ 29 ∣ B) :
    level_after_ribet_29 A B = 928 :=
  displayed_level_eq_928 hAB

#check TateParameter
#check ℚ_29
#check v_29
#check Frey_Tate_q_at_29
#check TateMultiplicativeQuotient
#check FullTateJSeries
#check TateUniformizationData
#check tate_curve_at_29
#check Frey_Kodaira_at_29
#check TateAlgorithmAt29
#check FreyNeronConductorData
#check Frey_Neron_conductor
#check ResidualRepresentation13
#check inertia_at_29_trivial_mod13_full
#check ribet_unramified_at_29_of_dvd_C
#check tate_numerical_layer_uses_only_proved
#check displayed_level_928_uses_only_proved

#print axioms tate_numerical_layer_uses_only_proved
#print axioms displayed_level_928_uses_only_proved

end BealMatveevBeal.TateCurve