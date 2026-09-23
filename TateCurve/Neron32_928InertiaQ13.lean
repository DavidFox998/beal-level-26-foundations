/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import TateCurve.ClosureContinued

/-!
# Néron `32`/`928` and `q^(1/13)` inertia boundary

This module records the next local argument in its valid direction.  For a
displayed solution, Tate uniformization supplies a curve-attached parameter
`q` with

`v₂₉(q) = v₂₉(Δ) = 26 v₂₉(B+3)`.

Tate's algorithm must then return Kodaira symbol `I_(26k)`, where
`k = v₂₉(B+3)`.  A constructed Néron model must identify the local conductor
and the displayed `32`/`928` split, with `928 = 29 * 32`.  Only after the
geometric mod-`13` representation and the cyclotomic action through
`q^(1/13)` have been constructed may divisibility of `v₂₉(q)` by `13` be
used to deduce unramifiedness.

The structures and propositions below keep those construction obligations
explicit.  The proved discriminant valuation, its divisibility, and the
elementary `32`/`928` identities do not construct Tate-algorithm, Néron-model,
or inertia data.
-/

namespace BealMatveevBeal.TateCurve

open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.Tate_Frey_Conductor_29_Numerical

/-- Exact forward projection of the Kodaira symbol supplied by an actual run
of Tate's algorithm.  This does not construct the evidence. -/
theorem kodaira_I_26k_forward {A B : ℕ}
    (data : TateAlgorithmAt29 A B) :
    data.symbol = .In (26 * padicValNat 29 (B + 3)) := by
  simpa [Frey_Kodaira_at_29] using data.symbol_eq

set_option genInjectivity false

/-- A curve-specific package for the forward passage from Tate
uniformization to Tate's algorithm and an identified Néron conductor. -/
structure Neron32_928Data (A B : ℕ)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) where
  uniformization : TateUniformizationData A B hsol
  neron : FreyNeronConductorData A B
  parameter_valuation_eq_discriminant :
    v_29 uniformization.parameter.q =
      Padic.valuation (freyDisc_in_Qp29 A B)

/-- A curve-specific package for the cyclotomic action through `q^(1/13)`.
The formula field is a construction obligation, not a numerical default. -/
structure InertiaQ13Data (A B : ℕ)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) where
  uniformization : TateUniformizationData A B hsol
  q13_cyclotomic_formula : Tate_cyclotomic_inertia_formula

/-- The complete uninhabited boundary for the next Tate step. -/
def TateNeron32_928InertiaQ13 : Prop :=
  Tate_uniformization ∧
    Frey_conductor_29_is_Neron ∧
    Tate_cyclotomic_inertia_formula ∧
    inertia_at_29_trivial_mod13_full

/-- Exact `q`-valuation projection from curve-attached uniformization data. -/
theorem tate_q_valuation_forward {A B : ℕ}
    {hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13}
    (data : TateUniformizationData A B hsol) :
    v_29 data.parameter.q =
      26 * (padicValNat 29 (B + 3) : ℤ) :=
  data.parameter_valuation

/-- Exact forward projections of the identified `32` and `928` branches.
The arithmetic identity is included separately and is not used to construct
the Néron data. -/
theorem neron_32_928_forward {A B : ℕ}
    (data : FreyNeronConductorData A B) :
    (¬ 29 ∣ A → ¬ 29 ∣ B →
        BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 32) ∧
      (29 ∣ A ∨ 29 ∣ B →
        BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 928) ∧
      (32 : ℕ) * 29 = 928 :=
  ⟨data.level32_when_29_coprime, data.level928_when_29_divides,
    thirty_two_mul_twenty_nine_numerical⟩

/-- Numerical surface consumed by the final forward projection. -/
def TateNeron32_928NumericalSurface (A B : ℕ) : Prop :=
  Padic.valuation (freyDisc_in_Qp29 A B) =
      26 * (padicValNat 29 (B + 3) : ℤ) ∧
    (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B) ∧
    (928 : ℕ) / 29 = 32 ∧
    (32 : ℕ) * 29 = 928 ∧
    (928 : ℕ) ≠ 32 ∧
    ¬ (29 : ℕ) ∣ 32

/-- The proved numerical input.  It remains separate from all geometric
construction obligations. -/
theorem tate_neron_32_928_numerical_surface {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    TateNeron32_928NumericalSurface A B := by
  refine ⟨valuation_discriminant_at_29 hsol hBpos hA hB,
    thirteen_dvd_valuation_discriminant_at_29 hsol hBpos hA hB hC,
    nine_twenty_eight_div_twenty_nine_numerical,
    thirty_two_mul_twenty_nine_numerical, ?_, ?_⟩
  · norm_num
  · norm_num

/-- Final forward projection.  It preserves the numerical surface while
projecting mod-`13` unramifiedness from the explicit construction boundary.
No numerical equality is used backwards to inhabit that boundary. -/
theorem tate_mod13_unramifiedness_forward {A B : ℕ}
    (hboundary : TateNeron32_928InertiaQ13)
    (hnumerical : TateNeron32_928NumericalSurface A B) :
    TateNeron32_928NumericalSurface A B ∧
      inertia_at_29_trivial_mod13_full :=
  ⟨hnumerical, hboundary.2.2.2⟩

#check Neron32_928Data
#check InertiaQ13Data
#check TateNeron32_928InertiaQ13
#check kodaira_I_26k_forward
#check tate_q_valuation_forward
#check neron_32_928_forward
#check tate_neron_32_928_numerical_surface
#check tate_mod13_unramifiedness_forward

#print axioms kodaira_I_26k_forward
#print axioms tate_q_valuation_forward
#print axioms neron_32_928_forward
#print axioms tate_neron_32_928_numerical_surface
#print axioms tate_mod13_unramifiedness_forward

end BealMatveevBeal.TateCurve