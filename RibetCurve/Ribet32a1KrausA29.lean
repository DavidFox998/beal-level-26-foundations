/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import MazurCurve.X0_13FreyJBorel
import RibetCurve.KrausElimination
import TateCurve.Neron32_928InertiaQ13

/-!
# Ribet lowering, `32a1`, and the Kraus `a₂₉` boundary

This module records the Ribet geometry in forward construction order.
Modularity, a geometric residual representation, absolute irreducibility,
local inertia and conductor data, the global Néron conductor, residual
level lowering, identification with `32a1`, and complete bad-reduction
elimination are explicit inputs.

The proved discriminant, valuation, group-cardinality, level, and coefficient
numerals are retained as an independent surface. None is used backwards to
construct geometric or automorphic data.
-/

namespace BealMatveevBeal.RibetCurve

open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Mazur_X0_13_Numerical
open BealMatveevBeal.Ribet_928_to_32_Numerical
open BealMatveevBeal.Tate_I29_Inertia
open BealMatveevBeal.Tate_Frey_Conductor_29_Numerical

set_option genInjectivity false

/-- Constructed data needed to pass from the Frey curve to the unique
recorded residual eigenform at level `32`. -/
structure Ribet32a1Data
    (G : Type*) [Group G] (A B : ℕ)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13) where
  modularity : FreyModularityData A B
  residual : FreyResidualRepresentation13 G A B
  irreducible : residual.IsAbsolutelyIrreducible
  unramifiedAt29 : residual.IsUnramifiedAt29
  localConductor : FreyLocalConductorAt29 A B
  globalNeron : FreyNeronConductorCertificate A B
  residualEigenform : ResidualEigenformAtLevel32
  residualEigenformIs32a1 : residualEigenform.Is32a1

/-- The coefficient identity and the still-required complete elimination of
all bad-reduction residue classes. -/
structure KrausA29Data where
  a29 : newform_32a1_ap 29 = some (-10)
  goodReductionMismatch :
    ∀ {A B : ℕ},
      A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
      ¬ 29 ∣ A → ¬ 29 ∣ B → ¬ 29 ∣ B + 3 →
        frey_ap 29 (A % 29) (B % 29) ≠ (-10 : ℤ)
  completeBadReductionElimination :
    explicit_a29_mod13_complete_Kraus_elimination

/-- Complete uninhabited boundary for the Ribet/`32a1`/Kraus step. -/
def Ribet32a1KrausA29 : Prop :=
  modular_Frey ∧
    residual_Galois_representation_mod13 ∧
    residual_Galois_representation_mod13_absolutely_irreducible ∧
    residual_Galois_representation_mod13_unramified_at_29 ∧
    Frey_local_conductor_exponent_at_29 ∧
    Frey_Neron_conductor_is_32_or_928 ∧
    ribet_level_lowering_29_to_32 ∧
    level_32_eigenform_is_32a1 ∧
    explicit_a29_mod13_complete_Kraus_elimination

/-- Tate's exact Kodaira symbol, projected only from Tate-algorithm data. -/
theorem kodaira_I_26k_forward_tate {A B : ℕ}
    (data : BealMatveevBeal.TateCurve.TateAlgorithmAt29 A B) :
    data.symbol =
      .In (26 * padicValNat 29 (B + 3)) :=
  BealMatveevBeal.TateCurve.kodaira_I_26k_forward data

/-- The `32`/`928` split, projected only from constructed Néron data. -/
theorem neron_32_928_forward_tate {A B : ℕ}
    (data : BealMatveevBeal.TateCurve.FreyNeronConductorData A B) :
    (¬ 29 ∣ A → ¬ 29 ∣ B →
        BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 32) ∧
      (29 ∣ A ∨ 29 ∣ B →
        BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 928) ∧
      (32 : ℕ) * 29 = 928 :=
  BealMatveevBeal.TateCurve.neron_32_928_forward data

/-- Wiles/BCDT modularity projected from constructed Frey modularity data. -/
theorem frey_modularity_forward
    {G : Type*} [Group G] {A B : ℕ}
    {hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13}
    (data : Ribet32a1Data G A B hsol) :
    BealMatveevBeal.SerreImageFull.modularity_Frey_semistable :=
  data.modularity.modularityTheorem

/-- Concrete mod-`13` irreducibility projected from the attached residual
representation. The numerical inequality `48 < 2184` does not prove it. -/
theorem concrete_mod13_irreducibility_forward
    {G : Type*} [Group G] {A B : ℕ}
    {hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13}
    (data : Ribet32a1Data G A B hsol) :
    data.residual.IsAbsolutelyIrreducible :=
  data.irreducible

/-- Local inertia and conductor information projected from constructed data. -/
theorem inertia_local_conductor_forward
    {G : Type*} [Group G] {A B : ℕ}
    {hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13}
    (data : Ribet32a1Data G A B hsol) :
    data.residual.IsUnramifiedAt29 ∧
      data.localConductor.tateAlgorithm.symbol =
        .In (26 * padicValNat 29 (B + 3)) ∧
      data.localConductor.exponent = 1 :=
  ⟨data.unramifiedAt29,
    kodaira_I_26k_forward_tate data.localConductor.tateAlgorithm,
    data.localConductor.exponent_eq_one⟩

/-- The global Néron selector and residual level are projected forward. -/
theorem global_Neron_residual_forward
    {G : Type*} [Group G] {A B : ℕ}
    {hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13}
    (data : Ribet32a1Data G A B hsol) :
    data.globalNeron.conductor =
        BealMatveevBeal.Level928Table.level_after_ribet_29 A B ∧
      data.residualEigenform.level = 32 :=
  ⟨data.globalNeron.conductor_eq_displayed,
    data.residualEigenform.level_eq⟩

/-- Exact forward identification of the produced residual eigenform with the
recorded `32a1` coefficient table. -/
theorem eigenform_32a1_forward
    {G : Type*} [Group G] {A B : ℕ}
    {hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13}
    (data : Ribet32a1Data G A B hsol) :
    data.residualEigenform.Is32a1 :=
  data.residualEigenformIs32a1

/-- At good reduction, the Frey trace at `29` differs from
`a₂₉(32a1) = -10`. -/
theorem kraus_a29_minus10_mismatch_forward
    (data : KrausA29Data)
    {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : ¬ 29 ∣ B + 3) :
    newform_32a1_ap 29 = some (-10) ∧
      frey_ap 29 (A % 29) (B % 29) ≠ (-10 : ℤ) :=
  ⟨data.a29, data.goodReductionMismatch hsol hA hB hC⟩

/-- Complete bad-reduction elimination is projected from its explicit
construction boundary, not inferred from the good-reduction scan. -/
theorem complete_bad_reduction_residue_elimination_forward
    (data : KrausA29Data) :
    explicit_a29_mod13_complete_Kraus_elimination :=
  data.completeBadReductionElimination

/-- Proved numerical surface, kept separate from every geometric,
representation-theoretic, and automorphic construction above. -/
theorem ribet_32a1_kraus_numerical_surface {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    freyDiscNat A B =
        16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2 ∧
      Padic.valuation (freyDisc_in_Qp29 A B) =
        26 * (padicValNat 29 (B + 3) : ℤ) ∧
      (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B) ∧
      (928 : ℕ) / 29 = 32 ∧
      (32 : ℕ) * 29 = 928 ∧
      (928 : ℕ) ≠ 32 ∧
      ¬ (29 : ℕ) ∣ 32 ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧
      48 < 2184 ∧
      newform_32a1_ap 29 = some (-10) := by
  refine ⟨frey_discriminant_nat_formula A B,
    valuation_discriminant_at_29 hsol hBpos hA hB,
    thirteen_dvd_valuation_discriminant_at_29 hsol hBpos hA hB hC,
    BealMatveevBeal.Ribet_928_to_32_Numerical.nine_twenty_eight_div_twenty_nine_numerical,
    BealMatveevBeal.Ribet_928_to_32_Numerical.thirty_two_mul_twenty_nine_numerical, ?_, ?_,
    card_sl2_f13_numerical,
    forty_eight_lt_sl2_f13_order_numerical,
    newform_32a1_a29⟩
  · norm_num
  · norm_num

#check Ribet32a1Data
#check KrausA29Data
#check Ribet32a1KrausA29
#check kodaira_I_26k_forward_tate
#check neron_32_928_forward_tate
#check frey_modularity_forward
#check concrete_mod13_irreducibility_forward
#check inertia_local_conductor_forward
#check global_Neron_residual_forward
#check eigenform_32a1_forward
#check kraus_a29_minus10_mismatch_forward
#check complete_bad_reduction_residue_elimination_forward
#check ribet_32a1_kraus_numerical_surface

#print axioms frey_modularity_forward
#print axioms concrete_mod13_irreducibility_forward
#print axioms inertia_local_conductor_forward
#print axioms global_Neron_residual_forward
#print axioms eigenform_32a1_forward
#print axioms kraus_a29_minus10_mismatch_forward
#print axioms complete_bad_reduction_residue_elimination_forward
#print axioms ribet_32a1_kraus_numerical_surface

end BealMatveevBeal.RibetCurve