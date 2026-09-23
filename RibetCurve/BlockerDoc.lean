/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.Modularity
import RibetCurve.GaloisRep
import RibetCurve.Conductor
import RibetCurve.LevelLowering
import RibetCurve.Newform32
import RibetCurve.KrausElimination
import Ribet_928_to_32_Numerical

/-!
# Ribet-library boundary at baseline `43735b3`

The pinned project proves `928 / 29 = 32`, `32 * 29 = 928`, `928 ≠ 32`,
`29 ∤ 32`, the displayed branch selectors, level-32 dimension one, the
one-entry newform list, `a₂₉(32a1) = -10`, Sturm-bound arithmetic, and the
cardinality of an explicitly empty finite set.

Those facts are consumed below but do not prove level lowering.  The forward
construction order is:

1. construct the displayed Frey elliptic curve and prove Wiles/BCDT
   modularity;
2. attach `ρ̄_{E,13}` to geometric torsion and prove absolute irreducibility
   from the two explicit Mazur inputs;
3. run Tate's algorithm, construct the Néron model, and identify the local
   conductor exponent and the displayed global levels `32` and `928`;
4. prove the cyclotomic inertia formula and mod-`13` unramifiedness at `29`;
5. prove a genuine Ribet theorem producing residual eigenform data at level
   `32`;
6. identify that eigenform with `32a1`; and
7. complete the Kraus trace elimination for every gap-3 residue class,
   including bad-reduction classes with `29 ∣ A B (B+3)`.

Thus `928 / 29 = 32`, dimension one, and the one-entry table are necessary
numerical inputs, not substitutes for steps 1–7.
-/

namespace BealMatveevBeal.RibetCurve

open BealMatveevBeal.Ribet_928_to_32_Numerical

/-- Complete proved numerical surface.  No modularity, conductor, Galois,
level-lowering, or Kraus boundary is used in its proof. -/
theorem ribet_numerical_layer_uses_only_proved :
    (928 : ℕ) / 29 = 32 ∧
      (32 : ℕ) * 29 = 928 ∧
      (928 : ℕ) ≠ 32 ∧
      ¬ 29 ∣ (32 : ℕ) ∧
      BealMatveevBeal.Level32Table.S2_Gamma0_32_dim = 1 ∧
      BealMatveevBeal.Level32Table.S2_Gamma0_32_newforms.length = 1 ∧
      BealMatveevBeal.Level32Table.newform_32a1_ap 29 = some (-10) ∧
      (32 : ℕ) * 3 / 2 = 48 ∧
      (2 : ℕ) * 48 / 12 = 8 ∧
      (∅ : Finset ℕ).card = 0 :=
  ribet_928_to_32_numerical_surface

/-- The selector theorem is arithmetic, not a conductor identification. -/
theorem displayed_selector_32_uses_only_proved {A B : ℕ}
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 32 :=
  displayed_residual_selector_eq_32 hA hB

#check FreyModularityData
#check modular_Frey
#check FreyResidualRepresentation13
#check FreyResidualRepresentation13.IsAbsolutelyIrreducible
#check FreyResidualRepresentation13.IsUnramifiedAt29
#check absolutely_irreducible_of_Mazur_inputs
#check FreyLocalConductorAt29
#check FreyNeronConductorCertificate
#check Frey_local_conductor_exponent_at_29
#check Frey_Neron_conductor_is_32_or_928
#check ResidualEigenformAtLevel32
#check ribet_level_lowering_29_to_32
#check level_32_eigenform_is_32a1
#check level_32_no_newform_for_Frey_gap3
#check frey_a29_mismatch_at_good_reduction
#check explicit_a29_mod13_complete_Kraus_elimination
#check ribet_numerical_layer_uses_only_proved

#print axioms newform_32a1_a29
#print axioms frey_a29_mismatch_at_good_reduction
#print axioms ribet_numerical_layer_uses_only_proved
#print axioms displayed_selector_32_uses_only_proved

end BealMatveevBeal.RibetCurve