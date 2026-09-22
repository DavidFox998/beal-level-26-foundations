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
# Ribet-library scaffold boundary at baseline `43735b3`

The pinned project proves the arithmetic `928 / 29 = 32`,
`32 * 29 = 928`, `928 ≠ 32`, and `29 ∤ 32`; displayed branch selectors;
recorded level-32 dimensions and table length; the recorded coefficient
`a₂₉(32a1) = -10`; Sturm-bound arithmetic; and the cardinality of an
explicitly empty finite set.

None of these facts proves level lowering. Forward development requires:

1. modularity of the displayed Frey elliptic curve;
2. construction and absolute irreducibility of `ρ̄_{E,13}`;
3. the local Néron conductor and mod-`13` inertia action at `29`;
4. a genuine Ribet theorem producing a residual eigenform at level `32`;
5. identification of that eigenform with the recorded `32a1`; and
6. a complete Kraus trace mismatch covering every gap-3 residue class.

Dimension one does not perform steps 4–6, and `928 / 29 = 32` is only
arithmetic until the displayed levels are identified with conductors.
-/

namespace BealMatveevBeal.RibetCurve

open BealMatveevBeal.Ribet_928_to_32_Numerical

/-- Complete already-proved numerical surface. No modularity, conductor,
Galois, level-lowering, or Kraus placeholder is used in its proof. -/
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

/-- The displayed selector theorem is proved arithmetic, not a conductor
identification. -/
theorem displayed_selector_32_uses_only_proved {A B : ℕ}
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 32 :=
  displayed_residual_selector_eq_32 hA hB

#check modular_Frey
#check residual_Galois_representation_mod13
#check residual_Galois_representation_mod13_absolutely_irreducible
#check residual_Galois_representation_mod13_unramified_at_29
#check Frey_local_conductor_exponent_at_29
#check Frey_Neron_conductor_is_32_or_928
#check ribet_level_lowering_29_to_32
#check level_32_no_newform_for_Frey_gap3
#check explicit_a29_mod13_complete_Kraus_elimination
#check ribet_numerical_layer_uses_only_proved

#print axioms ribet_numerical_layer_uses_only_proved
#print axioms displayed_selector_32_uses_only_proved

end BealMatveevBeal.RibetCurve