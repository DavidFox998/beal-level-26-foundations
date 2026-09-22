/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import MazurCurve.X0_13_Moduli
import MazurIrreducibility13

/-!
# The Frey `j`-invariant and the Fricke-image boundary

The rational functions are concrete.  The missing statements are written
with all Frey and gap-3 hypotheses explicit; no local valuation alternative
is promoted to the required global parameter exclusion.
-/

namespace BealMatveevBeal.MazurCurve

open BealMatveevBeal.DarmonMerelFrey4413

/-- Exact rational `j = c₄³/Δ` of the displayed Frey model. -/
def frey_j (A B : ℕ) : ℚ :=
  (frey_c4 A B : ℚ) ^ 3 / (freyDiscNat A B : ℚ)

theorem frey_j_eq_existing (A B : ℕ) :
    frey_j A B = BealMatveevBeal.MazurIrreducibility13.frey_j A B :=
  rfl

/-- Frey-specific reducibility boundary before the elliptic-curve
representation has been constructed. -/
def FreyReducibleMod13 (A B : ℕ) : Prop :=
  A ^ 4 + B ^ 4 = (B + 3) ^ 13 ∧
    ¬ BealMatveevBeal.MazurIrreducibility13.rho_Frey_mod13_irreducible

/-- Exact modular-curve theorem required from a construction of the Frey
mod-`13` representation and the `X₀(13)` moduli interpretation. -/
def reducible_13_iff_j_in_image : Prop :=
  ∀ A B : ℕ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
      (FreyReducibleMod13 A B ↔
        ∃ t : ℚ, t ≠ 0 ∧ frey_j A B = j_of_X0_13 t)

/-- Frey-specific global parameter exclusion.  This is stronger than the
proved local alternatives for `v₂₉(t)` and remains uninhabited. -/
def no_t_gives_Frey_j_when_29_dvd_C : Prop :=
  ∀ A B : ℕ, ∀ t : ℚ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
    1 ≤ B →
    ¬ 29 ∣ A →
    ¬ 29 ∣ B →
    29 ∣ B + 3 →
    t ≠ 0 →
      frey_j A B ≠ j_of_X0_13 t

#check frey_j
#check FreyReducibleMod13
#check reducible_13_iff_j_in_image
#check no_t_gives_Frey_j_when_29_dvd_C

end BealMatveevBeal.MazurCurve