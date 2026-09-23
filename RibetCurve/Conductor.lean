/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.GaloisRep
import Ribet_928_to_32_Numerical
import TateCurve.NeronConductor

/-!
# Néron-conductor data

The values `32` and `928` are proved values of a displayed selector.  This
module defines the local conductor and global conductor certificates needed
to identify those values with the Frey curve's actual Néron conductor.
-/

namespace BealMatveevBeal.RibetCurve

open BealMatveevBeal.Ribet_928_to_32_Numerical

/-- Precise local conductor data at `29`.  Multiplicative Kodaira type
`I_(26 v₂₉(B+3))` has conductor exponent one; proving these fields requires
Tate's algorithm and a Néron model. -/
structure FreyLocalConductorAt29 (A B : ℕ) where
  tateAlgorithm : BealMatveevBeal.TateCurve.TateAlgorithmAt29 A B
  exponent : ℕ
  exponent_eq_one : exponent = 1

/-- Global Néron-conductor certificate identifying the actual conductor with
the displayed `32`/`928` selector. -/
structure FreyNeronConductorCertificate (A B : ℕ) where
  local29 : FreyLocalConductorAt29 A B
  tateData : BealMatveevBeal.TateCurve.FreyNeronConductorData A B
  conductor : ℕ
  conductor_eq_displayed :
    conductor =
      BealMatveevBeal.Level928Table.level_after_ribet_29 A B

/-- Missing construction of the local conductor exponent at `29`. -/
def Frey_local_conductor_exponent_at_29 : Prop :=
  ∀ A B : ℕ, Nonempty (FreyLocalConductorAt29 A B)

/-- Missing identification of the actual Néron conductor with the displayed
`32`/`928` split. -/
def Frey_Neron_conductor_is_32_or_928 : Prop :=
  ∀ A B : ℕ, Nonempty (FreyNeronConductorCertificate A B)

/-- Displayed selector value `32`; this is arithmetic, not yet a conductor
theorem. -/
theorem displayed_level_eq_32 {A B : ℕ}
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 32 :=
  displayed_residual_selector_eq_32 hA hB

/-- Displayed selector value `928`; this is arithmetic, not yet a conductor
theorem. -/
theorem displayed_level_eq_928 {A B : ℕ}
    (h : 29 ∣ A ∨ 29 ∣ B) :
    BealMatveevBeal.Level928Table.level_after_ribet_29 A B = 928 :=
  displayed_residual_selector_eq_928 h

theorem conductor_eq_32_of_certificate {A B : ℕ}
    (d : FreyNeronConductorCertificate A B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    d.conductor = 32 := by
  rw [d.conductor_eq_displayed, displayed_level_eq_32 hA hB]

theorem conductor_eq_928_of_certificate {A B : ℕ}
    (d : FreyNeronConductorCertificate A B)
    (h : 29 ∣ A ∨ 29 ∣ B) :
    d.conductor = 928 := by
  rw [d.conductor_eq_displayed, displayed_level_eq_928 h]

#check FreyLocalConductorAt29
#check FreyNeronConductorCertificate
#check Frey_local_conductor_exponent_at_29
#check Frey_Neron_conductor_is_32_or_928
#check conductor_eq_32_of_certificate
#check conductor_eq_928_of_certificate

end BealMatveevBeal.RibetCurve