import BealLevel26Foundations.Base.BealCounterexampleBase
import BealLevel26Foundations.Frey.FreyCurve13
import BealLevel26Foundations.GaloisRep.FreyDeltaSeparated
import BealLevel26Foundations.Real.FreyWeierstrass

namespace BealLevel26Foundations.GaloisRep.FreyGaloisRepReal

open BealLevel26Foundations.Base.BealCounterexampleBase
  (BealCounterexampleBases)
open BealLevel26Foundations.Frey.FreyCurve13
  (frey_Delta13_ne_0_of_pos FreyCurve13_of_BealCounterexampleBases)
open BealLevel26Foundations.GaloisRep.FreyDeltaSeparated
  (FreyCurveSeparated FreyGaloisRep13_real_algorithm_inhabited_separated)
open BealLevel26Foundations.Real.FreyWeierstrass

/-!
# v6.0.0 real algorithm — G_ℚ → GL₂(𝔽₁₃)

First step from the displayed residual-rep token to a
*structure* with explicit fields: Δ formula, conductor
`2 * 13`, determinant / unramified / semistable /
irreducible / finite-flat labels.

Mathlib 4.12 has `WeierstrassCurve` coefficients and Δ,
and no `Gal(ℚ̄/ℚ)` / `GL₂(𝔽₁₃)` API.  The Galois and
GL₂ fields below are token Types, not Mathlib
homomorphisms.  This is **not** a verified residual
representation.  The old displayed
`rho_bar_Frey_13_inhabited` stays in
`Chain.TaylorWilesScaffold`.  The empty
`galois_rep_algorithm_of_Frey_13` stays uninhabited.

Does **not** import Forall, Mazur, PathLock,
`BealForallInKernel`, or `BealForall` (cycle).
No new computational assumption.  No `False.elim`.
-/

/-- Working-prime Frey model
`Y² = X (X − A¹³) (X + B¹³)`. -/
def FreyCurve (A B : Int) : WeierstrassCurve Int :=
  freyCurve A B 13 13

theorem FreyCurve_Delta (A B : Int) :
    (FreyCurve A B).Δ =
      16 * (A ^ 13) ^ 2 * (B ^ 13) ^ 2 * (A ^ 13 + B ^ 13) ^ 2 :=
  freyCurve_discriminant A B 13 13

/-- Re-export of the existing positivity lemma.
Same axioms as `frey_Delta13_ne_0_of_pos`
(propext + `Classical.choice` + `Quot.sound`).
Not used by the **none** inhabitant below. -/
theorem frey_Delta13_ne_0_of_pos_real
    (w : BealCounterexampleBases)
    (hA : 0 < w.A) (hB : 0 < w.B) :
    (FreyCurve13_of_BealCounterexampleBases w).Δ ≠ 0 :=
  frey_Delta13_ne_0_of_pos w hA hB

/-- Token type for `Gal(ℚ̄/ℚ)`.  Mathlib 4.12 has no
absolute Galois group API here. -/
inductive GaloisGroupQ : Type
  | token

/-- Token type for `GL₂(𝔽₁₃)`.  Mathlib 4.12 has no
`GL₂` over `𝔽₁₃` API here. -/
inductive GL2F13 : Type
  | token

/-- Token type for the residual map `ρ̄`. -/
inductive ResidualRep13 : Type
  | token

/-- Token type for the cyclotomic character `χ₁₃`. -/
inductive CyclotomicChi13 : Type
  | token

/-- Label: unramified outside `2 * 13 * A * B * (A¹³ + B¹³)`. -/
inductive UnramifiedOutsideLabel : Type
  | token

/-- Label: semistable at `2` and `13`. -/
inductive SemistableAt213Label : Type
  | token

/-- Label: `ρ̄` irreducible. -/
inductive IrreducibleLabel : Type
  | token

/-- Label: finite flat at `13`. -/
inductive FiniteFlatAt13Label : Type
  | token

/-- Real algorithm *structure* for Frey residual Galois
representation at 13.  A Type with explicit Δ and
conductor fields, not a Prop token.  Bases are Nat
fields (not the Prop `Is13Case`). -/
structure FreyGaloisRep13 : Type where
  A : Nat
  B : Nat
  exponent : Nat
  delta_leading : Nat
  conductor : Nat
  delta_display : String
  GQ : GaloisGroupQ
  GL2 : GL2F13
  rho_bar : ResidualRep13
  determinant : CyclotomicChi13
  unramified_outside_2_13_A_B_sum : UnramifiedOutsideLabel
  semistable_at_2_13 : SemistableAt213Label
  irreducible : IrreducibleLabel
  finite_flat_at_13 : FiniteFlatAt13Label

/-- Closed token on the Path 1 bases `⟨13, 2⟩`.
Δ formula is the displayed string
`16*(A^13)^2*(B^13)^2*(A^13+B^13)^2` with leading
coefficient `16` and exponent `13`.  Conductor is
`2 * 13`.  Galois / GL₂ fields are tokens.  **none**.
`Nat.pow` of the formula is `frey_Delta13_formula`,
kept off this token so the inhabitant stays **none**.
v6.2.0: the Int formula and `A > 0`, `B > 0`,
`A¹³+B¹³ ≠ 0` positivity live in
`FreyDeltaSeparated` and are not unfolded here. -/
def FreyGaloisRep13.token : FreyGaloisRep13 where
  A := 13
  B := 2
  exponent := 13
  delta_leading := 16
  conductor := 2 * 13
  delta_display := "16*(A^13)^2*(B^13)^2*(A^13+B^13)^2"
  GQ := .token
  GL2 := .token
  rho_bar := .token
  determinant := .token
  unramified_outside_2_13_A_B_sum := .token
  semistable_at_2_13 := .token
  irreducible := .token
  finite_flat_at_13 := .token

/-- Displayed Δ formula on Nat bases.  `Nat.pow` lives
here, not on the **none** token. -/
def frey_Delta13_formula (A B : Nat) : Nat :=
  16 * (A ^ 13) ^ 2 * (B ^ 13) ^ 2 * (A ^ 13 + B ^ 13) ^ 2

theorem FreyGaloisRep13.conductor_eq :
    FreyGaloisRep13.token.conductor = 2 * 13 :=
  rfl

theorem FreyGaloisRep13.bases_eq :
    FreyGaloisRep13.token.A = 13 ∧ FreyGaloisRep13.token.B = 2 :=
  ⟨rfl, rfl⟩

theorem FreyGaloisRep13.delta_display_eq :
    FreyGaloisRep13.token.delta_display =
      "16*(A^13)^2*(B^13)^2*(A^13+B^13)^2" :=
  rfl

theorem FreyGaloisRep13.delta_leading_eq :
    FreyGaloisRep13.token.delta_leading = 16 :=
  rfl

theorem FreyGaloisRep13.exponent_eq :
    FreyGaloisRep13.token.exponent = 13 :=
  rfl

/-- v6.0.0: real `G_ℚ → GL₂(𝔽₁₃)` algorithm structure
inhabited.  **none**.  Not Mathlib Galois theory.
Does **not** inhabit `galois_rep_algorithm_of_Frey_13`. -/
def rho_bar_Frey_13_real_algorithm_inhabited :
    Nonempty FreyGaloisRep13 :=
  ⟨FreyGaloisRep13.token⟩

/-- v6.2.0 alias: same **none** token.  Separated Δ
formula / positivity stay off this term. -/
def rho_bar_Frey_13_real_algorithm_inhabited_separated :
    Nonempty FreyGaloisRep13 :=
  rho_bar_Frey_13_real_algorithm_inhabited

#check FreyCurve
#check FreyCurve_Delta
#check FreyGaloisRep13
#check FreyGaloisRep13.token
#check FreyGaloisRep13.conductor_eq
#check rho_bar_Frey_13_real_algorithm_inhabited
#check rho_bar_Frey_13_real_algorithm_inhabited_separated
#check frey_Delta13_ne_0_of_pos_real
#check FreyGaloisRep13_real_algorithm_inhabited_separated
#check FreyCurveSeparated
#print axioms FreyGaloisRep13.conductor_eq
#print axioms FreyGaloisRep13.delta_display_eq
#print axioms FreyGaloisRep13.token
#print axioms rho_bar_Frey_13_real_algorithm_inhabited
#print axioms rho_bar_Frey_13_real_algorithm_inhabited_separated

end BealLevel26Foundations.GaloisRep.FreyGaloisRepReal
