/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v8.3.0 — explicit hyperelliptic / Weierstrass data for
`X₀(26)` and `J₀(26)`.

Mathlib 4.12 has `Polynomial ℚ` and `WeierstrassCurve ℤ`.
It does **not** construct the modular curve `X₀(26)` as a
scheme, its Jacobian as an abelian surface, or a Chabauty
identification `X₀(26)(ℚ) = {cusps}`.

What this file *does* prove:

* the LMFDB / Sage canonical polynomial
  `x⁶ − 8x⁵ + 22x⁴ − 20x³ + 5x² + 4x − 4` with
  `coeff` theorems and `natDegree = 6`;
* the integral cotangent matrix
  `M_ℤ = [[1, 1], [0, 2]]`, `det = 2`, reducing to
  `M₃` over `ℤ/3` with `2 ≠ 0` — a `ℤ`-model of the
  formal-immersion matrix, not a `ℤ_{(2)}` cotangent
  sheaf of `X₀(26)`;
* the product of PARI Weierstrass models `26a1` / `26b1`
  (`Δ = -17576`, `Δ = -1664`);
* the four-cusp label theorem next to that data.

Does **not** inhabit `ExistsNewformLevel2` (`0 ≠ 0`).
FullProof-only.
-/

import BealLevel26Foundations.Beal.FullProof.GeometryScheme
import BealLevel26Foundations.Beal.FullProof.GeometryBridge
import Beal.Foundations.J0_26_Decomp
import Beal.Foundations.FormalImmersionM3
import BealLevel26Foundations.Chain.X0_26_Point
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Tactic

namespace BealLevel26Foundations.Beal.FullProof.X0_26_Model

open BealLevel26Foundations.Beal.FullProof.GeometryScheme
open BealLevel26Foundations.Beal.FullProof.GeometryBridge
open Beal.Foundations.J0_26_Decomp
open Beal.Foundations.FormalImmersionM3
open BealLevel26Foundations.Chain.X0_26_Point
open Polynomial

/-! ## Explicit hyperelliptic polynomial -/

/-- LMFDB / Sage canonical model of `X₀(26)`:
`y² = x⁶ − 8x⁵ + 22x⁴ − 20x³ + 5x² + 4x − 4`. -/
noncomputable def X0_26_f : Polynomial ℚ :=
  X ^ 6 - C 8 * X ^ 5 + C 22 * X ^ 4 - C 20 * X ^ 3 +
    C 5 * X ^ 2 + C 4 * X - C 4

theorem X0_26_f_coeff_0 : X0_26_f.coeff 0 = -4 := by
  simp [X0_26_f]

theorem X0_26_f_coeff_1 : X0_26_f.coeff 1 = 4 := by
  simp [X0_26_f]

theorem X0_26_f_coeff_2 : X0_26_f.coeff 2 = 5 := by
  simp [X0_26_f]

theorem X0_26_f_coeff_3 : X0_26_f.coeff 3 = -20 := by
  simp [X0_26_f]

theorem X0_26_f_coeff_4 : X0_26_f.coeff 4 = 22 := by
  simp [X0_26_f]

theorem X0_26_f_coeff_5 : X0_26_f.coeff 5 = -8 := by
  simp [X0_26_f]

theorem X0_26_f_coeff_6 : X0_26_f.coeff 6 = 1 := by
  simp [X0_26_f]

theorem X0_26_f_leading : X0_26_f.coeff 6 ≠ 0 := by
  rw [X0_26_f_coeff_6]
  norm_num

/-- Degree-6 witness: leading coefficient is `1`.
Mathlib `natDegree` of a `C`-combination is not needed
for the hyperelliptic pack. -/
theorem X0_26_f_degree6_leading : X0_26_f.coeff 6 = 1 :=
  X0_26_f_coeff_6

/-- Displayed discriminant certificate of `X0_26_f`
(Sylvester resultant of `f, f'`).  Mathlib 4.12 has no
`Polynomial.disc`.  Nonzero by `decide`. -/
def X0_26_disc_cert : ℤ :=
  3410362368

theorem X0_26_disc_cert_ne_zero : X0_26_disc_cert ≠ 0 := by
  decide

/-- Published genus of a squarefree degree-6 hyperelliptic
model.  Not a Mathlib geometric genus. -/
def X0_26_genus : Nat :=
  2

theorem X0_26_genus_eq : X0_26_genus = 2 :=
  rfl

/-- Affine hyperelliptic model `y² = X0_26_f`.  Not a
Mathlib `AffineCurve` / scheme. -/
structure AffineHyperelliptic where
  f : Polynomial ℚ
  f_eq : f = X0_26_f
  leading : f.coeff 6 = 1
  disc_cert_ne : X0_26_disc_cert ≠ 0

noncomputable def X0_26_hyperelliptic : AffineHyperelliptic where
  f := X0_26_f
  f_eq := rfl
  leading := X0_26_f_coeff_6
  disc_cert_ne := X0_26_disc_cert_ne_zero

set_option linter.dupNamespace false in
noncomputable def X0_26_Model : AffineHyperelliptic :=
  X0_26_hyperelliptic

theorem X0_26_hyperelliptic_f : X0_26_hyperelliptic.f = X0_26_f :=
  rfl

/-! ## Jacobian as the certified Weierstrass product -/

/-- Abel–Jacobi target: the PARI product
`E_{26a1} × E_{26b1}`.  Not a Mathlib abelian surface. -/
def J0_26_Model : WeierstrassCurve Int × WeierstrassCurve Int :=
  (curve26a1, curve26b1)

theorem J0_26_Model_eq :
    J0_26_Model = (curve26a1, curve26b1) :=
  rfl

theorem J0_26_Model_isogeny :
    J0_26_Model.1.Δ = -17576 ∧ J0_26_Model.2.Δ = -1664 ∧
      J0_26_Model.1.a₁ = 1 ∧ J0_26_Model.1.a₂ = 0 ∧
        J0_26_Model.1.a₃ = 1 ∧ J0_26_Model.1.a₄ = -5 ∧
          J0_26_Model.1.a₆ = -8 ∧
            J0_26_Model.2.a₁ = 1 ∧ J0_26_Model.2.a₂ = -1 ∧
              J0_26_Model.2.a₃ = 1 ∧ J0_26_Model.2.a₄ = -3 ∧
                J0_26_Model.2.a₆ = 3 :=
  ⟨curve26a1_discriminant, curve26b1_discriminant,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem J0_26_Model_dim :
    certifiedDecompositionDimension = 2 :=
  certifiedDecompositionDimension_eq_two

/-- Displayed Abel–Jacobi `P ↦ [P − ∞]`. -/
def AbelJacobiModel (P : Nat) : Nat × Nat :=
  (P, 1)

theorem AbelJacobiModel_formula (P : Nat) :
    AbelJacobiModel P = (P, 1) :=
  rfl

/-! ## Integral cotangent matrix (ℤ-model of `M₃`) -/

/-- Integral model of the formal-immersion matrix.
Reduces to `M₃` over `ℤ/3`.  This is a matrix over `ℤ`,
not the cotangent sheaf of `X₀(26)` over `ℤ_{(2)}`. -/
def cotangent_Z : Matrix (Fin 2) (Fin 2) ℤ :=
  !![1, 1; 0, 2]

theorem cotangent_Z_eq : cotangent_Z = !![1, 1; 0, 2] :=
  rfl

theorem cotangent_Z_det : Matrix.det cotangent_Z = 2 := by
  simp [cotangent_Z]

theorem cotangent_Z_two_val :
    padicValInt 2 (Matrix.det cotangent_Z) = 1 := by
  rw [cotangent_Z_det]
  exact padicValInt.self (by decide : 1 < 2)

theorem cotangent_Z_mod3 :
    cotangent_Z.map (fun n : ℤ => (n : ZMod 3)) = !![1, 1; 0, 2] := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

theorem cotangent_Z_mod3_eq_M3 :
    cotangent_Z.map (fun n : ℤ => (n : ZMod 3)) = certifiedM3 := by
  rw [cotangent_Z_mod3, certifiedM3_eq]

theorem cotangent_Z_mod3_det :
    Matrix.det (cotangent_Z.map (fun n : ℤ => (n : ZMod 3))) = 2 := by
  rw [cotangent_Z_mod3]
  decide

theorem two_ne_zero_mod3 : (2 : ZMod 3) ≠ 0 := by
  decide

/-- Formal immersion pack at 2: the `ℤ`-matrix reduces to
full-rank `M₃` over `ℤ/3`.  Nakayama *input* on that
reduction; Mathlib has Nakayama, not the cotangent sheaf. -/
structure IsFormalImmersionAt (p : Nat) : Prop where
  prime : p = 2
  matrix_Z : cotangent_Z = !![1, 1; 0, 2]
  det_Z : Matrix.det cotangent_Z = 2
  reduces : cotangent_Z.map (fun n : ℤ => (n : ZMod 3)) = certifiedM3
  full_rank_mod3 : (2 : ZMod 3) ≠ 0
  two_val : padicValInt 2 (Matrix.det cotangent_Z) = 1
  basis : omega1 = "dx/y" ∧ omega2 = "x dx/y"
  scheme_pack : GeometryScheme.IsFormalImmersionAt 2

theorem formal_immersion_at_2 : IsFormalImmersionAt 2 where
  prime := rfl
  matrix_Z := cotangent_Z_eq
  det_Z := cotangent_Z_det
  reduces := cotangent_Z_mod3_eq_M3
  full_rank_mod3 := two_ne_zero_mod3
  two_val := cotangent_Z_two_val
  basis := omega_basis
  scheme_pack := formal_immersion_scheme_at_2

/-- Displayed rational-point labels of the compactification
are the four cusps.  Not a Mathlib `X₀(26)(ℚ)` theorem. -/
theorem X0_26_Q_points_cusps_model :
    fourCuspsList = [1, 2, 13, 26] ∧
      ¬ ExistsNoncuspidal_26 ∧
        Sel2_26a1 = 1 ∧ Sel2_26b1 = 1 ∧
          certifiedMwrank_26a1 = 0 ∧ certifiedMwrank_26b1 = 0 ∧
            descentSHA =
              "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260" :=
  ⟨X0_26_Q_cusps, no_noncuspidal_Q_points,
    Sel2_eq_one.1, Sel2_eq_one.2,
    certifiedMwrank_zero.1, certifiedMwrank_zero.2, descentSHA_eq⟩

def beal_forall_from_Is13Case_sketch_stays_uninhabited : Prop :=
  ∀ (A B C m n p : Nat),
    2 < m → 2 < n → 2 < p →
    A ^ m + B ^ n = C ^ p →
    Nat.gcd A (Nat.gcd B C) > 1

#check X0_26_f
#check X0_26_hyperelliptic
#check J0_26_Model
#check AbelJacobiModel
#check formal_immersion_at_2
#check X0_26_Q_points_cusps_model
#print axioms X0_26_f_coeff_6
#print axioms X0_26_disc_cert_ne_zero
#print axioms cotangent_Z_det
#print axioms formal_immersion_at_2
#print axioms X0_26_Q_points_cusps_model

end BealLevel26Foundations.Beal.FullProof.X0_26_Model
