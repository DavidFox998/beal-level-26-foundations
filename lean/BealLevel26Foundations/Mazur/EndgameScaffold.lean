import Beal.Foundations.FormalImmersionM3
import BealLevel26Foundations.Mazur.Genus_26_Real
import BealLevel26Foundations.Real.FreyWeierstrass
import BealLevel26Foundations.Ribet.LevelLowering_26
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

namespace BealLevel26Foundations.Mazur.EndgameScaffold

open Beal.Foundations.FormalImmersionM3
open BealLevel26Foundations.Mazur.Genus26Real
open BealLevel26Foundations.Real.FreyWeierstrass
open BealLevel26Foundations.Ribet.LevelLowering26

/-!
# v4.0.0 Mazur endgame scaffold

This module packages the README Mazur chain as typed structures:

`J₀(26)(ℚ)` rank 0
  + formal immersion at 2
  ⇒ `X₀(26)(ℚ)` = four cusps
  ⇒ no level-26 Frey point
  ⇒ `BealTheorem`

Mathlib 4.12 has no Jacobian of `X₀(26)`, no Mordell--Weil group, no
formal-immersion API, and no modular-curve rational-point theorem.
Nothing below is discharged by `decide` except the already-checked v1.4
matrix `M₃ = [[1, 1], [0, 2]]` and `det = 2`.

`BealTheoremFromMazurChain26` concludes `BealTheorem` only from the four
named structures together with a v3 `LevelLowering_26` certificate and
the v2 Frey Weierstrass model.  It is not an unconditional `BealTheorem`.
-/

/-- Primitive Beal counterexample in the exponent range of the level-26
route. -/
structure BealCounterexample26 where
  A : Nat
  B : Nat
  C : Nat
  x : Nat
  y : Nat
  z : Nat
  positiveA : 0 < A
  positiveB : 0 < B
  positiveC : 0 < C
  exponents : 3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z
  equation : A ^ x + B ^ y = C ^ z
  primitive : Nat.gcd A (Nat.gcd B C) = 1

def IsBealSolution26 (A B C x y z : Nat) : Prop :=
  0 < A ∧ 0 < B ∧ 0 < C ∧
    3 ≤ x ∧ 3 ≤ y ∧ 3 ≤ z ∧
    A ^ x + B ^ y = C ^ z ∧
    Nat.gcd A (Nat.gcd B C) = 1

/-- The Beal statement as a proposition.  This is not a theorem. -/
def BealTheorem : Prop :=
  ∀ A B C x y z : Nat, ¬ IsBealSolution26 A B C x y z

def ofSolution (A B C x y z : Nat)
    (h : IsBealSolution26 A B C x y z) :
    BealCounterexample26 :=
  { A := A
    B := B
    C := C
    x := x
    y := y
    z := z
    positiveA := h.1
    positiveB := h.2.1
    positiveC := h.2.2.1
    exponents := ⟨h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1⟩
    equation := h.2.2.2.2.2.2.1
    primitive := h.2.2.2.2.2.2.2 }

/-- Rank-zero boundary for `J₀(26)(ℚ)`.  Mathlib 4.12 has no Jacobian
and no Mordell--Weil rank.  The rank statement is supplied data. -/
structure J0_26_Q_RankZero26 where
  rankZero : Prop
  rankZero_witness : rankZero

/-- Formal-immersion-at-2 *input*.  Carries the v1.4 certificate
`M₃ = [[1, 1], [0, 2]]`, `det = 2`.  The actual geometric immersion
statement is a supplied field and is not obtained by `decide`. -/
structure FormalImmersionAtTwo26 where
  input : Matrix (Fin 2) (Fin 2) (ZMod 3)
  input_eq : input = !![1, 1; 0, 2]
  input_det : Matrix.det input = 2
  actualFormalImmersionAtTwo : Prop
  actualFormalImmersionAtTwo_witness : actualFormalImmersionAtTwo

theorem FormalImmersionAtTwo26.input_certificate
    (h : FormalImmersionAtTwo26) :
    h.input = !![1, 1; 0, 2] ∧ Matrix.det h.input = 2 :=
  ⟨h.input_eq, h.input_det⟩

theorem FormalImmersionAtTwo26.input_eq_v1_4_M3
    (h : FormalImmersionAtTwo26) :
    h.input = certifiedM3 := by
  rw [h.input_eq, certifiedM3_eq]

theorem FormalImmersionAtTwo26.input_eq_ledgerM3
    (h : FormalImmersionAtTwo26) :
    h.input = BealLevel26Foundations.M3Explicit.ledgerM3 := by
  rw [h.input_eq_v1_4_M3, certifiedM3_eq_ledgerM3]

/-- Four displayed cusps, premise-bearing.  The arithmetic count `4` is
the v1 genus certificate.  Identifying `X₀(26)(ℚ)` with those cusps is
supplied, not decided. -/
structure X0_26_RationalPoints26 where
  displayedCuspCount : Nat
  displayedCuspCount_eq_four : displayedCuspCount = 4
  rationalPointsAreFourCusps : Prop
  ofRankZeroAndImmersion :
    J0_26_Q_RankZero26 → FormalImmersionAtTwo26 →
      rationalPointsAreFourCusps

theorem X0_26_RationalPoints26.displayed_four
    (h : X0_26_RationalPoints26) :
    h.displayedCuspCount = 4 :=
  h.displayedCuspCount_eq_four

theorem displayedCuspCount_matches_genus_certificate :
    cuspCount26 = 4 :=
  cuspCount26_eq_four

theorem X0_26_RationalPoints26.fourCusps_of_rank_and_immersion
    (h : X0_26_RationalPoints26)
    (hRank : J0_26_Q_RankZero26)
    (hImm : FormalImmersionAtTwo26) :
    h.rationalPointsAreFourCusps :=
  h.ofRankZeroAndImmersion hRank hImm

/-- Abstract witness that a noncuspidal level-26 Frey point exists.
This is not a point of a Mathlib modular curve. -/
structure Level26FreyPointWitness where
  loweredLevel : Nat
  loweredLevel_eq_26 : loweredLevel = 26

def ExistsNoncuspidalLevel26FreyPoint : Prop :=
  Nonempty Level26FreyPointWitness

/-- `X₀(26)(ℚ) = 4` cusps implies there is no level-26 Frey point.
The converse production of such a point from a Beal equation, the v2
Frey model, and a v3 lowering certificate is also supplied data. -/
structure NoFreyPoint26 where
  ofFourCusps :
    ∀ (hPts : X0_26_RationalPoints26),
      hPts.rationalPointsAreFourCusps →
        ¬ ExistsNoncuspidalLevel26FreyPoint
  ofBealFreyLowering :
    ∀ (cex : BealCounterexample26) {ℓ N p : Nat},
      LevelLowering_26 ℓ N p 26 →
        (freyCurve (cex.A : Int) (cex.B : Int) cex.x cex.y).Δ ≠ 0 →
          ExistsNoncuspidalLevel26FreyPoint

theorem bealCounterexample_freyDiscriminant_ne_zero
    (cex : BealCounterexample26) :
    (freyCurve (cex.A : Int) (cex.B : Int) cex.x cex.y).Δ ≠ 0 := by
  have hA : (cex.A : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt cex.positiveA)
  have hB : (cex.B : Int) ≠ 0 := by
    exact_mod_cast (ne_of_gt cex.positiveB)
  have hSum : (cex.A : Int) ^ cex.x + (cex.B : Int) ^ cex.y ≠ 0 := by
    have hC : (cex.C : Int) ≠ 0 := by
      exact_mod_cast (ne_of_gt cex.positiveC)
    have hPow : (cex.C : Int) ^ cex.z ≠ 0 := pow_ne_zero _ hC
    have hEq : (cex.A : Int) ^ cex.x + (cex.B : Int) ^ cex.y =
        (cex.C : Int) ^ cex.z := by
      norm_cast
      exact cex.equation
    exact hEq.symm ▸ hPow
  exact freyCurve_discriminant_ne_zero hA hB hSum

/-- Conditional Mazur-chain conclusion.

Every argument is a supplied structure or a v2/v3 construction.
This theorem does not decide rank, does not decide
`X₀(26)(ℚ) = four cusps`, and does not prove `R = T`. -/
theorem BealTheoremFromMazurChain26
    {ℓ N p : Nat}
    (hRank : J0_26_Q_RankZero26)
    (hImm : FormalImmersionAtTwo26)
    (hCusps : X0_26_RationalPoints26)
    (hNoFrey : NoFreyPoint26)
    (hLower : LevelLowering_26 ℓ N p 26) :
    BealTheorem := by
  intro A B C x y z hSol
  let cex := ofSolution A B C x y z hSol
  have hEqZ :
      (A : Int) ^ x + (B : Int) ^ y = (C : Int) ^ z := by
    norm_cast
    exact cex.equation
  let model := ofBealEquation (A : Int) (B : Int) (C : Int) x y z hEqZ
  have hΔ := bealCounterexample_freyDiscriminant_ne_zero cex
  have hΔmodel : model.Δ ≠ 0 := by
    simpa [model, ofBealEquation] using hΔ
  have hCuspId :
      hCusps.rationalPointsAreFourCusps :=
    hCusps.fourCusps_of_rank_and_immersion hRank hImm
  have hPin :
      hImm.input = !![1, 1; 0, 2] ∧
        Matrix.det hImm.input = 2 ∧
        hImm.input = certifiedM3 ∧
        hLower.targetLevel = 26 ∧
        hLower.weight = 2 ∧
        hCusps.displayedCuspCount = 4 ∧
        model.Δ ≠ 0 :=
    ⟨hImm.input_eq, hImm.input_det, hImm.input_eq_v1_4_M3, rfl,
      hLower.weight_eq_two, hCusps.displayed_four, hΔmodel⟩
  let _displayed := hPin
  exact hNoFrey.ofFourCusps hCusps hCuspId
    (hNoFrey.ofBealFreyLowering cex hLower hΔ)

#print axioms FormalImmersionAtTwo26.input_certificate
#print axioms FormalImmersionAtTwo26.input_eq_v1_4_M3
#print axioms bealCounterexample_freyDiscriminant_ne_zero
#print axioms BealTheoremFromMazurChain26

end BealLevel26Foundations.Mazur.EndgameScaffold
