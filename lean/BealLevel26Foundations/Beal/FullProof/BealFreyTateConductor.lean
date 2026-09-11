/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v9.1.0 -- Tate Step 2 for Frey
Y^2 = X(X-A^4)(X+B^4).  Not Mathlib N(E).

Mathlib 4.12 has WeierstrassCurve.Delta and no
MinimalModel / Kodaira / conductor API.  This
file encodes Tate 1975 Step 2 as a function of
valuations (Silverman AEC IV.9): p | Delta and
p does not divide c4 implies Kodaira I_{v_p(Delta)}
and local conductor exponent 1.

Inhabited:
* c4 = 16 * (A^8 + A^4 B^4 + B^8) on the existing
  freyCurve (A : Int) (B : Int) 4 4.
* v2(c4) >= 4 when A or B is nonzero, so Step 2
  does not finish at 2 on this integral model.
* Odd q | A*B*(B+3), pairwise coprime bases,
  A,B positive: v_q(c4)=0, v_q(Delta)>0,
  conductorExponentTate = 1.
* tate_rhs = 2^5 * rad(A B (B+3)) * 13, and
  rad(ABC) | tate_rhs.  Packed odd Step-2
  primes divide tate_rhs.

Uninhabited:
* frey_tate_conductor -- the requested
  N | 2^5 * rad(AB(B+3)) * 13 for a Tate
  conductor N(E).  Step 2 does not give the
  2-adic exponent, and Mathlib has no N(E).
  Do not inhabit this with N = |Delta|
  (|Delta| = 2^4 A^8 B^8 C^26 is not that
  bound) or with the trivial N = 1.

Keeps baker_bound_gap3 Prop, the three Zsig
Props, conductor_86 Prop, B14_honest Prop.
Does not import RibetMazur, BealFreyB14, or
FreyModularity_13.  Not imported by the
24-module none chain.  Not BCDT.
-/

import BealLevel26Foundations.Beal.FullProof.BealFreyConductorGeneral
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace BealLevel26Foundations.BealFreyTateConductor

open BealLevel26Foundations.BealFreyConductorGeneral
open BealLevel26Foundations.Real.FreyWeierstrass

/-! ## Re-exports (v8.87 Weierstrass Delta; not Tate) -/

theorem frey_conductor_general (A B C : Nat)
    (h : Nat.pow A 4 + Nat.pow B 4 = Nat.pow C 13)
    (hGap : C = B + 3) :
    ∃ (e N0 : Nat),
      Int.natAbs (bealFreyWeierstrass A B).Δ = Nat.pow 2 e * N0 ∧
      N0 ∣ Nat.pow (A * B * C) 26 * 13 ∧
      e ≤ 5 :=
  BealLevel26Foundations.BealFreyConductorGeneral.frey_conductor_general
    A B C h hGap

/-! ## Tate Step 2 as a function of valuations -/

inductive KodairaTate where
  | I0 : KodairaTate
  | I : Nat → KodairaTate
  | needsFurtherSteps : KodairaTate
  deriving DecidableEq, Repr

def kodairaTate (vc4 vD : Nat) : KodairaTate :=
  if vD = 0 then KodairaTate.I0
  else if vc4 = 0 then KodairaTate.I vD
  else KodairaTate.needsFurtherSteps

/-- Local conductor exponent from Tate Step 2.
    Equals 1 on type I_n.  Equals 0 for good
    reduction and for models that need later
    Tate steps (not a claim about those steps). -/
def conductorExponentTate (vc4 vD : Nat) : Nat :=
  if vD = 0 then 0
  else if vc4 = 0 then 1
  else 0

theorem kodairaTate_of_step2 {vc4 vD : Nat}
    (hc4 : vc4 = 0) (hD : vD ≠ 0) :
    kodairaTate vc4 vD = KodairaTate.I vD := by
  rw [kodairaTate, if_neg hD, if_pos hc4]

theorem conductorExponentTate_of_step2 {vc4 vD : Nat}
    (hc4 : vc4 = 0) (hD : vD ≠ 0) :
    conductorExponentTate vc4 vD = 1 := by
  rw [conductorExponentTate, if_neg hD, if_pos hc4]

theorem kodairaTate_needs_further {vc4 vD : Nat}
    (hc4 : vc4 ≠ 0) (hD : vD ≠ 0) :
    kodairaTate vc4 vD = KodairaTate.needsFurtherSteps := by
  rw [kodairaTate, if_neg hD, if_neg hc4]

theorem conductorExponentTate_needs_further {vc4 vD : Nat}
    (hc4 : vc4 ≠ 0) (hD : vD ≠ 0) :
    conductorExponentTate vc4 vD = 0 := by
  rw [conductorExponentTate, if_neg hD, if_neg hc4]

/-! ## c4 identity on this Frey model -/

/-- Natural-number shape of c4 / 16. -/
def c4Paren (A B : Nat) : Nat :=
  A ^ 8 + A ^ 4 * B ^ 4 + B ^ 8

theorem c4Paren_add_cross (A B : Nat) :
    (A ^ 4 + B ^ 4) ^ 2 = c4Paren A B + A ^ 4 * B ^ 4 := by
  unfold c4Paren
  ring

theorem c4Paren_pos {A B : Nat} (h : A ≠ 0 ∨ B ≠ 0) :
    0 < c4Paren A B := by
  unfold c4Paren
  rcases h with hA | hB
  · have h8 : 0 < A ^ 8 := Nat.pow_pos (Nat.pos_of_ne_zero hA)
    have hle : A ^ 8 ≤ A ^ 8 + A ^ 4 * B ^ 4 + B ^ 8 :=
      Nat.le_trans (Nat.le_add_right (A ^ 8) (A ^ 4 * B ^ 4))
        (Nat.le_add_right _ _)
    exact lt_of_lt_of_le h8 hle
  · exact Nat.add_pos_right (A ^ 8 + A ^ 4 * B ^ 4)
      (Nat.pow_pos (Nat.pos_of_ne_zero hB))

theorem beal_frey_c4 (A B : Nat) :
    (bealFreyWeierstrass A B).c₄ =
      16 * (((A : Int) ^ 4) ^ 2 + (A : Int) ^ 4 * (B : Int) ^ 4 +
        ((B : Int) ^ 4) ^ 2) :=
  freyCurve_c4 (A : Int) (B : Int) 4 4

theorem beal_frey_c4_nat (A B : Nat) :
    (bealFreyWeierstrass A B).c₄ = ((16 * c4Paren A B : Nat) : Int) := by
  rw [beal_frey_c4]
  unfold c4Paren
  push_cast
  ring

/-! ## Tate at 2: this model has v2(c4) >= 4 -/

theorem v2_c4_ge_four {A B : Nat} (hAB : A ≠ 0 ∨ B ≠ 0) :
    4 ≤ padicValInt 2 (bealFreyWeierstrass A B).c₄ := by
  haveI : Fact (2 : Nat).Prime := ⟨Nat.prime_two⟩
  rw [beal_frey_c4_nat, padicValInt.of_nat]
  have h16 : (16 : Nat) ≠ 0 := by decide
  have hP : c4Paren A B ≠ 0 :=
    Nat.pos_iff_ne_zero.mp (c4Paren_pos hAB)
  rw [padicValNat.mul h16 hP]
  have hval : padicValNat 2 16 = 4 := by
    rw [show (16 : Nat) = 2 ^ 4 from rfl, padicValNat.prime_pow]
  rw [hval]
  exact Nat.le_add_right 4 _

theorem v2_c4_ne_zero {A B : Nat} (hAB : A ≠ 0 ∨ B ≠ 0) :
    padicValInt 2 (bealFreyWeierstrass A B).c₄ ≠ 0 :=
  Nat.ne_of_gt
    (lt_of_lt_of_le (Nat.succ_pos 3) (v2_c4_ge_four hAB))

/-- Step 2 does not finish at 2: v2(c4) != 0, so the
    algorithm reports needsFurtherSteps.  The 2-adic
    change of variables that would put this model
    into Step 2 is not a unit VariableChange over Z. -/
theorem tate_step2_does_not_finish_at_two {A B : Nat}
    (hAB : A ≠ 0 ∨ B ≠ 0)
    (hD : padicValInt 2 (bealFreyWeierstrass A B).Δ ≠ 0) :
    kodairaTate
      (padicValInt 2 (bealFreyWeierstrass A B).c₄)
      (padicValInt 2 (bealFreyWeierstrass A B).Δ) =
      KodairaTate.needsFurtherSteps :=
  kodairaTate_needs_further (v2_c4_ne_zero hAB) hD

/-! ## Euclid on gap 3 (local copy; do not import BealFreyB14) -/

theorem gcd_B_Bplus3_dvd_three (B : Nat) :
    Nat.gcd B (B + 3) ∣ 3 :=
  let d := Nat.gcd B (B + 3)
  let hB : d ∣ B := Nat.gcd_dvd_left B (B + 3)
  let hB3 : d ∣ B + 3 := Nat.gcd_dvd_right B (B + 3)
  let h3B : d ∣ 3 + B :=
    Eq.rec (motive := fun t (_ : B + 3 = t) => d ∣ t)
      hB3 (Nat.add_comm B 3)
  (Nat.dvd_add_iff_left hB).mpr h3B

theorem coprime_B_Bplus3_of_not_dvd_three (B : Nat)
    (h : ¬ 3 ∣ B) :
    Nat.Coprime B (B + 3) := by
  change Nat.gcd B (B + 3) = 1
  have hdvd : Nat.gcd B (B + 3) ∣ 3 := gcd_B_Bplus3_dvd_three B
  rcases (Nat.dvd_prime (by decide : Nat.Prime 3)).mp hdvd with h1 | h3eq
  · exact h1
  · have h3B : 3 ∣ B := h3eq ▸ Nat.gcd_dvd_left B (B + 3)
    exact absurd h3B h

theorem coprime_not_dvd_both {a b q : Nat}
    (h : Nat.Coprime a b) (hq : Nat.Prime q)
    (ha : q ∣ a) (hb : q ∣ b) : False := by
  have hg : q ∣ Nat.gcd a b := Nat.dvd_gcd ha hb
  have h1 : q ∣ 1 := by
    change Nat.gcd a b = 1 at h
    rw [h] at hg
    exact hg
  exact hq.not_dvd_one h1

theorem odd_prime_ne_two {q : Nat} (hq : q.Prime) (hodd : q ≠ 2) :
    ¬ q ∣ 16 := by
  intro h16
  have h2 : q ∣ 2 := hq.dvd_of_dvd_pow (by
    have : 16 = 2 ^ 4 := rfl
    exact this ▸ h16)
  have heq : q = 2 :=
    (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
  exact hodd heq

/-! ## Odd primes of ABC do not divide c4, under coprimeness -/

theorem not_dvd_c4Paren_of_dvd_A {A B q : Nat}
    (hq : q.Prime) (hA : q ∣ A) (hB : ¬ q ∣ B) :
    ¬ q ∣ c4Paren A B := by
  intro hP
  have hA8 : q ∣ A ^ 8 := dvd_pow hA (by decide : 8 ≠ 0)
  have hA4 : q ∣ A ^ 4 := dvd_pow hA (by decide : 4 ≠ 0)
  have hmid : q ∣ A ^ 4 * B ^ 4 := dvd_mul_of_dvd_left hA4 _
  have hsum : q ∣ A ^ 8 + A ^ 4 * B ^ 4 := dvd_add hA8 hmid
  have hB8 : q ∣ B ^ 8 := by
    unfold c4Paren at hP
    have hassoc :
        A ^ 8 + A ^ 4 * B ^ 4 + B ^ 8 =
          B ^ 8 + (A ^ 8 + A ^ 4 * B ^ 4) := by
      ac_rfl
    exact (Nat.dvd_add_left hsum).mp (hassoc ▸ hP)
  exact hB (hq.dvd_of_dvd_pow hB8)

theorem not_dvd_c4Paren_of_dvd_B {A B q : Nat}
    (hq : q.Prime) (hB : q ∣ B) (hA : ¬ q ∣ A) :
    ¬ q ∣ c4Paren A B := by
  intro hP
  have hB8 : q ∣ B ^ 8 := dvd_pow hB (by decide : 8 ≠ 0)
  have hB4 : q ∣ B ^ 4 := dvd_pow hB (by decide : 4 ≠ 0)
  have hmid : q ∣ A ^ 4 * B ^ 4 := dvd_mul_of_dvd_right hB4 _
  have hsum : q ∣ A ^ 4 * B ^ 4 + B ^ 8 := dvd_add hmid hB8
  have hA8 : q ∣ A ^ 8 := by
    unfold c4Paren at hP
    have hassoc :
        A ^ 8 + A ^ 4 * B ^ 4 + B ^ 8 =
          A ^ 8 + (A ^ 4 * B ^ 4 + B ^ 8) := by
      ac_rfl
    exact (Nat.dvd_add_left hsum).mp (hassoc ▸ hP)
  exact hA (hq.dvd_of_dvd_pow hA8)

theorem not_dvd_c4Paren_of_dvd_C {A B q : Nat}
    (hq : q.Prime)
    (hEq : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hC : q ∣ B + 3) (hA : ¬ q ∣ A) (hB : ¬ q ∣ B) :
    ¬ q ∣ c4Paren A B := by
  intro hP
  have hSum : A ^ 4 + B ^ 4 = (B + 3) ^ 13 := by
    rw [← nat_pow_eq_hpow A 4, ← nat_pow_eq_hpow B 4,
      ← nat_pow_eq_hpow (B + 3) 13]
    exact hEq
  have hCpow : q ∣ (B + 3) ^ 13 :=
    dvd_pow hC (by decide : 13 ≠ 0)
  have hSumDvd : q ∣ A ^ 4 + B ^ 4 := hSum ▸ hCpow
  have hSq : q ∣ (A ^ 4 + B ^ 4) ^ 2 :=
    dvd_pow hSumDvd (by decide)
  have hId := c4Paren_add_cross A B
  have hsum2 : q ∣ c4Paren A B + A ^ 4 * B ^ 4 := hId ▸ hSq
  have hcross : q ∣ A ^ 4 * B ^ 4 :=
    (Nat.dvd_add_right hP).mp hsum2
  rcases (Nat.Prime.dvd_mul hq).mp hcross with hA4 | hB4
  · exact hA (hq.dvd_of_dvd_pow hA4)
  · exact hB (hq.dvd_of_dvd_pow hB4)

theorem odd_prime_not_dvd_c4 {A B q : Nat}
    (hEq : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hAB : Nat.Coprime A B)
    (hAC : Nat.Coprime A (B + 3))
    (hBC : Nat.Coprime B (B + 3))
    (hq : q.Prime) (hodd : q ≠ 2)
    (hdvd : q ∣ A * B * (B + 3)) :
    ¬ (q : Int) ∣ (bealFreyWeierstrass A B).c₄ := by
  intro hc4
  have hc4N : q ∣ 16 * c4Paren A B := by
    rw [beal_frey_c4_nat] at hc4
    exact Int.natCast_dvd_natCast.mp hc4
  have hP : q ∣ c4Paren A B := by
    rcases (Nat.Prime.dvd_mul hq).mp hc4N with h16 | hQ
    · exact absurd h16 (odd_prime_ne_two hq hodd)
    · exact hQ
  have hABC := (Nat.Prime.dvd_mul hq).mp hdvd
  rcases hABC with hABm | hC
  · rcases (Nat.Prime.dvd_mul hq).mp hABm with hA | hB
    · have hBn : ¬ q ∣ B :=
        fun hb => coprime_not_dvd_both hAB hq hA hb
      exact not_dvd_c4Paren_of_dvd_A hq hA hBn hP
    · have hAn : ¬ q ∣ A :=
        fun ha => coprime_not_dvd_both hAB hq ha hB
      exact not_dvd_c4Paren_of_dvd_B hq hB hAn hP
  · have hAn : ¬ q ∣ A :=
      fun ha => coprime_not_dvd_both hAC hq ha hC
    have hBn : ¬ q ∣ B :=
      fun hb => coprime_not_dvd_both hBC hq hb hC
    exact not_dvd_c4Paren_of_dvd_C hq hEq hC hAn hBn hP

theorem odd_prime_c4_val_zero {A B q : Nat}
    (hEq : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hAB : Nat.Coprime A B)
    (hAC : Nat.Coprime A (B + 3))
    (hBC : Nat.Coprime B (B + 3))
    (hq : q.Prime) (hodd : q ≠ 2)
    (hdvd : q ∣ A * B * (B + 3)) :
    padicValInt q (bealFreyWeierstrass A B).c₄ = 0 :=
  padicValInt.eq_zero_of_not_dvd
    (odd_prime_not_dvd_c4 hEq hAB hAC hBC hq hodd hdvd)

/-! ## Odd primes of ABC divide Delta -/

theorem beal_frey_delta_nonneg (A B : Nat)
    (h : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    0 ≤ (bealFreyWeierstrass A B).Δ := by
  rw [BealLevel26Foundations.BealFreyConductorGeneral.beal_frey_weierstrass_delta
    A B (B + 3) h]
  exact mul_nonneg
    (mul_nonneg
      (mul_nonneg (by decide : (0 : Int) ≤ 16) (sq_nonneg _))
      (sq_nonneg _))
    (sq_nonneg _)

theorem beal_frey_delta_eq_nat (A B : Nat)
    (h : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    (bealFreyWeierstrass A B).Δ =
      ((16 * Nat.pow A 8 * Nat.pow B 8 * Nat.pow (B + 3) 26 : Nat) : Int) := by
  have hnn := beal_frey_delta_nonneg A B h
  have hAbs := beal_frey_weierstrass_delta_natAbs A B (B + 3) h
  have hcast :
      ((Int.natAbs (bealFreyWeierstrass A B).Δ : Nat) : Int) =
        ((16 * Nat.pow A 8 * Nat.pow B 8 * Nat.pow (B + 3) 26 : Nat) : Int) :=
    congrArg Nat.cast hAbs
  rw [Int.natAbs_of_nonneg hnn] at hcast
  exact hcast

theorem odd_prime_dvd_Delta_nat {A B q : Nat}
    (hq : q.Prime)
    (hdvd : q ∣ A * B * (B + 3)) :
    q ∣ 16 * Nat.pow A 8 * Nat.pow B 8 * Nat.pow (B + 3) 26 := by
  have hsq {x : Nat} (hx : q ∣ x) : q ∣ Nat.pow x 8 :=
    dvd_pow hx (by decide : 8 ≠ 0)
  have hCp {x : Nat} (hx : q ∣ x) : q ∣ Nat.pow x 26 :=
    dvd_pow hx (by decide : 26 ≠ 0)
  have hABC := (Nat.Prime.dvd_mul hq).mp hdvd
  rcases hABC with hABm | hC0
  · rcases (Nat.Prime.dvd_mul hq).mp hABm with hA | hB
    · exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right (hsq hA) _) _) _
    · exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (hsq hB) _) _
  · exact dvd_mul_of_dvd_right (hCp hC0) _

theorem odd_prime_dvd_Delta {A B q : Nat}
    (hq : q.Prime)
    (hEq : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hdvd : q ∣ A * B * (B + 3)) :
    (q : Int) ∣ (bealFreyWeierstrass A B).Δ := by
  rw [beal_frey_delta_eq_nat A B hEq]
  exact Int.natCast_dvd_natCast.mpr (odd_prime_dvd_Delta_nat hq hdvd)

theorem delta_natAbs_ne_zero {A B : Nat}
    (hA : 0 < A) (hB : 0 < B)
    (h : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    Int.natAbs (bealFreyWeierstrass A B).Δ ≠ 0 := by
  rw [BealLevel26Foundations.BealFreyConductorGeneral.beal_frey_weierstrass_delta_natAbs
    A B (B + 3) h]
  refine Nat.mul_ne_zero (Nat.mul_ne_zero (Nat.mul_ne_zero
    (by decide : (16 : Nat) ≠ 0)
    (Nat.pos_iff_ne_zero.mp (Nat.pow_pos hA)))
    (Nat.pos_iff_ne_zero.mp (Nat.pow_pos hB)))
    (Nat.pos_iff_ne_zero.mp (Nat.pow_pos (Nat.succ_pos (B + 2))))

theorem odd_prime_Delta_val_pos {A B q : Nat}
    (hA : 0 < A) (hB : 0 < B)
    (hEq : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hq : q.Prime)
    (hdvd : q ∣ A * B * (B + 3)) :
    0 < padicValInt q (bealFreyWeierstrass A B).Δ := by
  haveI : Fact q.Prime := ⟨hq⟩
  have hAbs :=
    BealLevel26Foundations.BealFreyConductorGeneral.beal_frey_weierstrass_delta_natAbs
      A B (B + 3) hEq
  have hne := delta_natAbs_ne_zero hA hB hEq
  have hdvdN : q ∣ Int.natAbs (bealFreyWeierstrass A B).Δ := by
    rw [hAbs]
    exact odd_prime_dvd_Delta_nat hq hdvd
  have hpow : q ^ 1 ∣ Int.natAbs (bealFreyWeierstrass A B).Δ := by
    rw [pow_one]
    exact hdvdN
  have hle : 1 ≤ padicValNat q
      (Int.natAbs (bealFreyWeierstrass A B).Δ) := by
    have hiff := padicValNat_dvd_iff (p := q) 1
      (Int.natAbs (bealFreyWeierstrass A B).Δ)
    rcases hiff.mp hpow with h0 | hle
    · exact absurd h0 hne
    · exact hle
  change 0 < padicValNat q (Int.natAbs (bealFreyWeierstrass A B).Δ)
  exact Nat.succ_le_iff.mp hle

/-- Tate Step 2 at an odd prime q | ABC: local
    conductor exponent 1.  Needs pairwise
    coprimeness (otherwise q may divide c4). -/
theorem tate_odd_prime_exponent_one {A B q : Nat}
    (hA : 0 < A) (hB : 0 < B)
    (hEq : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hAB : Nat.Coprime A B)
    (hAC : Nat.Coprime A (B + 3))
    (hBC : Nat.Coprime B (B + 3))
    (hq : q.Prime) (hodd : q ≠ 2)
    (hdvd : q ∣ A * B * (B + 3)) :
    conductorExponentTate
      (padicValInt q (bealFreyWeierstrass A B).c₄)
      (padicValInt q (bealFreyWeierstrass A B).Δ) = 1 :=
  conductorExponentTate_of_step2
    (odd_prime_c4_val_zero hEq hAB hAC hBC hq hodd hdvd)
    (odd_prime_Delta_val_pos hA hB hEq hq hdvd).ne'

theorem tate_odd_prime_kodaira_I {A B q : Nat}
    (hA : 0 < A) (hB : 0 < B)
    (hEq : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13)
    (hAB : Nat.Coprime A B)
    (hAC : Nat.Coprime A (B + 3))
    (hBC : Nat.Coprime B (B + 3))
    (hq : q.Prime) (hodd : q ≠ 2)
    (hdvd : q ∣ A * B * (B + 3)) :
    kodairaTate
      (padicValInt q (bealFreyWeierstrass A B).c₄)
      (padicValInt q (bealFreyWeierstrass A B).Δ) =
      KodairaTate.I
        (padicValInt q (bealFreyWeierstrass A B).Δ) :=
  kodairaTate_of_step2
    (odd_prime_c4_val_zero hEq hAB hAC hBC hq hodd hdvd)
    (odd_prime_Delta_val_pos hA hB hEq hq hdvd).ne'

/-! ## Displayed radical bound (not N(E)) -/

/-- Requested right-hand side.  Not a conductor. -/
def tate_rhs (A B : Nat) : Nat :=
  Nat.pow 2 5 * rad (A * B * (B + 3)) * 13

theorem rad_dvd_tate_rhs (A B : Nat) :
    rad (A * B * (B + 3)) ∣ tate_rhs A B :=
  Nat.dvd_trans
    (Nat.dvd_mul_left (rad (A * B * (B + 3))) (Nat.pow 2 5))
    (Nat.dvd_mul_right _ 13)

theorem two_pow5_dvd_tate_rhs (A B : Nat) :
    Nat.pow 2 5 ∣ tate_rhs A B :=
  Nat.dvd_trans
    (Nat.dvd_mul_right (Nat.pow 2 5) (rad (A * B * (B + 3))))
    (Nat.dvd_mul_right _ 13)

theorem thirteen_dvd_tate_rhs (A B : Nat) :
    13 ∣ tate_rhs A B :=
  Nat.dvd_mul_left 13 (Nat.pow 2 5 * rad (A * B * (B + 3)))

/-- Product of odd prime factors of ABC.
    Each such prime has Tate exponent 1 under
    pairwise coprimeness.  Not Mathlib N(E). -/
def packedOddStep2 (A B : Nat) : Nat :=
  ((A * B * (B + 3)).primeFactors.filter (fun q => q ≠ 2)).prod id

theorem packedOddStep2_dvd_rad (A B : Nat) :
    packedOddStep2 A B ∣ rad (A * B * (B + 3)) := by
  unfold packedOddStep2 rad
  exact Finset.prod_dvd_prod_of_subset _ _
    (fun q : Nat => id q)
    (Finset.filter_subset _ _)

theorem packedOddStep2_dvd_tate_rhs (A B : Nat) :
    packedOddStep2 A B ∣ tate_rhs A B :=
  Nat.dvd_trans (packedOddStep2_dvd_rad A B) (rad_dvd_tate_rhs A B)

theorem odd_prime_dvd_rad {q n : Nat}
    (hq : q.Prime) (hn : n ≠ 0) (hdvd : q ∣ n) :
    q ∣ rad n := by
  have hmem : q ∈ n.primeFactors :=
    Nat.mem_primeFactors.mpr ⟨hq, hdvd, hn⟩
  exact Finset.dvd_prod_of_mem id hmem

theorem odd_prime_dvd_tate_rhs {A B q : Nat}
    (hq : q.Prime) (_hodd : q ≠ 2)
    (hABC : A * B * (B + 3) ≠ 0)
    (hdvd : q ∣ A * B * (B + 3)) :
    q ∣ tate_rhs A B := by
  have : q ∣ rad (A * B * (B + 3)) :=
    odd_prime_dvd_rad hq hABC hdvd
  exact Nat.dvd_trans this (rad_dvd_tate_rhs A B)

/-! ## Requested Tate conductor bound stays a Prop -/

/-- Empty token.  Mathlib 4.12 has no Tate N(E).
    Not |Delta|.  Not packed rad. -/
inductive IsTateConductor : WeierstrassCurve Int → Nat → Prop

/-- Uninhabited.  The requested conclusion of
    Tate's algorithm on this Frey model.
    Step 2 gives exponent 1 at odd primes of
    ABC under coprimeness, but not the 2-adic
    exponent and not a Mathlib conductor N(E).
    Do not inhabit with N = |Delta| (false:
    A^8 does not divide rad(ABC)) or N = 1
    (trivial).  conductor_86 stays the
    stronger uninhabited N | 2^5*3*13. -/
def frey_tate_conductor : Prop :=
  ∀ A B : Nat,
    Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 →
    ∃ N, IsTateConductor (bealFreyWeierstrass A B) N ∧
      N ∣ Nat.pow 2 5 * rad (A * B * (B + 3)) * 13

#check rad
#check bealFreyWeierstrass
#check conductorExponentTate
#check beal_frey_c4
#check v2_c4_ge_four
#check tate_step2_does_not_finish_at_two
#check tate_odd_prime_exponent_one
#check tate_rhs
#check rad_dvd_tate_rhs
#check packedOddStep2_dvd_tate_rhs
#check frey_tate_conductor
#check frey_conductor_general
#print axioms beal_frey_c4
#print axioms v2_c4_ge_four
#print axioms tate_step2_does_not_finish_at_two
#print axioms tate_odd_prime_exponent_one
#print axioms rad_dvd_tate_rhs
#print axioms packedOddStep2_dvd_tate_rhs
#print axioms frey_conductor_general
#print axioms gcd_B_Bplus3_dvd_three

end BealLevel26Foundations.BealFreyTateConductor
