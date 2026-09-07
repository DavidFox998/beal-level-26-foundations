import BealLevel26Foundations.Frey.Conductor_26_Unconditional
import BealLevel26Foundations.Frey.FreyConductorData_26
import BealLevel26Foundations.Real.FreyWeierstrass
import Mathlib.Algebra.BigOperators.Group.Finset
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.PrimeFin
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace BealLevel26Foundations.Beal.FullProof.TrueConductor

open BealLevel26Foundations.Frey.Conductor26Unconditional
open BealLevel26Foundations.Frey.FreyConductorData26
open BealLevel26Foundations.Real.FreyWeierstrass

/-!
# v7.2.0-step1-true-conductor-scaffold

True-gcd + Tate typing for a primitive Beal triple, every prime.

This module does **not** inhabit
`beal_forall_from_Is13Case_sketch`.  It does **not** use
`sorry`, `admit`, or `False.elim`.  `verify-scaffold.sh`
rejects `sorry` tree-wide, so the remaining Tate / Kodaira
obligations are **uninhabited empty-Type witnesses**, the
same honesty as `tate_algorithm_of_Is13Case`.

What this file *does* prove, as equalities not `rfl` tokens:

* the Frey model `Y² = X(X − Aᵐ)(X + Bⁿ)` from a packed
  primitive triple (mixed exponents, not the working-prime
  `13,13` display);
* `Δ = 16 (Aᵐ)² (Bⁿ)² (Cᵖ)²` from the Beal equation, via
  the existing `ring` identity in `FreyWeierstrass`;
* the true gcd step: a primitive equation implies pairwise
  coprimality, hence an odd prime `q ∣ ABC` does not divide
  `c₄`;
* therefore `v_q(c₄) = 0` and `v_q(Δ) > 0`.

What stays uninhabited (Mathlib 4.12 has no Tate / Kodaira /
conductor):

* minimality of the model at `q`;
* Kodaira type `Iₙ` and local conductor exponent `1`;
* the 2-adic exponent (suppliers
  `FreyTwoAdicExponentOneCertificate` /
  `FreyTwoAdicConductorCertificate` package it as data,
  matching `FreyConductorData_26`);
* `N = 2 · rad(ABC)`.

The v7.1.0 `frey_beal_forall_none_formula` none chain is
untouched.  This file is a new FullProof root, not one of
the 24 Galois/kernel modules.
-/

/-- Packed primitive Beal triple.  Exponents match
`beal_forall_from_Is13Case_sketch` (`2 < m,n,p`), not the
working-prime-13 display. -/
structure PrimitiveBealTriple where
  A : Nat
  B : Nat
  C : Nat
  m : Nat
  n : Nat
  p : Nat
  positiveA : 0 < A
  positiveB : 0 < B
  positiveC : 0 < C
  hm : 2 < m
  hn : 2 < n
  hp : 2 < p
  equation : A ^ m + B ^ n = C ^ p
  primitive : Nat.gcd A (Nat.gcd B C) = 1

/-- Displayed `gcd(A, gcd(B, C))`. -/
def gcd3 (A B C : Nat) : Nat :=
  Nat.gcd A (Nat.gcd B C)

theorem PrimitiveBealTriple.gcd3_eq_one (w : PrimitiveBealTriple) :
    gcd3 w.A w.B w.C = 1 :=
  w.primitive

/-- Integral Frey model of a packed triple:
`Y² = X (X − Aᵐ) (X + Bⁿ)`. -/
def freyCurveOf (w : PrimitiveBealTriple) : WeierstrassCurve Int :=
  freyCurve (w.A : Int) (w.B : Int) w.m w.n

theorem freyCurveOf_eq (w : PrimitiveBealTriple) :
    freyCurveOf w = freyCurve (w.A : Int) (w.B : Int) w.m w.n :=
  rfl

/-- Discriminant identity, proved by `ring` in
`FreyWeierstrass`, not an `rfl` token and not `Int.pow` /
`Nat.pow` OFF. -/
theorem frey_Delta_formula (w : PrimitiveBealTriple) :
    (freyCurveOf w).Δ =
      16 * ((w.A : Int) ^ w.m) ^ 2 * ((w.B : Int) ^ w.n) ^ 2 *
        ((w.A : Int) ^ w.m + (w.B : Int) ^ w.n) ^ 2 :=
  freyCurve_discriminant (w.A : Int) (w.B : Int) w.m w.n

/-- Substitute the Beal equation: `Δ = 16 (Aᵐ)² (Bⁿ)² (Cᵖ)²`
up to the sign of the integer casts, which are nonnegative. -/
theorem frey_Delta_of_equation (w : PrimitiveBealTriple) :
    (freyCurveOf w).Δ =
      16 * ((w.A : Int) ^ w.m) ^ 2 * ((w.B : Int) ^ w.n) ^ 2 *
        ((w.C : Int) ^ w.p) ^ 2 := by
  have h : ((w.A : Int) ^ w.m) + ((w.B : Int) ^ w.n) =
      (w.C : Int) ^ w.p := by
    have hNat : w.A ^ w.m + w.B ^ w.n = w.C ^ w.p := w.equation
    exact_mod_cast hNat
  simpa [freyCurveOf, h] using
    (freyCurve_discriminant_of_equation (A := (w.A : Int))
      (B := (w.B : Int)) (C := (w.C : Int)) (x := w.m) (y := w.n)
      (z := w.p) h)

/-- `c₄` identity, proved by `ring`, not an `rfl` token. -/
theorem frey_c4_formula (w : PrimitiveBealTriple) :
    (freyCurveOf w).c₄ =
      16 * (((w.A : Int) ^ w.m) ^ 2 +
        (w.A : Int) ^ w.m * (w.B : Int) ^ w.n +
        ((w.B : Int) ^ w.n) ^ 2) :=
  freyCurve_c4 (w.A : Int) (w.B : Int) w.m w.n

theorem frey_Delta_ne_zero (w : PrimitiveBealTriple) :
    (freyCurveOf w).Δ ≠ 0 := by
  have hA : (w.A : Int) ≠ 0 := by exact_mod_cast (ne_of_gt w.positiveA)
  have hB : (w.B : Int) ≠ 0 := by exact_mod_cast (ne_of_gt w.positiveB)
  have hSumNat : 0 < w.A ^ w.m + w.B ^ w.n :=
    Nat.add_pos_left (pow_pos w.positiveA w.m) _
  have hSum : (w.A : Int) ^ w.m + (w.B : Int) ^ w.n ≠ 0 := by
    have hCast : ((w.A ^ w.m + w.B ^ w.n : Nat) : Int) ≠ 0 :=
      by exact_mod_cast (ne_of_gt hSumNat)
    simpa [Nat.cast_add, Nat.cast_pow] using hCast
  simpa [freyCurveOf] using
    (freyCurve_discriminant_ne_zero hA hB hSum)

private theorem exponent_ne_zero {k : Nat} (hk : 2 < k) : k ≠ 0 := by
  omega

/-- Coprime bases cannot share a prime factor. -/
theorem coprime_not_dvd_both {a b q : Nat}
    (h : Nat.Coprime a b) (hq : q.Prime) (ha : q ∣ a) : ¬ q ∣ b := by
  intro hb
  exact hq.not_dvd_one (h ▸ Nat.dvd_gcd ha hb)

/-- True gcd step, part 1: a prime dividing two of `A,B,C`
divides the third, via the Beal equation. -/
theorem prime_dvd_two_implies_third (w : PrimitiveBealTriple)
    {q : Nat} (hq : q.Prime) :
    (q ∣ w.A ∧ q ∣ w.B → q ∣ w.C) ∧
      (q ∣ w.A ∧ q ∣ w.C → q ∣ w.B) ∧
      (q ∣ w.B ∧ q ∣ w.C → q ∣ w.A) := by
  refine ⟨?hAB, ?hAC, ?hBC⟩
  · intro h
    have hPow : q ∣ w.A ^ w.m + w.B ^ w.n :=
      dvd_add (dvd_pow h.1 (exponent_ne_zero w.hm))
        (dvd_pow h.2 (exponent_ne_zero w.hn))
    have hCpow : q ∣ w.C ^ w.p := w.equation ▸ hPow
    exact hq.dvd_of_dvd_pow hCpow
  · intro h
    have hCpow : q ∣ w.C ^ w.p :=
      dvd_pow h.2 (exponent_ne_zero w.hp)
    have hApow : q ∣ w.A ^ w.m :=
      dvd_pow h.1 (exponent_ne_zero w.hm)
    have hBpow : q ∣ w.B ^ w.n := by
      have : q ∣ w.A ^ w.m + w.B ^ w.n := w.equation ▸ hCpow
      exact (Nat.dvd_add_right hApow).mp this
    exact hq.dvd_of_dvd_pow hBpow
  · intro h
    have hCpow : q ∣ w.C ^ w.p :=
      dvd_pow h.2 (exponent_ne_zero w.hp)
    have hBpow : q ∣ w.B ^ w.n :=
      dvd_pow h.1 (exponent_ne_zero w.hn)
    have hApow : q ∣ w.A ^ w.m := by
      have : q ∣ w.A ^ w.m + w.B ^ w.n := w.equation ▸ hCpow
      exact (Nat.dvd_add_left hBpow).mp this
    exact hq.dvd_of_dvd_pow hApow

/-- A prime cannot divide all three bases: that would
contradict `gcd = 1`. -/
theorem not_prime_dvd_all_three (w : PrimitiveBealTriple)
    {q : Nat} (hq : q.Prime) :
    ¬ (q ∣ w.A ∧ q ∣ w.B ∧ q ∣ w.C) := by
  intro h
  have hg : q ∣ Nat.gcd w.A (Nat.gcd w.B w.C) :=
    Nat.dvd_gcd h.1 (Nat.dvd_gcd h.2.1 h.2.2)
  have h1 : q ∣ 1 := w.primitive ▸ hg
  exact hq.ne_one (Nat.eq_one_of_dvd_one h1)

/-- Pairwise coprimality from the primitive Beal equation.
This is the true gcd step, not a displayed `rfl` token. -/
theorem pairwise_coprime (w : PrimitiveBealTriple) :
    Nat.Coprime w.A w.B ∧ Nat.Coprime w.B w.C ∧ Nat.Coprime w.A w.C := by
  refine ⟨?hAB, ?hBC, ?hAC⟩
  · exact Nat.coprime_of_dvd fun q hq hA hB =>
      not_prime_dvd_all_three w hq
        ⟨hA, hB, (prime_dvd_two_implies_third w hq).1 ⟨hA, hB⟩⟩
  · exact Nat.coprime_of_dvd fun q hq hB hC =>
      not_prime_dvd_all_three w hq
        ⟨(prime_dvd_two_implies_third w hq).2.2 ⟨hB, hC⟩, hB, hC⟩
  · exact Nat.coprime_of_dvd fun q hq hA hC =>
      not_prime_dvd_all_three w hq
        ⟨hA, (prime_dvd_two_implies_third w hq).2.1 ⟨hA, hC⟩, hC⟩

theorem odd_prime_ne_two {q : Nat} (hq : q.Prime) (hodd : q ≠ 2) :
    ¬ q ∣ 16 := by
  intro h16
  have h2 : q ∣ 2 := hq.dvd_of_dvd_pow (by
    have : 16 = 2 ^ 4 := rfl
    exact this ▸ h16)
  have : q = 2 := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2
  exact hodd this

/-- Natural-number shape of `c₄ / 16`. -/
def freyC4Nat (w : PrimitiveBealTriple) : Nat :=
  16 * ((w.A ^ w.m) ^ 2 + w.A ^ w.m * w.B ^ w.n + (w.B ^ w.n) ^ 2)

theorem frey_c4_eq_nat (w : PrimitiveBealTriple) :
    (freyCurveOf w).c₄ = (freyC4Nat w : Int) := by
  rw [frey_c4_formula, freyC4Nat]
  push_cast
  rfl

theorem frey_Delta_eq_nat (w : PrimitiveBealTriple) :
    (freyCurveOf w).Δ =
      ((16 * (w.A ^ w.m) ^ 2 * (w.B ^ w.n) ^ 2 * (w.C ^ w.p) ^ 2 : Nat) : Int) := by
  rw [frey_Delta_of_equation]
  push_cast
  rfl

/-- An odd prime dividing `ABC` divides `Δ`. -/
theorem odd_prime_dvd_Delta (w : PrimitiveBealTriple)
    {q : Nat} (hq : q.Prime) (hdvd : q ∣ w.A * w.B * w.C) :
    (q : Int) ∣ (freyCurveOf w).Δ := by
  have hNat :
      q ∣ 16 * (w.A ^ w.m) ^ 2 * (w.B ^ w.n) ^ 2 * (w.C ^ w.p) ^ 2 := by
    have hsq {x e : Nat} (he : e ≠ 0) (hx : q ∣ x) : q ∣ (x ^ e) ^ 2 :=
      dvd_pow (dvd_pow hx he) (by decide)
    have hABC := (Nat.Prime.dvd_mul hq).mp hdvd
    rcases hABC with hAB | hC
    · rcases (Nat.Prime.dvd_mul hq).mp hAB with hA | hB
      · exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left
            (dvd_mul_of_dvd_right (hsq (exponent_ne_zero w.hm) hA) _) _) _
      · exact dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right (hsq (exponent_ne_zero w.hn) hB) _) _
    · exact dvd_mul_of_dvd_right (hsq (exponent_ne_zero w.hp) hC) _
  rw [frey_Delta_eq_nat]
  exact Int.natCast_dvd_natCast.mpr hNat

/-- True gcd step, part 2: an odd prime dividing `ABC` does
not divide `c₄`. -/
theorem odd_prime_not_dvd_c4 (w : PrimitiveBealTriple)
    {q : Nat} (hq : q.Prime) (hodd : q ≠ 2)
    (hdvd : q ∣ w.A * w.B * w.C) :
    ¬ (q : Int) ∣ (freyCurveOf w).c₄ := by
  intro hc4
  have hc4N : q ∣ freyC4Nat w := by
    rw [frey_c4_eq_nat] at hc4
    exact Int.natCast_dvd_natCast.mp hc4
  have h16k : q ∣ 16 * ((w.A ^ w.m) ^ 2 + w.A ^ w.m * w.B ^ w.n +
      (w.B ^ w.n) ^ 2) := hc4N
  have hquad :
      q ∣ (w.A ^ w.m) ^ 2 + w.A ^ w.m * w.B ^ w.n + (w.B ^ w.n) ^ 2 := by
    rcases (Nat.Prime.dvd_mul hq).mp h16k with h16 | hQ
    · exact (odd_prime_ne_two hq hodd h16).elim
    · exact hQ
  have hABC := (Nat.Prime.dvd_mul hq).mp hdvd
  have hCop := pairwise_coprime w
  rcases hABC with hAB | hC
  · rcases (Nat.Prime.dvd_mul hq).mp hAB with hA | hB
    · have hA0 : q ∣ w.A ^ w.m := dvd_pow hA (exponent_ne_zero w.hm)
      have hA02 : q ∣ (w.A ^ w.m) ^ 2 := dvd_pow hA0 (by decide)
      have hAmB : q ∣ w.A ^ w.m * w.B ^ w.n :=
        dvd_mul_of_dvd_left hA0 _
      have hBn2 : q ∣ (w.B ^ w.n) ^ 2 := by
        have := hquad
        have hsum : q ∣ (w.A ^ w.m) ^ 2 + w.A ^ w.m * w.B ^ w.n :=
          dvd_add hA02 hAmB
        exact (Nat.dvd_add_right hsum).mp this
      have hB : q ∣ w.B := hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hBn2)
      exact coprime_not_dvd_both hCop.1 hq hA hB
    · have hB0 : q ∣ w.B ^ w.n := dvd_pow hB (exponent_ne_zero w.hn)
      have hB02 : q ∣ (w.B ^ w.n) ^ 2 := dvd_pow hB0 (by decide)
      have hAmB : q ∣ w.A ^ w.m * w.B ^ w.n :=
        dvd_mul_of_dvd_right hB0 _
      have hAm2 : q ∣ (w.A ^ w.m) ^ 2 := by
        have hsum : q ∣ w.A ^ w.m * w.B ^ w.n + (w.B ^ w.n) ^ 2 :=
          dvd_add hAmB hB02
        have hassoc :
            (w.A ^ w.m) ^ 2 + w.A ^ w.m * w.B ^ w.n + (w.B ^ w.n) ^ 2 =
              (w.A ^ w.m) ^ 2 + (w.A ^ w.m * w.B ^ w.n + (w.B ^ w.n) ^ 2) := by
          ac_rfl
        exact (Nat.dvd_add_left hsum).mp (hassoc ▸ hquad)
      have hA : q ∣ w.A := hq.dvd_of_dvd_pow (hq.dvd_of_dvd_pow hAm2)
      exact coprime_not_dvd_both hCop.1 hq hA hB
  · have hC0 : q ∣ w.C ^ w.p := dvd_pow hC (exponent_ne_zero w.hp)
    have hEq : q ∣ w.A ^ w.m + w.B ^ w.n := w.equation ▸ hC0
    have hBnot : ¬ q ∣ w.B := fun hB => coprime_not_dvd_both hCop.2.1 hq hB hC
    have hAnot : ¬ q ∣ w.A := fun hA => coprime_not_dvd_both hCop.2.2 hq hA hC
    have hAm : ¬ q ∣ w.A ^ w.m := fun h =>
      hAnot (hq.dvd_of_dvd_pow h)
    have hBn : ¬ q ∣ w.B ^ w.n := fun h =>
      hBnot (hq.dvd_of_dvd_pow h)
    have hId :
        (w.A ^ w.m + w.B ^ w.n) ^ 2 =
          ((w.A ^ w.m) ^ 2 + w.A ^ w.m * w.B ^ w.n + (w.B ^ w.n) ^ 2) +
            w.A ^ w.m * w.B ^ w.n := by
      ring
    have hsq : q ∣ (w.A ^ w.m + w.B ^ w.n) ^ 2 :=
      dvd_pow hEq (by decide)
    have hAmBn : q ∣ w.A ^ w.m * w.B ^ w.n := by
      have hsum : q ∣
          ((w.A ^ w.m) ^ 2 + w.A ^ w.m * w.B ^ w.n + (w.B ^ w.n) ^ 2) +
            w.A ^ w.m * w.B ^ w.n := hId ▸ hsq
      exact (Nat.dvd_add_right hquad).mp hsum
    rcases (Nat.Prime.dvd_mul hq).mp hAmBn with hA | hB
    · exact hAm hA
    · exact hBn hB

/-- Odd-prime multiplicative valuation input from the true
gcd step.  Not Kodaira `Iₙ`. -/
theorem odd_prime_multiplicative_valuation
    (w : PrimitiveBealTriple) {q : Nat}
    (hq : q.Prime) (hodd : q ≠ 2)
    (hdvd : q ∣ w.A * w.B * w.C) :
    OddPrimeMultiplicativeValuationInput26 q (w.A : Int) (w.B : Int) w.m w.n :=
  { prime := hq
    discriminant_ne_zero := by
      simpa [freyCurveOf] using frey_Delta_ne_zero w
    prime_dvd_discriminant := by
      simpa [freyCurveOf] using odd_prime_dvd_Delta w hq hdvd
    prime_not_dvd_c4 := by
      simpa [freyCurveOf] using odd_prime_not_dvd_c4 w hq hodd hdvd }

theorem odd_prime_c4_val_zero_Delta_val_pos
    (w : PrimitiveBealTriple) {q : Nat}
    (hq : q.Prime) (hodd : q ≠ 2)
    (hdvd : q ∣ w.A * w.B * w.C) :
    freyC4Valuation26 q (w.A : Int) (w.B : Int) w.m w.n = 0 ∧
      0 < freyDiscriminantValuation26 q (w.A : Int) (w.B : Int) w.m w.n :=
  oddPrimeMultiplicativeValuationInput26_values
    (odd_prime_multiplicative_valuation w hq hodd hdvd)

/-! ## Uninhabited Tate / conductor obligations

Mathlib 4.12 has no Kodaira types, no minimality predicate
for Weierstrass models, and no conductor.  The names below
are the typed holes.  They are empty `Type`s / uninhabited
`Prop`s, **not** `sorry`.
-/

/-- Empty witness that `E` is minimal at `p`.  Not a Mathlib
Néron model. -/
inductive IsMinimalAtWitness (E : WeierstrassCurve Int) (p : Nat) : Type

def IsMinimalAt (E : WeierstrassCurve Int) (p : Nat) : Prop :=
  Nonempty (IsMinimalAtWitness E p)

/-- Empty witness that the local conductor exponent of `E`
at `p` equals `e`. -/
inductive ConductorExponentWitness
    (E : WeierstrassCurve Int) (p : Nat) : Nat → Type

def conductorExponentAt_eq
    (E : WeierstrassCurve Int) (p e : Nat) : Prop :=
  Nonempty (ConductorExponentWitness E p e)

/-- Empty witness that the global conductor of `E` equals `N`. -/
inductive GlobalConductorWitness
    (E : WeierstrassCurve Int) : Nat → Type

def globalConductor_eq (E : WeierstrassCurve Int) (N : Nat) : Prop :=
  Nonempty (GlobalConductorWitness E N)

/-- Square-free radical of `A B C`. -/
def radABC (A B C : Nat) : Nat :=
  (A * B * C).primeFactors.prod id

/-- Typed hole: the Frey model is minimal at every odd prime
dividing `ABC`.  Uninhabited. -/
def frey_minimal_model_at_odd_prime : Prop :=
  ∀ (w : PrimitiveBealTriple) (q : Nat),
    q.Prime → q ≠ 2 → q ∣ w.A * w.B * w.C →
    IsMinimalAt (freyCurveOf w) q

/-- Typed hole: odd-prime conductor exponent `1`.  Uninhabited. -/
def frey_conductor_exponent_one_odd : Prop :=
  ∀ (w : PrimitiveBealTriple) (q : Nat),
    q.Prime → q ≠ 2 → q ∣ w.A * w.B * w.C →
    conductorExponentAt_eq (freyCurveOf w) q 1

/-- Typed hole: 2-adic conductor exponent `1` by Tate at 2,
not the displayed `2 * 13` token.  Uninhabited. -/
def frey_conductor_two : Prop :=
  ∀ (w : PrimitiveBealTriple),
    conductorExponentAt_eq (freyCurveOf w) 2 1

/-- Typed hole: `N = 2 · rad(ABC)`.  Uninhabited. -/
def frey_global_conductor : Prop :=
  ∀ (w : PrimitiveBealTriple),
    globalConductor_eq (freyCurveOf w) (2 * radABC w.A w.B w.C)

/-- Supplier: 2-adic exponent-one packaged as data, matching
the parent `FreyConductorData_26.twoAdicExponent` field.
Not a theorem that the exponent is `1`. -/
structure FreyTwoAdicExponentOneCertificate
    (E : WeierstrassCurve Int) where
  exponent_one : Prop
  exponent_one_witness : exponent_one

/-- Supplier: 2-adic conductor packaged as data. -/
structure FreyTwoAdicConductorCertificate
    (E : WeierstrassCurve Int) where
  exponent : FreyTwoAdicExponentOneCertificate E
  semistable : Prop
  semistable_witness : semistable

theorem two_adic_exponent_one_of_certificate
    {E : WeierstrassCurve Int}
    (d : FreyTwoAdicExponentOneCertificate E) :
    d.exponent_one :=
  d.exponent_one_witness

theorem two_adic_semistable_of_certificate
    {E : WeierstrassCurve Int}
    (d : FreyTwoAdicConductorCertificate E) :
    d.semistable :=
  d.semistable_witness

/-- Re-export of the parent conductor-data divisibility.
Still supplied, still not Tate. -/
theorem supplied_conductor_divides_two_pow_times_radical
    (d : FreyConductorData_26) :
    d.freyConductor ∣ 2 ^ d.twoAdicExponent * d.radical :=
  Frey_conductor_of_data d

/-- Lock: this module does not inhabit the quantified Beal
statement.  The name is recorded so later slices cannot
quietly change the goal. -/
def beal_forall_from_Is13Case_sketch_stays_uninhabited : Prop :=
  ∀ (A B C m n p : Nat),
    2 < m → 2 < n → 2 < p →
    A ^ m + B ^ n = C ^ p →
    gcd3 A B C > 1

#check PrimitiveBealTriple
#check freyCurveOf
#check frey_Delta_formula
#check frey_Delta_of_equation
#check frey_c4_formula
#check pairwise_coprime
#check odd_prime_not_dvd_c4
#check odd_prime_multiplicative_valuation
#check frey_minimal_model_at_odd_prime
#check frey_conductor_exponent_one_odd
#check frey_conductor_two
#check frey_global_conductor
#check FreyTwoAdicExponentOneCertificate
#check FreyTwoAdicConductorCertificate
#check beal_forall_from_Is13Case_sketch_stays_uninhabited
#print axioms frey_Delta_of_equation
#print axioms pairwise_coprime
#print axioms odd_prime_not_dvd_c4
#print axioms odd_prime_c4_val_zero_Delta_val_pos
#print axioms two_adic_exponent_one_of_certificate
#print axioms supplied_conductor_divides_two_pow_times_radical

end BealLevel26Foundations.Beal.FullProof.TrueConductor
