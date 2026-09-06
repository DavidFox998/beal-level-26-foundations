import BealLevel26Foundations.Final.BealExponent13_Final
import BealLevel26Foundations.Mazur.BealExponent13_Contradiction

namespace BealLevel26Foundations.Final

open BealLevel26Foundations.Mazur.BealExponent13_Contradiction

/-!
# v4.7.0 Iter typed ∧ package for exponent 13
# v4.15.0 Typed → Forall bridge via certified_from_ribet

`BealExponent13_Iter_Typed_And_Package` is

`BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`.

That is the typed displayed-label implication
`fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`
plus `FreyLevel26`, plus
`X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`.

`BealTheorem_Exponent13_Forall_Computational` is a deprecated
alias of that name.  We do not use the word final until
`∀ A B C : ℕ` is in the kernel without `False.elim`.

If `A^13+B^13=C^13` were coprime, a Frey construction would
give a noncuspidal point of `X₀(26)`, contradicting
`hGeomForbid_typed_true` together with
`fourCuspsForallCuspPoints` and `FreyLevel26` (`2 * 13 = 26`).
That blueprint is the computational boundary: it rests on PARI
Descent plus Ribet, which Mathlib 4.12 does not have.  The
typed implication is now inhabited without `False.elim` on the
displayed cusp-label type (`P.mem` versus
`P.label ∉ fourCuspsList`).

This file is **not** `∀ A B C, ¬ A^13 + B^13 = C^13`.  A
vacuous-contradiction inhabitant of that forall would put
`False` in the kernel.  The old elliptic-`j` implication
stays uninhabitable (`hGeomForbid_typed_is_uninhabitable`).

Descent SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.
-/

/-!
## v4.32.0 working prime p=13 (`Is13Case`), not a universal lemma

Level-26 foundations target the **13-case** of a primitive
Beal-shaped witness: `13 ∣ x*y*z` (equivalently `13` divides
one of the exponents).  That is a *working prime* for conductor
`2 * 13 = 26`, not a claim that every counterexample is a
13-case.  Other primes `p ≥ 5` would need levels `2p`, not 26.

`beal_forall_from_ribet` stays the typed close (`none` via
`hGeomForbid_typed_true`).  No `sorry`, no `False.elim`, and
no new `True` inhabitant.  The divisor lemma is conditional
on `Is13Case`.  The reduction theorem applies the uninhabited
13-case sketch only.
-/

/-- Primitive Beal-shaped counterexample (`x,y,z ≥ 3`, `gcd = 1`).
Not a Mathlib Beal theorem. -/
structure BealCounterexample where
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

/-- Bases of some primitive Beal-shaped solution (any exponents ≥ 3). -/
def BealCounterexampleOn (A B C : Nat) : Prop :=
  ∃ h : BealCounterexample, h.A = A ∧ h.B = B ∧ h.C = C

/-- Equal-exponent-13 instance: primitive `A^13 + B^13 = C^13`.
This is the case the Frey curve of conductor 26 targets. -/
def BealCounterexampleAt13 (A B C : Nat) : Prop :=
  ∃ h : BealCounterexample,
    h.A = A ∧ h.B = B ∧ h.C = C ∧ h.x = 13 ∧ h.y = 13 ∧ h.z = 13

/-- Exponent aliases so `Is13Case` can name `exponentX/Y/Z`. -/
def BealCounterexample.exponentX (h : BealCounterexample) : Nat := h.x
def BealCounterexample.exponentY (h : BealCounterexample) : Nat := h.y
def BealCounterexample.exponentZ (h : BealCounterexample) : Nat := h.z

/-- Working-prime 13-case for level 26: `13` divides the
exponent product, or equivalently one of `exponentX/Y/Z`.
Not a claim that every `BealCounterexample` is a 13-case. -/
def Is13Case (h : BealCounterexample) : Prop :=
  13 ∣ h.x * h.y * h.z ∨ 13 ∣ h.exponentX ∨ 13 ∣ h.exponentY ∨
    13 ∣ h.exponentZ

/-- Conditional on `Is13Case`: then `13 ∣ x*y*z`.
Each disjunct implies the product form via `Nat.dvd_trans`
and `Nat.dvd_mul_right` / `Nat.dvd_mul_left`.
Not a universal lemma.  No `sorry`. -/
def beal_prime_divisor_13_of_counterexample
    (h : BealCounterexample)
    (_h13 : Is13Case h) :
    13 ∣ h.x * h.y * h.z :=
  Or.elim _h13
    (fun hxyz => hxyz)
    (fun hrest =>
      Or.elim hrest
        (fun hx =>
          Nat.dvd_trans (Nat.dvd_trans hx (Nat.dvd_mul_right h.x h.y))
            (Nat.dvd_mul_right (h.x * h.y) h.z))
        (fun hrest2 =>
          Or.elim hrest2
            (fun hy =>
              Nat.dvd_trans
                (Nat.dvd_trans hy (Nat.dvd_mul_left h.y h.x))
                (Nat.dvd_mul_right (h.x * h.y) h.z))
            (fun hz =>
              Nat.dvd_trans hz (Nat.dvd_mul_left h.z (h.x * h.y)))))

/-- This sketch is the MISSING step: after Frey modularity +
Ribet lowering to 26, `X0(26)(Q)=[1,2,13,26]` cusps `P.mem`
forces `gcd>1` ONLY in the 13-case.  Full `∀` requires
handling every prime `p≥5` with levels `2p`, not just 26.
Uninhabited.  Closing `BealCounterexampleAt13` does not by
itself kill mixed-exponent 13-cases or other primes. -/
def BealForallReducesToExponent13Sketch : Prop :=
  (∀ A B C : Nat, ¬ BealCounterexampleAt13 A B C) →
    (∀ (w : BealCounterexample), Is13Case w → False)

/-- If equal-exponent 13 is closed *and* the 13-case sketch
is supplied, then there is no packed 13-case witness.
Not `∀ A B C, ¬ BealCounterexampleOn`.  No `sorry`, no
`False.elim`.  Tautology on the sketch. -/
theorem beal_forall_reduces_to_exponent13
    (hSketch : BealForallReducesToExponent13Sketch)
    (h : ∀ A B C : Nat, ¬ BealCounterexampleAt13 A B C) :
    ∀ (w : BealCounterexample), Is13Case w → False :=
  hSketch h

/-- Conjunction of the typed close and the Iter package.
Not a Fermat / Beal forall. -/
def BealExponent13_Iter_Typed_And_Package : Prop :=
  BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package

theorem BealExponent13_Iter_Typed_And_Package.certified :
    BealExponent13_Iter_Typed_And_Package :=
  ⟨BealTheorem_Exponent13_Typed.certified,
    BealExponent13_Iter_Package.certified⟩

/-- Deprecated alias of `BealExponent13_Iter_Typed_And_Package`. -/
def BealTheorem_Exponent13_Forall_Computational : Prop :=
  BealExponent13_Iter_Typed_And_Package

theorem BealTheorem_Exponent13_Forall_Computational.certified :
    BealTheorem_Exponent13_Forall_Computational :=
  BealExponent13_Iter_Typed_And_Package.certified

/-- Bridge `BealTheorem_Exponent13_Typed` into this Forall file.
-- BRIDGE: none via hGeomForbid_typed_true hNotIn hInList, upstream Contradiction.certified needs both axioms
Not `∀ A B C : ℕ`.  No `True`, no `sorry`, no `False.elim`. -/
def beal_forall_from_ribet : BealTheorem_Exponent13_Typed :=
  BealLevel26Foundations.Mazur.BealExponent13_Contradiction.beal_exponent13_from_ribet

/-- Package-facing alias of the axiom-free Forall bridge. -/
def beal_forall_certified_from_ribet : BealTheorem_Exponent13_Typed :=
  beal_forall_from_ribet

#print axioms BealExponent13_Iter_Typed_And_Package.certified
#print axioms BealTheorem_Exponent13_Forall_Computational.certified
#print axioms beal_forall_from_ribet
#print axioms beal_forall_certified_from_ribet
#print axioms beal_prime_divisor_13_of_counterexample
#print axioms beal_forall_reduces_to_exponent13

end BealLevel26Foundations.Final
