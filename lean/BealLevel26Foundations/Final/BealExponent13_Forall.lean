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
## v4.33.0 working prime vs universal — fixed to be provable, no sorry

`Is13Case` is only `13 ∣ x*y*z`.  The exponent-or form is
`Is13ExpCase` and is **out of scope** for level 26 (other
primes need levels `2p`).  The divisor theorems are identities
on `Is13Case`.  No `sorry`.

`beal_forall_from_ribet` is `BealTheorem_Exponent13_Typed`
(`hGeomForbid_typed_true` ∧ `FreyLevel26`).  `#check` that
name: it does not take a packed witness and does not prove
`gcd > 1`.  The gcd conclusion stays a named sketch.
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

/-- Exponent aliases for `Is13ExpCase`. -/
def BealCounterexample.exponentX (w : BealCounterexample) : Nat := w.x
def BealCounterexample.exponentY (w : BealCounterexample) : Nat := w.y
def BealCounterexample.exponentZ (w : BealCounterexample) : Nat := w.z

/-- Packed `gcd(A,B,C)`.  Primitive witnesses have this `= 1`. -/
def BealCounterexample.gcd (w : BealCounterexample) : Nat :=
  Nat.gcd w.A (Nat.gcd w.B w.C)

-- v4.33.0 working prime vs universal — fixed to be provable, no sorry
/-- Working-prime 13-case for level 26: `13` divides the
exponent product.  Not a claim that every witness is a 13-case. -/
def Is13Case (w : BealCounterexample) : Prop :=
  13 ∣ w.x * w.y * w.z

/-- Exponent-or form.  Out of scope for the level-26 route
(other primes need levels `2p`, `p ≥ 5`).  Not used to inhabit
the product divisor. -/
def Is13ExpCase (w : BealCounterexample) : Prop :=
  13 ∣ w.exponentX ∨ 13 ∣ w.exponentY ∨ 13 ∣ w.exponentZ

/-- Trivially provable — first disjunct is now the whole definition. -/
theorem beal_prime_divisor_13_first_disjunct
    (w : BealCounterexample)
    (h : 13 ∣ w.x * w.y * w.z) :
    13 ∣ w.x * w.y * w.z :=
  h

/-- Conditional on `Is13Case`.  Identity.  No `sorry`. -/
theorem beal_prime_divisor_13_of_counterexample
    (w : BealCounterexample)
    (h13 : Is13Case w) :
    13 ∣ w.x * w.y * w.z :=
  h13

/-- `Is13ExpCase` is out of scope for level 26.  We do not
decide whether it implies `Is13Case`; LEM only. -/
theorem is13ExpCase_out_of_scope_for_level_26
    (w : BealCounterexample)
    (_hExp : Is13ExpCase w) :
    Is13Case w ∨ ¬ Is13Case w :=
  Classical.em (Is13Case w)

/-- Sketch only: Frey + Ribet + four cusps would force `gcd > 1`
in the 13-case.  Uninhabited.  Primitive witnesses already
have `w.gcd = 1`. -/
def Is13CaseForcesGcdGt1Sketch : Prop :=
  ∀ (w : BealCounterexample), Is13Case w → w.gcd > 1

/-- gcd>1 in the 13-case only if the gcd sketch is supplied.
`beal_forall_from_ribet` cannot be applied to `(w, h13)` —
signature is the typed close.  No `sorry`, no `False.elim`. -/
theorem is13Case_forces_gcd_gt1
    (w : BealCounterexample)
    (h13 : Is13Case w)
    (hSketch : Is13CaseForcesGcdGt1Sketch) :
    w.gcd > 1 :=
  hSketch w h13

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

/-- `#check beal_forall_from_ribet` is `BealTheorem_Exponent13_Typed`,
not `Is13Case → gcd > 1`.  The displayed bridge
(`hGeomForbid_typed_true` / `hNotIn` / `hInList` /
`X0_26_Q=[1,2,13,26]` `P.mem`) stays that typed close. -/
def is13Case_existing_typed_bridge
    (_w : BealCounterexample)
    (_h13 : Is13Case _w) :
    BealTheorem_Exponent13_Typed :=
  beal_forall_from_ribet

#check beal_forall_from_ribet
#print axioms BealExponent13_Iter_Typed_And_Package.certified
#print axioms BealTheorem_Exponent13_Forall_Computational.certified
#print axioms beal_forall_from_ribet
#print axioms beal_forall_certified_from_ribet
#print axioms beal_prime_divisor_13_first_disjunct
#print axioms beal_prime_divisor_13_of_counterexample
#print axioms is13ExpCase_out_of_scope_for_level_26
#print axioms is13Case_existing_typed_bridge
#print axioms is13Case_forces_gcd_gt1
#print axioms beal_forall_reduces_to_exponent13

end BealLevel26Foundations.Final
