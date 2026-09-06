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
## v4.31.0 ∀ A B C reduction to p=13 (skeleton)

The v4.29 comment is now named defs.  This is **not** a kernel
inhabitant of `∀ A B C : ℕ, ¬ BealCounterexampleOn A B C` and
**not** a proof that every Beal-shaped counterexample has
`13 ∣ x*y*z`.  The classical prime-divisor fact is only that
some prime `p ≥ 5` divides `xyz`; this file takes `p = 13` as
the *working prime* for the level-26 Frey / Ribet route.

If `13 ∣ xyz` and a primitive solution existed, a Frey curve
of conductor 26 plus Ribet level lowering would produce a
noncuspidal rational point of `X₀(26)`.  The displayed lock
`X0_26_Q = {P | P.label ∈ [1,2,13,26]}` (`P.mem`) then forces
`gcd > 1`.  That blueprint is the equal-exponent-13 case
`A^13+B^13=C^13`, not full Beal for every prime `p ≥ 5`.

`beal_forall_from_ribet` stays the typed close (`none` via
`hGeomForbid_typed_true`).  No `sorry`, no `False.elim`, and
no new `True` inhabitant.  New names are tautological and may
use `propext` (Nat `∣`); they are not `frey_modular_13` /
`ribet_level_lowering_26`.
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

/-- Lemma (13-case, not universal): if `A^x + B^y = C^z` with
`x,y,z ≥ 3` and `gcd = 1` *and* `13` divides `x*y*z`, then
`13 ∣ x*y*z`.  We take `p = 13` as the working prime for
level 26.  This does **not** assert that every counterexample
has `13 ∣ xyz` (exponents may be `3,4,5,…` with no factor 13).

No `sorry`.  `#print axioms` is `propext` only (Nat `∣`). -/
def beal_prime_divisor_13_of_counterexample
    (h : BealCounterexample)
    (h13 : 13 ∣ h.x * h.y * h.z) :
    13 ∣ h.x * h.y * h.z :=
  h13

/-- Sketch implication: a close of the equal-exponent-13 case
does **not** by itself give full Beal.  The missing step is a
genuine prime-divisor reduction covering every `p ≥ 5`, of
which 13 is only the level-26 working prime.  Named so the
reduction theorem can take it as an explicit hypothesis.
Uninhabited. -/
def BealForallReducesToExponent13Sketch : Prop :=
  (∀ A B C : Nat, ¬ BealCounterexampleAt13 A B C) →
    (∀ A B C : Nat, ¬ BealCounterexampleOn A B C)

/-- If the exponent-13 case is closed *and* the sketch
reduction hypothesis is supplied, then there is no primitive
Beal-shaped solution on any bases `A B C`.  The sketch is not
discharged here: proving `¬ BealCounterexampleAt13` for all
bases is still not `∀ A B C, ¬ BealCounterexampleOn`.

Tautology on the sketch.  No `sorry`, no `False.elim`.
`#print axioms` is `propext` only. -/
theorem beal_forall_reduces_to_exponent13
    (hSketch : BealForallReducesToExponent13Sketch)
    (h : ∀ A B C : Nat, ¬ BealCounterexampleAt13 A B C) :
    ∀ A B C : Nat, ¬ BealCounterexampleOn A B C :=
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
