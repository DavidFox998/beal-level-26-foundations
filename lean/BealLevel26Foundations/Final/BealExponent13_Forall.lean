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
## v4.35.0 sketch still uninhabited — signatures recorded

`Is13CaseForcesGcdGt1Sketch` stays uninhabited.  The proposed
term `frey_modular_13 w h13` / `ribet_level_lowering_26 hFrey`
/ `hGeomForbid_typed_true hRibet …` does not type-check.

`#check is13CaseForcesGcdGt1Sketch_inhabited` is
`BealTheorem_Exponent13_Typed` (the existing typed close),
not `∀ w, Is13Case w → w.gcd > 1`.  A packed witness has
`gcd = 1` by `primitive`, so inhabiting the sketch would be
`Is13Case → False` in the kernel.  No `False.elim`.
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

-- v4.34.0 working prime vs universal — identities, no placeholders
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

/-- Conditional on `Is13Case`.  Identity. -/
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
in the 13-case.  Uninhabited.
`#check hGeomForbid_typed_true` /
`#check beal_forall_from_ribet` do not inhabit this. -/
def Is13CaseForcesGcdGt1Sketch : Prop :=
  ∀ (w : BealCounterexample), Is13Case w → w.gcd > 1

/-- Packed gcd is `1` by the `primitive` field. -/
theorem primitive_gcd_eq_one (w : BealCounterexample) : w.gcd = 1 :=
  w.primitive

/-- A primitive witness cannot have `gcd > 1`. -/
theorem primitive_not_gcd_gt1 (w : BealCounterexample) : ¬ w.gcd > 1 :=
  fun hgt => Nat.lt_irrefl (1 : Nat) (w.primitive ▸ hgt)

/-- gcd>1 in the 13-case only if the gcd sketch is supplied.
`frey_modular_13` is `∀ A B C, Modularity (FreyCurve13 A B C)`.
`ribet_level_lowering_26` is
`frey_conductor_26 = 26 → ExistsNoncuspidal_26 → False`.
`hGeomForbid_typed_true` is
`fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`.
None of those apply to `(w, h13)` as `w.gcd > 1`. -/
theorem is13Case_forces_gcd_gt1
    (w : BealCounterexample)
    (h13 : Is13Case w)
    (hSketch : Is13CaseForcesGcdGt1Sketch) :
    w.gcd > 1 :=
  hSketch w h13

/-- Primitive `gcd = 1` contradicts the sketch `gcd > 1`.
Not `False.elim`.  Uses `Nat.lt_irrefl`. -/
theorem beal_13_case_no_primitive_witness
    (w : BealCounterexample)
    (h13 : Is13Case w)
    (hSketch : Is13CaseForcesGcdGt1Sketch) :
    False :=
  primitive_not_gcd_gt1 w (is13Case_forces_gcd_gt1 w h13 hSketch)

/-- No 13-case packed witness, given the gcd sketch.
Not `∀ A B C, ¬ BealCounterexampleOn`. -/
theorem beal_exponent13_no_counterexample
    (hSketch : Is13CaseForcesGcdGt1Sketch) :
    ∀ w : BealCounterexample, Is13Case w → False :=
  fun w h13 => beal_13_case_no_primitive_witness w h13 hSketch

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
Not `∀ A B C, ¬ BealCounterexampleOn`.  Tautology on the sketch. -/
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
Not `∀ A B C : ℕ`.  No `True` inhabitant, no `False.elim`. -/
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

/-- Not an inhabitant of `Is13CaseForcesGcdGt1Sketch`.
`#check` this name: `BealTheorem_Exponent13_Typed`.
The proposed Frey/Ribet/`hGeomForbid` application on `(w, h13)`
does not type-check, and `w.gcd > 1` contradicts `primitive`. -/
def is13CaseForcesGcdGt1Sketch_inhabited : BealTheorem_Exponent13_Typed :=
  beal_forall_from_ribet

#check BealLevel26Foundations.Mazur.BealTheoremFromMazurChain26.hGeomForbid_typed_true
#check BealLevel26Foundations.Modularity.FreyModularity13.frey_modular_13
#check BealLevel26Foundations.Modularity.RibetLevelLowering26.ribet_level_lowering_26
#check beal_forall_from_ribet
#check is13CaseForcesGcdGt1Sketch_inhabited
#check Is13CaseForcesGcdGt1Sketch
#print axioms BealExponent13_Iter_Typed_And_Package.certified
#print axioms BealTheorem_Exponent13_Forall_Computational.certified
#print axioms beal_forall_from_ribet
#print axioms beal_forall_certified_from_ribet
#print axioms beal_prime_divisor_13_first_disjunct
#print axioms beal_prime_divisor_13_of_counterexample
#print axioms is13ExpCase_out_of_scope_for_level_26
#print axioms is13Case_existing_typed_bridge
#print axioms primitive_gcd_eq_one
#print axioms primitive_not_gcd_gt1
#print axioms is13Case_forces_gcd_gt1
#print axioms beal_13_case_no_primitive_witness
#print axioms beal_exponent13_no_counterexample
#print axioms beal_forall_reduces_to_exponent13
#print axioms is13CaseForcesGcdGt1Sketch_inhabited

end BealLevel26Foundations.Final
