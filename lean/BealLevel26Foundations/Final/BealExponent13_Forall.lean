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
Same inhabitant as `beal_exponent13_from_ribet`.
-- BRIDGE: Uses certified_from_ribet which is none via hGeomForbid, upstream certified needs both axioms
Not `∀ A B C : ℕ`.  No `True`, no `sorry`, no `False.elim`. -/
def beal_forall_from_ribet :=
  beal_exponent13_from_ribet

#print axioms BealExponent13_Iter_Typed_And_Package.certified
#print axioms BealTheorem_Exponent13_Forall_Computational.certified
#print axioms beal_forall_from_ribet

end BealLevel26Foundations.Final
