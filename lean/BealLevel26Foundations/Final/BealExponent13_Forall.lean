import BealLevel26Foundations.Final.BealExponent13_Final

namespace BealLevel26Foundations.Final

/-!
# v4.5.0 ∀ *computational package* for exponent 13

`BealTheorem_Exponent13_Forall_Computational` is

`BealTheorem_Exponent13_Typed ∧ BealExponent13_Final_Package`.

That is the typed displayed-label implication
`fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`
plus `FreyLevel26`, plus
`X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`.

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

/-- Conjunction of the typed close and the Final package.
Not a Fermat / Beal forall. -/
def BealTheorem_Exponent13_Forall_Computational : Prop :=
  BealTheorem_Exponent13_Typed ∧ BealExponent13_Final_Package

theorem BealTheorem_Exponent13_Forall_Computational.certified :
    BealTheorem_Exponent13_Forall_Computational :=
  ⟨BealTheorem_Exponent13_Typed.certified,
    BealExponent13_Final_Package.certified⟩

#print axioms BealTheorem_Exponent13_Forall_Computational.certified

end BealLevel26Foundations.Final
