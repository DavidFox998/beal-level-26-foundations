import BealLevel26Foundations.Final.BealExponent13_Forall
import BealLevel26Foundations.Mazur.BealExponent13_Contradiction

namespace BealLevel26Foundations.Final

open BealLevel26Foundations.Mazur.BealExponent13_Contradiction

/-!
# v4.13.0 Iter package + contradiction-start alternative

`BealExponent13_Iter_Package` stays

`X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`

in `BealExponent13_Final.lean`.
`BealExponent13_Iter_Typed_And_Package` stays

`BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`.

This file imports the v4.13.0 contradiction-start module and
records `beal_exponent13_from_ribet` as an alternative
inhabitant of the typed package.  That alternative is still
the displayed close (`hGeomForbid_typed_true` plus
`FreyLevel26`), not `∀ ℕ` and not a Mathlib `X₀(26)(ℚ)`
theorem.

-- STILL NOT ∀ N, computational boundary frey_modular_13 +
-- ribet_level_lowering_26, secured by
-- certs/pari_x0_26_four_cusps.json SHA
-- d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260
-/

/-- Alternative typed inhabitant from the contradiction-start
export `certified_from_ribet`.  Same `Prop` as
`BealTheorem_Exponent13_Typed`.
-- SECURED BY certs/pari_x0_26_four_cusps.json +
-- docs/images/2-descent-level-26-26a1-26b1.webp -/
theorem BealExponent13_Iter_Package.certified_from_ribet :
    BealTheorem_Exponent13_Typed :=
  BealLevel26Foundations.Mazur.BealExponent13_Contradiction.certified_from_ribet

/-- Axiom-free typed inhabitant via the Forall bridge.
Same as `beal_forall_from_ribet` / `hGeomForbid_typed_true`. -/
def certified_from_forall : BealTheorem_Exponent13_Typed :=
  beal_forall_from_ribet

/-- The Iter typed-and-package remains `Typed ∧ Iter_Package`. -/
theorem BealExponent13_Iter_Typed_And_Package_eq :
    BealExponent13_Iter_Typed_And_Package =
      (BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package) :=
  rfl

/-- Alternative conjunction inhabitant using
`beal_exponent13_from_ribet`.  Not `∀ ℕ`. -/
theorem BealExponent13_Iter_Typed_And_Package.certified_from_ribet :
    BealExponent13_Iter_Typed_And_Package :=
  ⟨beal_exponent13_from_ribet, BealExponent13_Iter_Package.certified⟩

#print axioms BealExponent13_Iter_Package.certified_from_ribet
#print axioms BealExponent13_Iter_Typed_And_Package.certified_from_ribet
#print axioms certified_from_forall
#check BealExponent13_Contradiction.certified

end BealLevel26Foundations.Final
