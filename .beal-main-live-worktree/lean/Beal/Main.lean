import Beal.ConditionalBealTheorem

/-!
# The general Beal conclusion, conditional on its mathematical premises

The requested forward route would pass through Tate closure and Néron/inertia,
Mazur's `X₀(13)` and Frey-j/Borel exclusion, Ribet's `32a1` and Kraus
coefficient, Kolyvagin's L-value/Selmer evidence, the conditional level-32
bridge, the six-stage dependency table, and finally the bounded gap-3 search.
Those interfaces do not currently construct all of the general hypotheses
needed to enter the level-26 assembly. The assembly's seven-field certificate
package still requires Frey construction, modularity, level lowering, and
geometric soundness for arbitrary solutions.

The separate, kernel-checked foundations theorem excludes
`A ^ 4 + B ^ 4 = (B + 3) ^ 13` for `B ≤ 1000000`. That bounded statement
does not construct these general inputs. In particular, neither a Boolean
search nor the Tate–Mazur–Ribet–Kolyvagin numerical interfaces inhabits the
general common-prime theorem.
-/

namespace Beal.Main

open Beal17Mazur

/-- General common-prime formulation, with no hidden restriction on the
positive bases or exponents at least three. -/
def BealTheorem : Prop :=
  ∀ x y z p q r : ℕ,
    0 < x → 0 < y → 0 < z →
    3 ≤ p → 3 ≤ q → 3 ≤ r →
    x ^ p + y ^ q = z ^ r →
    ∃ d : ℕ, Nat.Prime d ∧ d ∣ x ∧ d ∣ y ∧ d ∣ z

/-- An arbitrary positive solution with exponents at least three.
No coprimality assumption is built into the general conclusion. -/
structure BealData where
  x : ℕ
  y : ℕ
  z : ℕ
  p : ℕ
  q : ℕ
  r : ℕ
  positiveX : 0 < x
  positiveY : 0 < y
  positiveZ : 0 < z
  exponentP : 3 ≤ p
  exponentQ : 3 ≤ q
  exponentR : 3 ≤ r
  equation : x ^ p + y ^ q = z ^ r

/-- Explicit mathematical premises of the existing conditional level-26
route. No constructor of this package is claimed here. -/
structure BealMainInputs (J0_26 : Type*) [AddCommGroup J0_26] where
  certificates : BealCertificates_26 J0_26

/-- Conditional deduction from the supplied level-26 certificates. The
primitive-counterexample contradiction gives a nontrivial gcd; a prime
dividing that gcd divides all three bases. -/
theorem beal_conditional_forward
    {J0_26 : Type*} [AddCommGroup J0_26]
    (inputs : BealMainInputs J0_26) (data : BealData) :
    ∃ d : ℕ, Nat.Prime d ∧ d ∣ data.x ∧ d ∣ data.y ∧ d ∣ data.z := by
  have hbeal : BealConjecture :=
    conditional_beal_of_certificates inputs.certificates
  have hgcd : Nat.gcd data.x (Nat.gcd data.y data.z) ≠ 1 := by
    intro hone
    exact hbeal data.x data.y data.z data.p data.q data.r
      ⟨data.positiveX, data.positiveY, data.positiveZ,
        (by omega), (by omega), (by omega), data.equation, hone⟩
  obtain ⟨d, hprime, hdvd⟩ := Nat.exists_prime_and_dvd hgcd
  refine ⟨d, hprime, ?_, ?_, ?_⟩
  · exact dvd_trans hdvd (Nat.gcd_dvd_left _ _)
  · exact dvd_trans hdvd
      (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_left _ _))
  · exact dvd_trans hdvd
      (dvd_trans (Nat.gcd_dvd_right _ _) (Nat.gcd_dvd_right _ _))

/-- This theorem is conditional: the `BealData` argument is not constructed
by the bounded million-search theorem. -/
theorem beal_main_theorem
    {J0_26 : Type*} [AddCommGroup J0_26]
    (inputs : BealMainInputs J0_26) : BealTheorem := by
  intro x y z p q r hx hy hz hp hq hr heq
  exact beal_conditional_forward inputs
    { x := x, y := y, z := z, p := p, q := q, r := r
      positiveX := hx, positiveY := hy, positiveZ := hz
      exponentP := hp, exponentQ := hq, exponentR := hr
      equation := heq }

#print axioms beal_main_theorem

end Beal.Main