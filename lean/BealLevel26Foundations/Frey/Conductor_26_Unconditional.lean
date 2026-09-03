import BealLevel26Foundations.Frey.FreyConductorUnconditional_26
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace BealLevel26Foundations.Frey.Conductor26Unconditional

open BealLevel26Foundations.Frey.FreyConductorUnconditional26

/-!
# Odd-prime valuation input for the Frey conductor

Mathlib 4.12 has no elliptic-curve conductor, Kodaira symbols, or Tate
algorithm.  This module therefore proves the valuation statement that is
available unconditionally and does not define a conductor exponent to be one
by fiat.

For a nonzero discriminant, `p ∤ c₄` gives `vₚ(c₄)=0`.  Combined with
`p ∣ Δ`, this is the arithmetic input used by Tate's algorithm to identify
multiplicative type `Iₙ`, where `n=vₚ(Δ)`, and local conductor exponent one.
The classification implication is not present in Mathlib 4.12, so the full
equality `N = 2^e * rad(ABC)` remains outside this unconditional module.
-/

def freyC4Valuation26
    (p : Nat) (A B : Int) (x y : Nat) : Nat :=
  padicValInt p (freyCurve A B x y).c₄

def freyDiscriminantValuation26
    (p : Nat) (A B : Int) (x y : Nat) : Nat :=
  padicValInt p (freyCurve A B x y).Δ

theorem freyC4Valuation26_eq_zero
    {p : Nat} [Fact p.Prime] {A B : Int} {x y : Nat}
    (hc4 : ¬ (p : Int) ∣ (freyCurve A B x y).c₄) :
    freyC4Valuation26 p A B x y = 0 := by
  exact padicValInt.eq_zero_of_not_dvd hc4

theorem freyDiscriminantValuation26_ne_zero
    {p : Nat} [Fact p.Prime] {A B : Int} {x y : Nat}
    (hΔ0 : (freyCurve A B x y).Δ ≠ 0)
    (hpΔ : (p : Int) ∣ (freyCurve A B x y).Δ) :
    freyDiscriminantValuation26 p A B x y ≠ 0 := by
  have hpPow : (p : Int) ^ 1 ∣ (freyCurve A B x y).Δ := by
    simpa using hpΔ
  have hPositive :
      1 ≤ freyDiscriminantValuation26 p A B x y := by
    exact ((padicValInt_dvd_iff 1 (freyCurve A B x y).Δ).mp hpPow).resolve_left hΔ0
  omega

structure OddPrimeMultiplicativeValuationInput26
    (p : Nat) (A B : Int) (x y : Nat) : Prop where
  prime : p.Prime
  discriminant_ne_zero : (freyCurve A B x y).Δ ≠ 0
  prime_dvd_discriminant : (p : Int) ∣ (freyCurve A B x y).Δ
  prime_not_dvd_c4 : ¬ (p : Int) ∣ (freyCurve A B x y).c₄

theorem oddPrimeMultiplicativeValuationInput26_values
    {p : Nat} {A B : Int} {x y : Nat}
    (h : OddPrimeMultiplicativeValuationInput26 p A B x y) :
    freyC4Valuation26 p A B x y = 0 ∧
      freyDiscriminantValuation26 p A B x y ≠ 0 := by
  letI : Fact p.Prime := ⟨h.prime⟩
  exact ⟨freyC4Valuation26_eq_zero h.prime_not_dvd_c4,
    freyDiscriminantValuation26_ne_zero h.discriminant_ne_zero
      h.prime_dvd_discriminant⟩

#print axioms freyC4Valuation26_eq_zero
#print axioms freyDiscriminantValuation26_ne_zero
#print axioms oddPrimeMultiplicativeValuationInput26_values

end BealLevel26Foundations.Frey.Conductor26Unconditional