import Beal.«Beal.General».Minimal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Preliminary invariant facts at 2. These are inputs to, not a replacement
for, the local minimal-model and Tate-algorithm computations required to
identify a Néron conductor. No conductor formula is asserted here.
-/

namespace Beal.General

private theorem odd_c4_factor (U V : ℕ) (h : Odd U ∨ Odd V) :
    Odd (U ^ 2 + U * V + V ^ 2) := by
  have hu : U % 2 = 0 ∨ U % 2 = 1 := by omega
  have hv : V % 2 = 0 ∨ V % 2 = 1 := by omega
  have hh : U % 2 = 1 ∨ V % 2 = 1 := by
    rcases h with h | h
    · exact Or.inl (Nat.odd_iff.mp h)
    · exact Or.inr (Nat.odd_iff.mp h)
  apply Nat.odd_iff.mpr
  rcases hu with hu | hu <;> rcases hv with hv | hv
  all_goals simp [Nat.add_mod, Nat.mul_mod, pow_two, hu, hv] at *

/-- Under primitive parity, the displayed integral model has
v₂(c₄)=4. It is not thereby known to be a minimal model. -/
theorem frey_c4_v2_of_parity (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (hparity : Odd (x ^ p) ∨ Odd (y ^ q)) :
    padicValInt 2 (freyWeierstrassGeneral x y z p q r).c₄ = 4 := by
  have hc4Nat :
      (freyWeierstrassGeneral x y z p q r).c₄ =
        ((16 * ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) : ℕ) : ℤ) := by
    rw [frey_c4]
    push_cast
    ring
  rw [hc4Nat]
  simp only [padicValInt, Int.natAbs_ofNat]
  have hS : (x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2 ≠ 0 := by positivity
  have h16 : padicValNat 2 16 = 4 := by
    change padicValNat 2 (2 ^ 4) = 4
    rw [padicValNat.pow 4 (by norm_num : (2 : ℕ) ≠ 0), padicValNat_self]
  have hSval :
      padicValNat 2 ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have hmod : ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd hd
    have hodd : ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) % 2 = 1 :=
      Nat.odd_iff.mp (odd_c4_factor (x ^ p) (y ^ q) hparity)
    rw [hodd] at hmod
    norm_num at hmod
  rw [padicValNat.mul (by norm_num : (16 : ℕ) ≠ 0) hS, h16, hSval]

/-- Coprime powered inputs cannot both be even. This still says
nothing about Kodaira type or the conductor exponent. -/
theorem frey_c4_v2_of_coprime (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (hcop : Nat.Coprime (x ^ p) (y ^ q)) :
    padicValInt 2 (freyWeierstrassGeneral x y z p q r).c₄ = 4 := by
  apply frey_c4_v2_of_parity x y z p q r hx hy
  rcases Nat.even_or_odd (x ^ p) with heU | hoU
  · rcases Nat.even_or_odd (y ^ q) with heV | hoV
    · exfalso
      rcases heU with ⟨u, hu⟩
      rcases heV with ⟨v, hv⟩
      have hdU : 2 ∣ x ^ p := ⟨u, by omega⟩
      have hdV : 2 ∣ y ^ q := ⟨v, by omega⟩
      have hgcd : 2 ∣ Nat.gcd (x ^ p) (y ^ q) := Nat.dvd_gcd hdU hdV
      have hcop' : Nat.gcd (x ^ p) (y ^ q) = 1 := hcop
      rw [hcop'] at hgcd
      norm_num at hgcd
    · exact Or.inr hoV
  · exact Or.inl hoU

/-- The displayed model has singular reduction modulo 2;
this alone cannot determine a Néron conductor. -/
theorem frey_discriminant_even (x y z p q r : ℕ) :
    (2 : ℤ) ∣ (freyWeierstrassGeneral x y z p q r).Δ := by
  rw [frey_delta_raw]
  refine ⟨8 * ((x : ℤ) ^ p) ^ 2 * ((y : ℤ) ^ q) ^ 2 *
    ((x : ℤ) ^ p + (y : ℤ) ^ q) ^ 2, ?_⟩
  ring

/- TODO: First determine a minimal integral model at every prime,
including each high-valuation case at 2. Then formalize the relevant
Tate-algorithm steps and derive the local conductor exponents. Neither
the raw v₂(c₄)=4, the discriminant valuation, nor singular reduction
implies an exponent or N=2^?*rad(x*y*z). No such formula is claimed. -/

#print axioms frey_c4_v2_of_coprime
#print axioms frey_discriminant_even

end Beal.General