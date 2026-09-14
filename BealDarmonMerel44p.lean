/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Lake's LEAN_PATH puts the relocated kernel's `Beal/`
  prefix first, so `Beal.Matveev.*` cannot be imported from siblings.
  Do **not** import `Beal.Matveev.MatveevThm14General`.
-/
import Mathlib
import BealDarmonMerel
import BealKraus
import BealCatalanZsig

/-!
# Darmon–Merel signature (4,4,p) / Ribet-to-32 no-go
(not a `B ≤ 10⁶` close)

Successor of `406931f` (`v24-v24x-final-Darmon-Merel-nogo`).
Darmon–Merel for signature `(4,4,n)` needs `gcd(x,y) = 1`.
On gap-3, `3 ∣ B` forces `3 ∣ A`, so that hypothesis fails.
When `3 ∤ B` one has `gcd(A,B) = 1`, but Darmon–Merel is not
in Mathlib 4.12. Ribet at `13` yields uniform level 32 on the
displayed residual estimate `32 rad(AB)` only if `rad(AB) = 1`,
hence `A = B = 1`, which are 13th powers. On a genuine solution
with `B > 0`, `B` is even so `2 ∣ AB` and the residual is not 32.
If every prime valuation of `n` is a multiple of 13 then `n` is
a 13th power; `A = a¹³` and `B = b¹³` rewrites the equation as
`(a⁴)¹³ + (b⁴)¹³ = C¹³`, Fermat exponent 13, which is not in
Mathlib 4.12. An unlowered prime in `A` still survives (`13 ∤ 8`)
and `A > B0` on `B ≥ B0`.

Darmon–Merel, Ribet-to-32, and FLT stay `def Prop`.
`baker_bound_gap3` stays uninhabited. Not v25.
`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

namespace BealMatveevBeal.BealDarmonMerel44p

open BealMatveevBeal.BealDarmonMerel
open BealMatveevBeal.BealKraus
open BealMatveevBeal.BealCatalanZsig

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_dm :
    C1_floor = BealMatveevBeal.BealDarmonMerel.C1_floor := rfl

theorem B0_nat_eq_dm :
    B0_nat = BealMatveevBeal.BealDarmonMerel.B0_nat := rfl

theorem C1_floor_eq_kraus :
    C1_floor = BealMatveevBeal.BealKraus.C1_floor := rfl

theorem B0_nat_eq_kraus :
    B0_nat = BealMatveevBeal.BealKraus.B0_nat := rfl

/-! ## Displayed residual `32 rad(AB)` is not 32 on a solution -/

theorem residualLevelEstimate_eq (A B : ℕ) :
    residualLevelEstimate A B = 32 * natRadical (A * B) :=
  rfl

theorem two_dvd_mul_of_even {A B : ℕ} (hB : Even B) : 2 ∣ A * B :=
  dvd_mul_of_dvd_right (even_iff_two_dvd.mp hB) A

theorem natRadical_ne_one_of_even_pos {A B : ℕ}
    (hA : A ≠ 0) (hB : 0 < B) (he : Even B) :
    natRadical (A * B) ≠ 1 := by
  have h2 : 2 ∣ A * B := two_dvd_mul_of_even he
  have hne : A * B ≠ 0 := mul_ne_zero hA (Nat.pos_iff_ne_zero.mp hB)
  have hmem : 2 ∈ (A * B).primeFactors := by
    rw [Nat.mem_primeFactors]
    exact ⟨Nat.prime_two, h2, hne⟩
  have hrad : 2 ∣ natRadical (A * B) :=
    Finset.dvd_prod_of_mem (fun q => q) hmem
  intro h1
  rw [h1] at hrad
  exact (by decide : ¬ (2 ∣ 1)) hrad

/-- On a gap-3 solution `B` is even, so `2` divides `AB` and the
    displayed residual `32 rad(AB)` is not 32. This is **not** the
    Néron conductor. -/
theorem residualLevelEstimate_ne_thirty_two_of_sol {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) :
    residualLevelEstimate A B ≠ 32 := by
  have hA : A ≠ 0 := A_ne_zero_of_sol hsol hB
  have he : Even B := B_even_of_sol hsol
  have hrad : natRadical (A * B) ≠ 1 :=
    natRadical_ne_one_of_even_pos hA hB he
  intro h
  have hmul : 32 * natRadical (A * B) = 32 * 1 := by
    simpa [residualLevelEstimate] using h
  have : natRadical (A * B) = 1 :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 32) hmul
  exact hrad this

/-- If the displayed residual were 32, then `rad(AB) = 1`, so
    `A = B = 1`, which are 13th powers. Uniform level 32 on this
    estimate therefore requires thirteenth powers — and does not
    occur on a positive gap-3 solution. -/
theorem uniform_level_32_requires_A_B_pth_powers {A B : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0)
    (h : residualLevelEstimate A B = 32) :
    (∃ a, A = a ^ 13) ∧ (∃ b, B = b ^ 13) := by
  have hmul : 32 * natRadical (A * B) = 32 * 1 := by
    simpa [residualLevelEstimate] using h
  have hrad : natRadical (A * B) = 1 :=
    Nat.eq_of_mul_eq_mul_left (by decide : 0 < 32) hmul
  have hn : A * B ≠ 0 := mul_ne_zero hA hB
  have hempty : (A * B).primeFactors = ∅ := by
    by_contra hne
    obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hpP : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpdvd : p ∣ natRadical (A * B) :=
      Finset.dvd_prod_of_mem (fun q => q) hp
    rw [hrad] at hpdvd
    exact hpP.not_dvd_one hpdvd
  have hAB : A * B = 1 := by
    have h01 := (Nat.primeFactors_eq_empty (n := A * B)).1 hempty
    rcases h01 with h0 | h1
    · exact (hn h0).elim
    · exact h1
  have hA1 : A = 1 := Nat.eq_one_of_mul_eq_one_right hAB
  have hB1 : B = 1 := Nat.eq_one_of_mul_eq_one_left hAB
  exact ⟨⟨1, by simp [hA1]⟩, ⟨1, by simp [hB1]⟩⟩

/-! ## Thirteenth powers and Fermat shape `(a⁴)¹³ + (b⁴)¹³ = C¹³` -/

theorem thirteen_dvd_padicValNat_pow {a p : ℕ} (hp : p.Prime) :
    13 ∣ padicValNat p (a ^ 13) := by
  by_cases ha : a = 0
  · subst ha
    simp
  · haveI : Fact p.Prime := ⟨hp⟩
    rw [padicValNat.pow 13 ha]
    exact dvd_mul_right _ _

theorem exists_thirteenth_root_of_thirteen_dvd_padic {n : ℕ}
    (hn : n ≠ 0)
    (h : ∀ p, Nat.Prime p → 13 ∣ padicValNat p n) :
    ∃ m, n = m ^ 13 := by
  let m := n.factorization.prod fun p e => p ^ (e / 13)
  refine ⟨m, ?_⟩
  have hself : n.factorization.prod (· ^ ·) = n :=
    Nat.factorization_prod_pow_eq_self hn
  apply Eq.symm
  calc
    m ^ 13
        = (n.factorization.support.prod fun p =>
            p ^ (n.factorization p / 13)) ^ 13 := by
          simp only [m, Finsupp.prod]
    _ = n.factorization.support.prod fun p =>
            (p ^ (n.factorization p / 13)) ^ 13 := by
          rw [Finset.prod_pow]
    _ = n.factorization.support.prod fun p =>
            p ^ n.factorization p := by
          refine Finset.prod_congr rfl ?_
          intro p hp
          have hpP : p.Prime :=
            Nat.prime_of_mem_primeFactors (by
              simpa [Nat.support_factorization] using hp)
          have h13 : 13 ∣ n.factorization p := by
            rw [Nat.factorization_def n hpP]
            exact h p hpP
          rw [← pow_mul, Nat.mul_comm, Nat.mul_div_cancel' h13]
    _ = n := by
          simpa [Finsupp.prod] using hself

/-- If `A = a¹³` and `B = b¹³` solve `A⁴ + B⁴ = C¹³`, the equation
    is Fermat of exponent 13. FLT is not in Mathlib 4.12. -/
theorem fermat_shape_of_A_B_pth_powers {a b C : ℕ}
    (hsol : (a ^ 13) ^ 4 + (b ^ 13) ^ 4 = C ^ 13) :
    (a ^ 4) ^ 13 + (b ^ 4) ^ 13 = C ^ 13 := by
  have hA : (a ^ 13) ^ 4 = (a ^ 4) ^ 13 := by
    rw [← pow_mul, ← pow_mul]
  have hB : (b ^ 13) ^ 4 = (b ^ 4) ^ 13 := by
    rw [← pow_mul, ← pow_mul]
  rw [hA, hB] at hsol
  exact hsol

theorem fermat_shape_of_sol_thirteenth_powers {a b A B C : ℕ}
    (hA : A = a ^ 13) (hB : B = b ^ 13)
    (hsol : A ^ 4 + B ^ 4 = C ^ 13) :
    (a ^ 4) ^ 13 + (b ^ 4) ^ 13 = C ^ 13 := by
  subst hA
  subst hB
  exact fermat_shape_of_A_B_pth_powers hsol

/-! ## Signature (4,4,p) still does not cut `B ≤ 10⁶` -/

theorem darmon_merel_hypothesis_fails_when_three_dvd_B_reexport
    {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (h3 : 3 ∣ B) :
    ¬ Nat.Coprime A B :=
  darmon_merel_hypothesis_fails_when_three_dvd_B hsol h3

theorem kraus_uniform_residual_level_32_nogo_reexport {p A B : ℕ}
    (hp : p.Prime)
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B)
    (hp6 : ¬ p ∣ 6) (hpA : p ∣ A)
    (hnot13 : ¬ 13 ∣ padicValNat p A) :
    p ∣ residualLevelEstimate A B ∧
      ¬ 13 ∣ padicValNat p (freyDiscNat A B) ∧
      B0_nat < A ∧
      ¬ residualLevelEstimate A B ∣ 32 := by
  have hB0dm : BealMatveevBeal.BealDarmonMerel.B0_nat ≤ B := by
    simpa [B0_nat_eq_dm] using hB0
  have h := kraus_uniform_residual_level_32_nogo hp hsol hB hB0dm hp6 hpA hnot13
  refine ⟨h.1, h.2.1, ?_, h.2.2.2⟩
  simpa [B0_nat_eq_dm] using h.2.2.1

/-- Even assuming Darmon–Merel signature `(4,4,p)` (uninhabited)
    and Ribet-to-32 (uninhabited), gap-3 with `B ≥ B0` is not a
    uniform level-32 check: `3 ∣ B` kills coprimeness; the displayed
    residual is not 32 because `B` is even; `A > B0` and `13 ∤ 8`. -/
theorem baker_bound_gap3_darmon_merel_44p_nogo {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (3 ∣ B → ¬ Nat.Coprime A B) ∧
      residualLevelEstimate A B ≠ 32 ∧
      B0_nat < A ∧
      ¬ 13 ∣ 8 ∧ 13 ∣ 26 := by
  have hB0dm : BealMatveevBeal.BealDarmonMerel.B0_nat ≤ B := by
    simpa [B0_nat_eq_dm] using hB0
  have hnogo := baker_bound_gap3_darmon_merel_nogo hsol hB hB0dm
  refine ⟨hnogo.1, residualLevelEstimate_ne_thirty_two_of_sol hsol hB, ?_,
    hnogo.2.2⟩
  simpa [B0_nat_eq_dm] using hnogo.2.1

theorem baker_bound_gap3_darmon_merel_44p_nogo_val :
    ¬ 13 ∣ 8 ∧ 13 ∣ 26 :=
  ⟨not_thirteen_dvd_eight, thirteen_dvd_twenty_six⟩

/-! ## Locked uninhabited Props -/

/-- Darmon–Merel signature `(4,4,n)` for `n ≥ 4`. Not in Mathlib 4.12. -/
def darmon_merel_signature_44p : Prop :=
  BealMatveevBeal.BealDarmonMerel.darmon_merel_signature_44p

/-- Residual conductor after Ribet at 13 equals 32 for every gap-3
    Frey curve. False for the displayed estimate on `B > 0`, and not
    the Néron conductor. Not in Mathlib 4.12. -/
def ribet_level_lowering_to_32 : Prop :=
  ∀ A B : ℕ, A ^ 4 + B ^ 4 = (B + 3) ^ 13 → 0 < B →
    residualLevelEstimate A B = 32

def ribet_level_lowering : Prop :=
  BealMatveevBeal.BealDarmonMerel.ribet_level_lowering

/-- Fermat's Last Theorem at exponent 13. Not in Mathlib 4.12. -/
def fermat_last_theorem_thirteen : Prop :=
  ∀ x y z : ℕ, x ^ 13 + y ^ 13 = z ^ 13 → x * y * z = 0

def baker_bound_gap3 : Prop :=
  BealMatveevBeal.BealDarmonMerel.baker_bound_gap3

def kraus_uniform_residual_level : Prop :=
  BealMatveevBeal.BealDarmonMerel.kraus_uniform_residual_level

def darmon_merel_x4_y4_zp_no_coprime_solutions : Prop :=
  BealMatveevBeal.BealDarmonMerel.darmon_merel_x4_y4_zp_no_coprime_solutions

#check C1_floor_eq
#check B0_nat_eq
#check residualLevelEstimate_ne_thirty_two_of_sol
#check uniform_level_32_requires_A_B_pth_powers
#check exists_thirteenth_root_of_thirteen_dvd_padic
#check fermat_shape_of_A_B_pth_powers
#check baker_bound_gap3_darmon_merel_44p_nogo
#check baker_bound_gap3
#check darmon_merel_signature_44p
#check ribet_level_lowering_to_32
#check fermat_last_theorem_thirteen
#print axioms residualLevelEstimate_ne_thirty_two_of_sol
#print axioms uniform_level_32_requires_A_B_pth_powers
#print axioms exists_thirteenth_root_of_thirteen_dvd_padic
#print axioms fermat_shape_of_A_B_pth_powers
#print axioms baker_bound_gap3_darmon_merel_44p_nogo

end BealMatveevBeal.BealDarmonMerel44p
