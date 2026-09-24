import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic.NormNum

/-!
The exponent split, not elimination of the 2^k branch. A bounded
(4,4,13) computation is not a general theorem for (4,4,n).
-/

namespace Beal.General

theorem positive_exponent_split : ∀ n : ℕ, 0 < n →
    (∃ k : ℕ, n = 2 ^ k) ∨
    (∃ ell : ℕ, Nat.Prime ell ∧ 3 ≤ ell ∧ ell ∣ n) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hn1 : n = 1
    · exact Or.inl ⟨0, by simp [hn1]⟩
    by_cases h2 : 2 ∣ n
    · have hlow : 2 ≤ n := Nat.le_of_dvd hn h2
      have hhalf : 0 < n / 2 := Nat.div_pos hlow (by norm_num)
      rcases ih (n / 2) (Nat.div_lt_self hn (by norm_num)) hhalf with
        ⟨k, hk⟩ | ⟨ell, hp, hge, hd⟩
      · refine Or.inl ⟨k + 1, ?_⟩
        calc
          n = (n / 2) * 2 := (Nat.div_mul_cancel h2).symm
          _ = 2 ^ (k + 1) := by rw [hk, pow_succ]
      · refine Or.inr ⟨ell, hp, hge, ?_⟩
        rw [← Nat.div_mul_cancel h2]
        exact dvd_mul_of_dvd_left hd 2
    · obtain ⟨ell, hp, hd⟩ := Nat.exists_prime_and_dvd hn1
      have hge : 3 ≤ ell := by
        have hne : ell ≠ 2 := by
          intro heq
          subst ell
          exact h2 hd
        have hle := hp.two_le
        omega
      exact Or.inr ⟨ell, hp, hge, hd⟩

theorem beal_exponent_split (p : ℕ) (hp : 3 ≤ p) :
    (∃ k : ℕ, 2 ≤ k ∧ p = 2 ^ k) ∨
    (∃ ell : ℕ, Nat.Prime ell ∧ 3 ≤ ell ∧ ell ∣ p) := by
  rcases positive_exponent_split p (by omega) with ⟨k, hk⟩ | h
  · left
    refine ⟨k, ?_, hk⟩
    by_contra hlt
    have hcases : k = 0 ∨ k = 1 := by omega
    rcases hcases with hz | ho
    · simp [hz] at hk
      omega
    · simp [ho] at hk
      omega
  · exact Or.inr h

theorem odd_prime_exponent_rewrite (x y z p q r ell : ℕ)
    (hdiv : ell ∣ p) (hsol : x ^ p + y ^ q = z ^ r) :
    (x ^ (p / ell)) ^ ell + y ^ q = z ^ r := by
  calc
    (x ^ (p / ell)) ^ ell + y ^ q = x ^ p + y ^ q := by
      rw [← pow_mul, Nat.div_mul_cancel hdiv]
    _ = z ^ r := hsol

theorem two_power_no_odd_prime_factor (k ell : ℕ)
    (hp : Nat.Prime ell) (hge : 3 ≤ ell) : ¬ ell ∣ 2 ^ k := by
  intro hd
  have htwo : ell ∣ 2 := hp.dvd_of_dvd_pow hd
  rcases (Nat.dvd_prime Nat.prime_two).mp htwo with h1 | h2
  · exact hp.ne_one h1
  · omega

theorem branch_separate (k : ℕ) (_hk : 2 ≤ k) :
    ¬ ∃ ell : ℕ, Nat.Prime ell ∧ 3 ≤ ell ∧ ell ∣ 2 ^ k := by
  rintro ⟨ell, hprime, hge, hdiv⟩
  exact two_power_no_odd_prime_factor k ell hprime hge hdiv

/- TODO: A separate, applicable Darmon–Merel-style treatment of
(4,4,n), with all its hypotheses and exceptional cases, is needed
before eliminating the pure powers of two, including exponent 4.
The exponent split and the bounded B ≤ 10⁶ check do not eliminate it. -/

#print axioms beal_exponent_split
#print axioms odd_prime_exponent_rewrite
#print axioms branch_separate

end Beal.General