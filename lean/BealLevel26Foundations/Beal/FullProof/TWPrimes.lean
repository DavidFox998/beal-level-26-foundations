/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v8.15.0 — Finite `Q₁ ≡ 1 [MOD ℓ]` table for every
prime `ℓ` with `5 ≤ ℓ ≤ 1000`.  Ten small Finsets; not
Dirichlet and not `∀ N ≤ 10000`.  `Q₂ ≡ 1 [MOD ℓ²]`
within `5·10⁶` fails for 56 residuals.

Does **not** inhabit `ExistsNewformLevel2` (`0 ≠ 0`).
Does **not** drop `ModularImpliesLevel2Newform`.
-/

import BealLevel26Foundations.Beal.FullProof.TWPrimes_5_100
import BealLevel26Foundations.Beal.FullProof.TWPrimes_101_200
import BealLevel26Foundations.Beal.FullProof.TWPrimes_201_300
import BealLevel26Foundations.Beal.FullProof.TWPrimes_301_400
import BealLevel26Foundations.Beal.FullProof.TWPrimes_401_500
import BealLevel26Foundations.Beal.FullProof.TWPrimes_501_600
import BealLevel26Foundations.Beal.FullProof.TWPrimes_601_700
import BealLevel26Foundations.Beal.FullProof.TWPrimes_701_800
import BealLevel26Foundations.Beal.FullProof.TWPrimes_801_900
import BealLevel26Foundations.Beal.FullProof.TWPrimes_901_1000
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

namespace BealLevel26Foundations.Beal.FullProof.TWPrimes

open BealLevel26Foundations.Beal.FullProof.TWPrimes_5_100
open BealLevel26Foundations.Beal.FullProof.TWPrimes_101_200
open BealLevel26Foundations.Beal.FullProof.TWPrimes_201_300
open BealLevel26Foundations.Beal.FullProof.TWPrimes_301_400
open BealLevel26Foundations.Beal.FullProof.TWPrimes_401_500
open BealLevel26Foundations.Beal.FullProof.TWPrimes_501_600
open BealLevel26Foundations.Beal.FullProof.TWPrimes_601_700
open BealLevel26Foundations.Beal.FullProof.TWPrimes_701_800
open BealLevel26Foundations.Beal.FullProof.TWPrimes_801_900
open BealLevel26Foundations.Beal.FullProof.TWPrimes_901_1000

/-- Membership in the 166-row table of primes in `[5, 1000]`.
The converse (`Nat.Prime ℓ → 5 ≤ ℓ → ℓ ≤ 1000 → InTWEll1000 ℓ`)
is not kernel-checked: `interval_cases` on those ranges
hits max recursion / heartbeats. -/
def InTWEll1000 (ℓ : Nat) : Prop :=
  ℓ ∈ primes5to100 ∨ ℓ ∈ primes101to200 ∨ ℓ ∈ primes201to300 ∨
    ℓ ∈ primes301to400 ∨ ℓ ∈ primes401to500 ∨ ℓ ∈ primes501to600 ∨
    ℓ ∈ primes601to700 ∨ ℓ ∈ primes701to800 ∨ ℓ ∈ primes801to900 ∨
    ℓ ∈ primes901to1000

/-- Smallest prime `Q₁ ≤ 20000` with `Q₁ ≡ 1 [MOD ℓ]`
for every residual in the 166-row table.  Not Dirichlet
and not a proof that every `Nat.Prime` in `[5, 1000]`
is in the table. -/
theorem exists_prime_one_mod_ell_all {ℓ : Nat}
    (h : InTWEll1000 ℓ) :
    ∃ Q1 : Nat, Q1.Prime ∧ Q1 % ℓ = 1 ∧ Q1 ≤ 20000 ∧ 5 ≤ Q1 := by
  rcases h with h | h | h | h | h | h | h | h | h | h
  · exact exists_prime_one_mod_ell_5_100 h
  · exact exists_prime_one_mod_ell_101_200 h
  · exact exists_prime_one_mod_ell_201_300 h
  · exact exists_prime_one_mod_ell_301_400 h
  · exact exists_prime_one_mod_ell_401_500 h
  · exact exists_prime_one_mod_ell_501_600 h
  · exact exists_prime_one_mod_ell_601_700 h
  · exact exists_prime_one_mod_ell_701_800 h
  · exact exists_prime_one_mod_ell_801_900 h
  · exact exists_prime_one_mod_ell_901_1000 h

theorem Q1_not_dvd_N_of_Q1_gt_N {Q1 N : Nat}
    (hN : 0 < N) (hgt : N < Q1) : ¬ Q1 ∣ N := by
  intro h
  exact Nat.not_le.mpr hgt (Nat.le_of_dvd hN h)

/-- Computable search for a prime `p` with `N < p ≤ bound`
and `p ≡ 1 [MOD ℓ]`.  May return `none`. -/
def find_next_prime_one_mod_gt (ℓ N bound : Nat) : Option Nat :=
  (List.range (bound + 1)).find? fun p =>
    N < p ∧ Nat.Prime p ∧ p % ℓ = 1

theorem find_next_prime_one_mod_gt_spec {ℓ N bound p : Nat}
    (h : find_next_prime_one_mod_gt ℓ N bound = some p) :
    N < p ∧ p.Prime ∧ p % ℓ = 1 ∧ p ≤ bound := by
  have hmem := List.mem_of_find?_eq_some h
  have hpred : N < p ∧ Nat.Prime p ∧ p % ℓ = 1 := by
    have := List.find?_some h
    exact of_decide_eq_true this
  have hle : p ≤ bound := Nat.lt_succ_iff.mp (List.mem_range.mp hmem)
  exact ⟨hpred.1, hpred.2.1, hpred.2.2, hle⟩

/-- Uninhabited.  56 primes `ℓ ≤ 1000` have no prime
`Q₂ ≡ 1 [MOD ℓ²]` at most `5·10⁶`. -/
def exists_prime_one_mod_ell_sq_all : Prop :=
  ∀ ℓ : Nat, ℓ.Prime → 5 ≤ ℓ → ℓ ≤ 1000 →
    ∃ Q2 : Nat, Q2.Prime ∧ Q2 % (ℓ * ℓ) = 1 ∧ Q2 ≤ 5000000

/-- Uninhabited.  A prime `≡ 1 [MOD ℓ]` in `(N, N+20000]`
for every `N ≤ 10000` is not a 166-row table. -/
def find_next_prime_one_mod_gt_exists : Prop :=
  ∀ ℓ N : Nat, ℓ.Prime → 5 ≤ ℓ → ℓ ≤ 1000 → N ≤ 10000 →
    ∃ Q1 : Nat, Q1.Prime ∧ Q1 % ℓ = 1 ∧ N < Q1 ∧ Q1 ≤ N + 20000

end BealLevel26Foundations.Beal.FullProof.TWPrimes
