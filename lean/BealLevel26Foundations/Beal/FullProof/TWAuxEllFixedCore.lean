/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v8.17.0 — Conductor-relative TW primes `N < Qᵢ`.
-/

import Mathlib.Data.Nat.Prime.Basic

namespace BealLevel26Foundations.Beal.FullProof.TWAuxEllFixedCore

/-- TW primes relative to a conductor `N`: `N < Qᵢ`
implies `Qᵢ ∤ N`.  Not `∀ N, ¬ Q₁ ∣ N`. -/
structure TWAuxEllFixed (ℓ N : Nat) where
  Q1ell : Nat
  Q2ell : Nat
  Q1_prime : Q1ell.Prime
  Q2_prime : Q2ell.Prime
  Q1_mod : Q1ell % ℓ = 1
  Q2_mod : Q2ell % (ℓ ^ 2) = 1
  Q1_ge5 : 5 ≤ Q1ell
  Q2_ge5 : 5 ≤ Q2ell
  Q1_ne_Q2 : Q1ell ≠ Q2ell
  Q1_gt_N : N < Q1ell
  Q2_gt_N : N < Q2ell

def TWAuxEllFixedExists (ℓ N : Nat) : Prop :=
  Nonempty (TWAuxEllFixed ℓ N)

theorem TWAuxEllFixed.Q1_not_dvd {ℓ N : Nat}
    (tw : TWAuxEllFixed ℓ N) (hN : 0 < N) : ¬ tw.Q1ell ∣ N := by
  intro h
  exact Nat.not_le.mpr tw.Q1_gt_N (Nat.le_of_dvd hN h)

theorem TWAuxEllFixed.Q2_not_dvd {ℓ N : Nat}
    (tw : TWAuxEllFixed ℓ N) (hN : 0 < N) : ¬ tw.Q2ell ∣ N := by
  intro h
  exact Nat.not_le.mpr tw.Q2_gt_N (Nat.le_of_dvd hN h)

end BealLevel26Foundations.Beal.FullProof.TWAuxEllFixedCore
