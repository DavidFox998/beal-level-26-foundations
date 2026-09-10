/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v8.67.0 — Level 26 newforms skeleton
(displayed ledger prefixes, not Mathlib
cusp forms, not Kraus, not a Beal ∀).

Shows the first 20 coefficients of the locked
`CoefficientLedger_26` arrays for `26a1` /
`26b1` (LMFDB labels `26.2.a.a` / `26.2.a.b`
are displayed names, not a Mathlib
identification).  The Kraus-prime list is
the Track B `smallZsigPrimes` list
`[53, 79, 131, 157, 313, 443, 521, 547]`.

Does **not** import `RibetMazur` (that would
cycle).  Does **not** import
`Mathlib.NumberTheory.ModularForms.Basic`
(Mathlib 4.12 is not used as a modular-forms
engine here; these are `List Int` prefixes).
Not imported by the 24-module none chain.

`level26_a_eliminated_by_53`,
`level26_b_eliminated_by_443`, and
`kraus_elimination_q_13_level_26_proof_sketch`
stay uninhabited Props.  A p=53 or p=443
Φ₁₃ hit is not Kraus matching.
`kraus_elimination_q_13_level_26` stays a Prop.
`ExistsNewformLevel2` stays `0 ≠ 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.  No new Beal `∀`.
-/

import BealLevel26Foundations.CoefficientLedger_26
import BealLevel26Foundations.Beal.FullProof.Beal_4_13_13_Zsigmondy_Density_2M
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

namespace BealLevel26Foundations.Level26_Newforms

open BealLevel26Foundations.Chain.Level2
open BealLevel26Foundations.CoefficientLedger26
open BealLevel26Foundations.Beal_4_13_13_Zsigmondy_Density_2M
  (smallZsigPrimes)

/-- Displayed LMFDB count: two rational newforms
of weight 2 and level 26.  Not a Mathlib
cusp-form dimension theorem. -/
def s2_gamma0_26_dim_displayed : Nat := 2

theorem s2_gamma0_26_dim_displayed_eq :
    s2_gamma0_26_dim_displayed = 2 :=
  rfl

/-- Prefix `a₀,…,a₁₉` of locked `qExp_26a1`
(26a1 / displayed `26.2.a.a`).  Ledger lock
`a₃ = 1`, `a₅ = -3`. -/
def newform_26_a_qexp : List Int :=
  [0, 1, -1, 1, 1, -3, -1, -1, -1, -2, 3, 6, 1, 1, 1, -3, 1, -3, 2, 2]

/-- Prefix `a₀,…,a₁₉` of locked `qExp_26b1`
(26b1 / displayed `26.2.a.b`).  Ledger lock
`a₃ = -3`, `a₅ = -1`. -/
def newform_26_b_qexp : List Int :=
  [0, 1, 1, -3, 1, -1, -3, 1, 1, 6, -1, -2, -3, -1, 1, 3, 1, -3, 6, 6]

theorem newform_26_a_qexp_eq_ledger_prefix :
    newform_26_a_qexp = List.take 20 qExp_26a1 :=
  rfl

theorem newform_26_b_qexp_eq_ledger_prefix :
    newform_26_b_qexp = List.take 20 qExp_26b1 :=
  rfl

theorem newform_26_a_a3 : newform_26_a_qexp[3]? = some (1 : Int) := by
  decide

theorem newform_26_a_a5 : newform_26_a_qexp[5]? = some (-3 : Int) := by
  decide

theorem newform_26_b_a3 : newform_26_b_qexp[3]? = some (-3 : Int) := by
  decide

theorem newform_26_b_a5 : newform_26_b_qexp[5]? = some (-1 : Int) := by
  decide

/-- Track B small Zsigmondy primes, copied as the
Kraus-side prime list.  Equality with
`smallZsigPrimes` is `rfl`, not a matching theorem. -/
def kraus_primes_26 : List Nat :=
  [53, 79, 131, 157, 313, 443, 521, 547]

theorem kraus_primes_26_eq_smallZsigPrimes :
    kraus_primes_26 = smallZsigPrimes :=
  rfl

/-- Displayed Kraus congruence at `ℓ = 13`.
Not a theorem that Frey traces match a newform. -/
def kraus_condition (a_p_E a_p_f : Int) : Prop :=
  (a_p_E : ZMod 13) = (a_p_f : ZMod 13)

/-- The Kraus-prime list is the Track B list, and
the named-row count is `4488 + 5 * 299 = 5983`.
This does **not** inhabit Kraus matching. -/
theorem zsig_density_links_to_kraus :
    kraus_primes_26 = smallZsigPrimes ∧
      4488 + 5 * 299 = 5983 :=
  ⟨kraus_primes_26_eq_smallZsigPrimes, rfl⟩

/-- Uninhabited.  A p=53 Φ₁₃ hit is not Kraus
elimination of 26a1. -/
def level26_a_eliminated_by_53 : Prop :=
  BealLevel26Foundations.Beal_4_13_13_Zsigmondy_Density_2M.kraus_elimination_q_13_level_26

/-- Uninhabited.  A p=443 Φ₁₃ hit is not Kraus
elimination of 26b1. -/
def level26_b_eliminated_by_443 : Prop :=
  BealLevel26Foundations.Beal_4_13_13_Zsigmondy_Density_2M.kraus_elimination_q_13_level_26

/-- Uninhabited.  Conjunction of the two
placeholders is still not Kraus. -/
def kraus_elimination_q_13_level_26_proof_sketch : Prop :=
  level26_a_eliminated_by_53 ∧ level26_b_eliminated_by_443

/-- Uninhabited.  Kraus matching at `q = 13`, level 26. -/
def kraus_elimination_q_13_level_26 : Prop :=
  BealLevel26Foundations.Beal_4_13_13_Zsigmondy_Density_2M.kraus_elimination_q_13_level_26

/-- Uninhabited.  Remaining `∀ B C` Hensel lock. -/
def exists_p_with_order_ne_13_mod_p_sq_inhabited : Prop :=
  BealLevel26Foundations.Beal_4_13_13_Zsigmondy_Density_2M.exists_p_with_order_ne_13_mod_p_sq_inhabited

/-- Uninhabited.  Named rows are not every gap-3 pair. -/
def S_has_prime_with_exp_one_when_C_ge_B_plus_3 : Prop :=
  BealLevel26Foundations.Beal_4_13_13_Zsigmondy_Density_2M.S_has_prime_with_exp_one_when_C_ge_B_plus_3

theorem ExistsNewformLevel2_eq_zero_ne_zero :
    ExistsNewformLevel2 = ((0 : Nat) ≠ 0) :=
  BealLevel26Foundations.Beal_4_13_13_Zsigmondy_Density_2M.ExistsNewformLevel2_eq_zero_ne_zero

#check newform_26_a_qexp
#check newform_26_b_qexp
#check kraus_primes_26
#check zsig_density_links_to_kraus
#check kraus_condition
#check level26_a_eliminated_by_53
#check kraus_elimination_q_13_level_26_proof_sketch
#check kraus_elimination_q_13_level_26
#check ExistsNewformLevel2_eq_zero_ne_zero
#print axioms newform_26_a_qexp_eq_ledger_prefix
#print axioms newform_26_a_a3
#print axioms newform_26_b_a5
#print axioms kraus_primes_26_eq_smallZsigPrimes
#print axioms zsig_density_links_to_kraus
#print axioms ExistsNewformLevel2_eq_zero_ne_zero

end BealLevel26Foundations.Level26_Newforms
