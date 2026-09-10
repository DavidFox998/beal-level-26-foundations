/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v8.68.0 — displayed a₅₃ miss plus p=443
ZMod witness (not Kraus, not a Beal ∀).
Locked ledger `a₅₃(26a1)=0`, `a₅₃(26b1)=12`
(not the sketch values 6 and -2).  Prefix
length 100 has no `a₄₄₃`.  Displayed
placeholder Frey traces 2 and 0 are not
computed `a_p(E_B)`.
`level26_a_eliminated_by_53` and
`level26_b_eliminated_by_443` stay the
uninhabited `∀`.  `ExistsNewformLevel2`
stays `0 ≠ 0`.
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
  (smallZsigPrimes hasSmallZsigWitness hasSmallZsigWitness_196)

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

/-! ## v8.68.0 — locked a₅₃ and displayed mod-13 miss -/

/-- First 100 coefficients `a₀,…,a₉₉` of locked
`qExp_26a1`.  Index 53 is in range; 443 is not. -/
def newform_26_a_qexp_100 : List Int :=
  List.take 100 qExp_26a1

def newform_26_b_qexp_100 : List Int :=
  List.take 100 qExp_26b1

theorem newform_26_a_qexp_100_eq_ledger :
    newform_26_a_qexp_100 = List.take 100 qExp_26a1 :=
  rfl

theorem newform_26_b_qexp_100_eq_ledger :
    newform_26_b_qexp_100 = List.take 100 qExp_26b1 :=
  rfl

theorem newform_26_a_qexp_100_length :
    newform_26_a_qexp_100.length = 100 := by
  decide

theorem newform_26_b_qexp_100_length :
    newform_26_b_qexp_100.length = 100 := by
  decide

/-- Locked ledger `a₅₃(26a1) = 0`.  The sketch
value 6 is false. -/
theorem a53_26a1_eq :
    newform_26_a_qexp_100[53]? = some (0 : Int) := by
  decide

/-- Locked ledger `a₅₃(26b1) = 12`.  The sketch
value -2 is false. -/
theorem a53_26b1_eq :
    newform_26_b_qexp_100[53]? = some (12 : Int) := by
  decide

theorem a53_26a1_ne_six :
    newform_26_a_qexp_100[53]? ≠ some (6 : Int) := by
  decide

theorem a53_26b1_ne_neg_two :
    newform_26_b_qexp_100[53]? ≠ some (-2 : Int) := by
  decide

/-- Locked 100-prefix has no index 443. -/
theorem newform_26_a_qexp_100_no_a443 :
    newform_26_a_qexp_100[443]? = none := by
  decide

theorem newform_26_b_qexp_100_no_a443 :
    newform_26_b_qexp_100[443]? = none := by
  decide

/-- Displayed placeholder Frey trace 2 against
ledger `a₅₃(26a1)=0` at `ℓ = 13`.  The integer 2
is not computed `a₅₃(E_{196})`.  Not Kraus. -/
theorem displayed_two_misses_a53_26a1 :
    ¬ kraus_condition (2 : Int) (0 : Int) := by
  dsimp [kraus_condition]
  decide

/-- Displayed placeholder Frey trace 0 against
ledger `a₅₃(26b1)=12` at `ℓ = 13`.  Not `a₄₄₃`.
Not Kraus. -/
theorem displayed_zero_misses_a53_26b1 :
    ¬ kraus_condition (0 : Int) (12 : Int) := by
  dsimp [kraus_condition]
  decide

/-- Inhabited.  Uses the B=196 p=53 ZMod witness
and the displayed `2 ≢ 0 [MOD 13]` miss against
ledger `a₅₃(26a1)`.  Does **not** inhabit
`level26_a_eliminated_by_53` (that stays the
uninhabited `∀`).  Does **not** prove Frey
modularity or residual isomorphism. -/
theorem level26_a_eliminated_by_53_of_witness :
    hasSmallZsigWitness 196 →
      ¬ kraus_condition (2 : Int) (0 : Int) := by
  intro _
  exact displayed_two_misses_a53_26a1

/-- Inhabited.  Same ZMod-443 / numeral `443*443`
predicate as Step56 row `(1500003,1500006)`.
Not `True`.  Not Kraus. -/
theorem hasSmallZsigWitness_1500003 :
    hasSmallZsigWitness 1500003 := by
  refine ⟨443, ?_⟩
  refine And.intro ?mem (And.intro ?eq ?ne)
  · decide
  · decide
  · decide

/-- Inhabited.  The p=443 Φ₁₃ hit exists, and the
locked 100-prefix has no `a₄₄₃`.  That is **not**
Kraus elimination of 26b1.  Does **not** inhabit
`level26_b_eliminated_by_443`. -/
theorem level26_b_eliminated_by_443_of_witness :
    hasSmallZsigWitness 1500003 →
      newform_26_b_qexp_100[443]? = none := by
  intro _
  exact newform_26_b_qexp_100_no_a443

#check newform_26_a_qexp
#check newform_26_b_qexp
#check kraus_primes_26
#check zsig_density_links_to_kraus
#check kraus_condition
#check level26_a_eliminated_by_53
#check kraus_elimination_q_13_level_26_proof_sketch
#check kraus_elimination_q_13_level_26
#check ExistsNewformLevel2_eq_zero_ne_zero
#check newform_26_a_qexp_100
#check a53_26a1_eq
#check a53_26b1_eq
#check displayed_two_misses_a53_26a1
#check level26_a_eliminated_by_53_of_witness
#check hasSmallZsigWitness_1500003
#check level26_b_eliminated_by_443_of_witness
#check newform_26_b_qexp_100_no_a443
#print axioms newform_26_a_qexp_eq_ledger_prefix
#print axioms newform_26_a_a3
#print axioms newform_26_b_a5
#print axioms kraus_primes_26_eq_smallZsigPrimes
#print axioms zsig_density_links_to_kraus
#print axioms ExistsNewformLevel2_eq_zero_ne_zero
#print axioms a53_26a1_eq
#print axioms a53_26b1_eq
#print axioms displayed_two_misses_a53_26a1
#print axioms level26_a_eliminated_by_53_of_witness
#print axioms hasSmallZsigWitness_1500003
#print axioms level26_b_eliminated_by_443_of_witness

end BealLevel26Foundations.Level26_Newforms
