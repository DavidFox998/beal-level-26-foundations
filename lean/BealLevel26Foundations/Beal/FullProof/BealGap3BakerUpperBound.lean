/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v9.0.0 -- Baker / Bugeaud effective upper bound
for gap-3.  The missing bound.  Not inhabited.

Keeps the v8.86.0 B <= 2M residue theorems:
`beal_..._mod16` (B % 16 != 14) and
`beal_..._B14_full` (352 named B == 14 rows
via q = 53/29/109).  Those have empty axioms.
They are not a Mathlib Baker theorem.

The requested lemma is Baker/Bugeaud linear forms
in logarithms: exists B0 = 10^6 such that every
B > B0 has no A with A^4 + B^4 = (B+3)^13.
Mathlib 4.12 has no Baker theory and no
Bugeaud P(Phi13) > C theorem.  The existing
`bugeaud_P_phi13_gt_C_when_B_gt_2000000` is
already an uninhabited Prop.

`sorry` is forbidden by verify-scaffold.
`baker_bound_gap3` is therefore an uninhabited
Prop -- the honest hole -- not a sorry proof.
A future inhabit would be allowed to use
{propext, Classical.choice, Quot.sound};
Real.sqrt is not an axiom we add.
Not BCDT.

Does **not** inhabit
`exists_zsig_q_gt_2M_dvd_C13_sub_B4`
(needs Baker, not Zsig).
Does **not** inhabit
`beal_gap3_B_gt_2M_eliminated`.
Does **not** change `frey_conductor_general`.
`conductor_86` stays Prop.  `B14_honest`
stays Prop.  Density/Step kraus forall stays
uninhabited.  Chain ExistsNewformLevel2 stays
0 != 0.
Does **not** import `RibetMazur`,
`BealFreyB14`, or `FreyModularity_13`.
Not imported by the 24-module none chain.
-/

namespace BealLevel26Foundations.BealGap3BakerUpperBound

/-! ## Displayed Baker cutoff B0 = 10^6 -/

/-- Named cutoff in the requested Baker shape.
    Displayed Nat, not an effective bound. -/
def baker_B0 : Nat := 1000000

theorem baker_B0_eq : baker_B0 = 1000000 :=
  rfl

theorem baker_B0_eq_pow10_6 : baker_B0 = Nat.pow 10 6 :=
  rfl

/-! ## Missing effective bound (uninhabited) -/

/-- Missing Baker / Bugeaud linear-forms-in-logs
    bound: exists B0 = 10^6 such that every B > B0
    has no gap-3 solution.  Uninhabited Prop.
    Not closable from the 5983 census.
    `sorry` is not used (scaffold forbids it).
    This is the missing effective bound. -/
def baker_bound_gap3 : Prop :=
  ∃ B0 : Nat, B0 = Nat.pow 10 6 ∧
    ∀ B : Nat, B0 < B →
      ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13

/-- Same statement at the displayed numeral. -/
def baker_bound_gap3_at_B0 : Prop :=
  ∀ B : Nat, baker_B0 < B →
    ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13

#check baker_B0
#check baker_B0_eq
#check baker_B0_eq_pow10_6
#check baker_bound_gap3
#check baker_bound_gap3_at_B0
#print axioms baker_B0_eq
#print axioms baker_B0_eq_pow10_6

end BealLevel26Foundations.BealGap3BakerUpperBound
