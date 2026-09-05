import BealLevel26Foundations.Descent.TwoDescent_26a1_26
import Mathlib.Tactic

namespace BealLevel26Foundations.Descent.Selmer26

open BealLevel26Foundations.Descent.TwoDescent26

/-!
# v4.1.0 Selmer / Sha *names* on displayed torsion-order Nats

Blueprint: `Sel₂(E/ℚ)` sits in `H¹(G_ℚ, E[2])`, with exact sequence
`0 → E(ℚ)/2E(ℚ) → Sel₂ → Sha[2] → 0`.  Rank `0` and `Sha[2] = 0`
would give `|Sel₂| = |E(ℚ)/2E(ℚ)|`.

This file does not construct that sequence.  Mathlib 4.12 has no
`SelmerGroup`.  Not a Selmer group.  Not Sha[2] triviality.  Not a
Mordell--Weil theorem.

`Sha2_26a1_trivial` is `SelmerBound_26a1 = 3`, i.e. `3 = 3`.
`Sha2_26b1_trivial` is `7 = 7`.  `RankZero_*_from_Selmer` aliases
those equalities.  They do not replace
`J0_26_Q_RankZero26.of_qExpansion.rankZero` and will need an actual
descent computation (for example from Sage JSON) before they can be
more than displayed Nat equalities.

The frozen v1.4.0 ledger SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`
is unchanged.
-/

/-- `3 = 3` on the displayed torsion-order Nat.  Not Sha[2] triviality. -/
def Sha2_26a1_trivial : Prop := SelmerBound_26a1 = 3

/-- `7 = 7` on the displayed torsion-order Nat.  Not Sha[2] triviality. -/
def Sha2_26b1_trivial : Prop := SelmerBound_26b1 = 7

/-- Alias of `Sha2_26a1_trivial` (`3 = 3`).  Not a Mordell--Weil theorem. -/
def RankZero_26a1_from_Selmer : Prop := Sha2_26a1_trivial

/-- Alias of `Sha2_26b1_trivial` (`7 = 7`).  Not a Mordell--Weil theorem. -/
def RankZero_26b1_from_Selmer : Prop := Sha2_26b1_trivial

theorem RankZero_26a1_from_Selmer.certified : RankZero_26a1_from_Selmer :=
  rfl

theorem RankZero_26b1_from_Selmer.certified : RankZero_26b1_from_Selmer :=
  rfl

theorem Sha2_26a1_trivial_is_three_eq_three : Sha2_26a1_trivial = (3 = 3) :=
  rfl

theorem Sha2_26b1_trivial_is_seven_eq_seven : Sha2_26b1_trivial = (7 = 7) :=
  rfl

#print axioms RankZero_26a1_from_Selmer.certified
#print axioms RankZero_26b1_from_Selmer.certified

end BealLevel26Foundations.Descent.Selmer26
