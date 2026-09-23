/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import KolyvaginCurve.MordellWeilFintype
import Mathlib.Algebra.Homology.ShortComplex.Basic
import Mathlib.Tactic

/-!
# Two-Selmer exact-sequence interface

This module defines typed data for

`0 → E(ℚ)/2E(ℚ) → Sel₂(E) → Sha(E)[2] → 0`.

No formal Selmer group or exact sequence is constructed by the numerical
cardinalities in the project.
-/

namespace BealMatveevBeal.KolyvaginCurve

/-- The subgroup `2E(ℚ)` of doubles in the project's Mordell--Weil group. -/
def twiceMordellWeilSubgroup (E : WeierstrassCurve ℚ) :
    AddSubgroup (ProjectMordellWeilGroup E) where
  carrier := {x | ∃ y, y + y = x}
  zero_mem' := ⟨0, by simp⟩
  add_mem' := by
    rintro x y ⟨a, rfl⟩ ⟨b, rfl⟩
    refine ⟨a + b, ?_⟩
    abel
  neg_mem' := by
    rintro x ⟨a, rfl⟩
    refine ⟨-a, ?_⟩
    abel

/-- Typed construction and exactness data for the two-Selmer sequence. -/
structure TwoSelmerExactSequence (E : WeierstrassCurve ℚ) where
  Sel2 : AddCommGrp
  Sha2 : AddCommGrp
  mwModTwoToSelmer :
    (ProjectMordellWeilGroup E ⧸ twiceMordellWeilSubgroup E) →+ Sel2
  selmerToShaTwo : Sel2 →+ Sha2
  left_injective : Function.Injective mwModTwoToSelmer
  exact_middle : Function.Exact mwModTwoToSelmer selmerToShaTwo
  right_surjective : Function.Surjective selmerToShaTwo
  sel2Fintype : Fintype Sel2

/-- Cardinality of the constructed formal two-Selmer group. -/
def TwoSelmerExactSequence.sel2Card {E : WeierstrassCurve ℚ}
    (s : TwoSelmerExactSequence E) : ℕ :=
  @Fintype.card s.Sel2 s.sel2Fintype

/-- Construction target for both displayed curves. -/
def twoSelmer_exact_sequence : Prop :=
  Nonempty (TwoSelmerExactSequence.{0, 0}
      BealMatveevBeal.BSD_MordellWeil.curve26a1_Q) ∧
    Nonempty (TwoSelmerExactSequence.{0, 0}
      BealMatveevBeal.BSD_MordellWeil.curve26b1_Q)

/-- Forward bridge from singleton formal Selmer groups and finite generation
to finite Mordell--Weil groups.  This is the missing algebraic theorem, not a
restatement of the displayed cardinalities. -/
def singleton_twoSelmer_implies_MW_finite : Prop :=
  ∀
    (s26a1 : TwoSelmerExactSequence.{0, 0}
      BealMatveevBeal.BSD_MordellWeil.curve26a1_Q)
    (s26b1 : TwoSelmerExactSequence.{0, 0}
      BealMatveevBeal.BSD_MordellWeil.curve26b1_Q),
    s26a1.sel2Card = 1 →
    s26b1.sel2Card = 1 →
    MordellWeil_26a1_finitely_generated →
    MordellWeil_26b1_finitely_generated →
      MW_rank_zero_26a1_fintype ∧ MW_rank_zero_26b1_fintype

#check twiceMordellWeilSubgroup
#check TwoSelmerExactSequence
#check TwoSelmerExactSequence.sel2Card
#check twoSelmer_exact_sequence
#check singleton_twoSelmer_implies_MW_finite

end BealMatveevBeal.KolyvaginCurve