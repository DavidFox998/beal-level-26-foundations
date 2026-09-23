/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.Newform32

/-!
# Kraus trace elimination

The trace functions below are exact aliases of the existing finite-field
point count and recorded `32a1` table.  The good-reduction `l = 29` mismatch
is already proved.  Classes with `29 ∣ A B (B+3)` are not eliminated by that
single scan and keep the complete theorem uninhabited.
-/

namespace BealMatveevBeal.RibetCurve

/-- Exact finite-field trace of the displayed Frey cubic. -/
def frey_ap (l A B : ℕ) : ℤ :=
  BealMatveevBeal.Level32Table.frey_ap l A B

/-- Recorded coefficient lookup for `32a1`. -/
def newform_32a1_ap (l : ℕ) : Option ℤ :=
  BealMatveevBeal.Level32Table.newform_32a1_ap l

theorem newform_32a1_a29 :
    newform_32a1_ap 29 = some (-10) :=
  BealMatveevBeal.Level32Table.newform_32a1_ap_29

/-- The existing complete finite scan at `29`, under good-reduction
hypotheses. -/
theorem frey_a29_mismatch_at_good_reduction
    {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : ¬ 29 ∣ B + 3) :
    frey_ap 29 (A % 29) (B % 29) ≠ (-10 : ℤ) :=
  BealMatveevBeal.Level32Table.no_match_32a1_of_good_red_29
    hsol hA hB hC

/-- Missing complete `a₂₉ mod 13`/multi-prime Kraus elimination, including
all bad-reduction residue classes. -/
def explicit_a29_mod13_complete_Kraus_elimination : Prop :=
  level_32_no_newform_for_Frey_gap3

#check frey_ap
#check newform_32a1_ap
#check newform_32a1_a29
#check frey_a29_mismatch_at_good_reduction
#check explicit_a29_mod13_complete_Kraus_elimination

end BealMatveevBeal.RibetCurve