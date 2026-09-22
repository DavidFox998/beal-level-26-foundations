/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RibetCurve.Newform32

/-!
# Kraus trace-elimination scaffold

The functions below are aliases of the existing exact finite-field point
count and the recorded `32a1` coefficient table. The project proves a
mismatch at `29` under good-reduction hypotheses, but not a complete
elimination of all gap-3 residue classes: classes with `29 ∣ ABC` require
additional good primes or another argument.
-/

namespace BealMatveevBeal.RibetCurve

/-- Existing exact finite-field trace of the displayed Frey cubic. -/
def frey_ap (l A B : ℕ) : ℤ :=
  BealMatveevBeal.Level32Table.frey_ap l A B

/-- Existing recorded coefficient lookup for `32a1`. -/
def newform_32a1_ap (l : ℕ) : Option ℤ :=
  BealMatveevBeal.Level32Table.newform_32a1_ap l

/-- Missing complete `a₂₉ mod 13`/multi-prime Kraus elimination. -/
def explicit_a29_mod13_complete_Kraus_elimination : Prop :=
  level_32_no_newform_for_Frey_gap3

#check frey_ap
#check newform_32a1_ap
#check explicit_a29_mod13_complete_Kraus_elimination

end BealMatveevBeal.RibetCurve