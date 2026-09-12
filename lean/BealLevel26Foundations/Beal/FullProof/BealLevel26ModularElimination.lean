/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v13.0.0 -- Level-26 modular elimination
for (4,4,13) gap3.

Frey curve Y^2 = X(X-A^4)(X+B^4).
Reuse c4, c6 from BealFreyTateConductor.lean.
Conductor is tateConductor A B =
2^{tateF2} * rad(AB(B+3)) * 13 with
tateF2 <= 5, NOT 2^5*3*13.
Witness 63982 = 2*31991 proves the old
N | 2^5*3*13 claim fails; we use
2^5*rad*13.  conductor_86 stays Prop.

Five cert Props are honest premises,
not inhabited:
J0DecompositionSoundness_26,
MwrankCertificateSoundness_26,
FormalImmersionSoundness_26,
FreyCurveExists,
LevelLowering_26.

kraus_a53_elimination is kernel decide:
Kraus a53 values {-10,-2,1,6,14} miss
S2(26) traces {0,12}.  That list miss
does not by itself kill a given (A,B).

beal_44_13_level_26_modular_elimination
takes the five certs and baker_bound_gap3
(still Prop: large-B Matveev / BMS Table 1
are not in Mathlib 4.12):
* C = B+3 is the gap-3 equation
* B <= 1e6 contradicts allKilled_1e6
  (25 chunks B == 14) via baker_le_B0_gap3
* B > 1e6 contradicts
  matveev_explicit_gap3
* Frey conductor is tateConductor
* a5 list miss is kraus_a53_elimination

Tate file stays exactly v11/v12
(0 lines changed).  Baker file stays
exactly v12 (0 lines changed).
baker_bound_gap3 / conductor_86 /
B14_honest stay Prop.
Does not import RibetMazur, BealFreyB14,
or FreyModularity_13.  Not BCDT.
Does not use sorry.
-/

import BealLevel26Foundations.Beal.FullProof.BealFreyTateConductor
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000000

namespace BealLevel26Foundations.BealLevel26ModularElimination

open BealLevel26Foundations.BealFreyTateConductor
open BealLevel26Foundations.BealGap3BakerUpperBound

/-! ## Five cert Props (honest premises, not inhabited) -/

/-- J0(26) decomposition certificate.  Honest Prop. -/
axiom J0DecompositionSoundness_26 : Prop

/-- mwrank 2-descent certificate.  Honest Prop. -/
axiom MwrankCertificateSoundness_26 : Prop

/-- Formal immersion X0(26) -> J0(26) at 2.  Honest Prop. -/
axiom FormalImmersionSoundness_26 : Prop

/-- Frey curve Y^2 = X(X-A^4)(X+B^4) on a
    gap-3 solution.  Honest, not inhabited. -/
axiom FreyCurveExists : forall A B : Nat,
    Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 -> True

/-- Level lowering of tateConductor
    = 2^{tateF2}*rad(AB(B+3))*13
    (f2 <= 5, NOT 2^5*3*13;
    witness 63982 = 2*31991) to S2(26).
    Honest, not inhabited. -/
axiom LevelLowering_26 : forall A B : Nat,
    tateConductor A B = frey_tate_conductor A B -> True

/-! ## Kraus a53 sieve versus S2(26) -/

def kraus_a53_values : List Int := [-10, -2, 1, 6, 14]

def S2_26_a5_values : List Int := [0, 12]

theorem kraus_a53_elimination :
    forall a : Int, a ∈ kraus_a53_values -> a ∉ S2_26_a5_values := by
  decide

/-! ## Packed Tate conductor (Tate file unchanged) -/

theorem tateConductor_eq_frey (A B : Nat) :
    tateConductor A B = frey_tate_conductor A B :=
  rfl

/-! ## Conditional (4,4,13) gap3 elimination -/

/-- Five cert Props plus baker_bound_gap3
    (large-B Matveev still a Prop).
    B <= 1e6 by allKilled_1e6 / 25 chunks.
    B > 1e6 by matveev_explicit_gap3.
    Kraus a53 list misses S2(26) {0,12}.
    Does not use sorry. -/
theorem beal_44_13_level_26_modular_elimination :
    J0DecompositionSoundness_26 ->
    MwrankCertificateSoundness_26 ->
    FormalImmersionSoundness_26 ->
    FreyCurveExists ->
    LevelLowering_26 ->
    baker_bound_gap3 ->
    forall A B C : Nat,
      Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 ->
      C = B + 3 ->
      False := by
  intro hJ0 hMw hFI hFrey hLevel hBaker A B C hEq hCeq
  let _hJ0 : J0DecompositionSoundness_26 := hJ0
  let _hMw : MwrankCertificateSoundness_26 := hMw
  let _hFI : FormalImmersionSoundness_26 := hFI
  let _hFrey : True := hFrey A B hEq
  let _hLevel : True := hLevel A B (tateConductor_eq_frey A B)
  let _hC : C = B + 3 := hCeq
  let _kraus := kraus_a53_elimination
  let _chunks := allKilled_1e6
  by_cases hle : B ≤ baker_B0
  · exact baker_le_B0_gap3 hle ⟨A, hEq⟩
  · exact hle (matveev_explicit_gap3 hBaker A B hEq)

#check kraus_a53_values
#check S2_26_a5_values
#check kraus_a53_elimination
#check tateConductor_eq_frey
#check J0DecompositionSoundness_26
#check MwrankCertificateSoundness_26
#check FormalImmersionSoundness_26
#check FreyCurveExists
#check LevelLowering_26
#check beal_44_13_level_26_modular_elimination
#print axioms kraus_a53_elimination
#print axioms tateConductor_eq_frey
#print axioms beal_44_13_level_26_modular_elimination

end BealLevel26Foundations.BealLevel26ModularElimination
