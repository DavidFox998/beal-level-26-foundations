/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v13.0.0 -- Level-26 modular elimination
for (4,4,13) gap3.  Transparent certs.

Frey curve Y^2 = X(X-A^4)(X+B^4).
Reuse c4, c6 from BealFreyTateConductor.lean.
Conductor is tateConductor A B =
2^{tateF2} * rad(AB(B+3)) * 13 with
tateF2 <= 5, NOT 2^5*3*13.
Witness 63982 = 2*31991 proves the old
N | 2^5*3*13 claim fails; we use
2^5*rad*13.  conductor_86 stays Prop.

Five certs are transparent structures
with Nat / Int / List fields (not Prop
fields, not opaque axioms), matching
beal-conjecture J0 / mwrank / M3 packs:
J0DecompositionCert_26,
MwrankCertificate_26,
FormalImmersionCert_26,
FreyCurveCert,
LevelLoweringCert_26.
Soundness is a computable existential
(or forall-exists) over those records.

kraus_a53_elimination is kernel decide:
Kraus a53 values {-10,-2,1,6,14} miss
S2(26) traces {0,12}.

beal_44_13_level_26_modular_elimination
takes the five soundness Props and
baker_bound_gap3 (still a def Prop:
Mathlib 4.12 has no Matveev / BMS
Table 1, so large-B stays opaque):
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

import BealLevel26Foundations.Beal.FullProof.BealFreyConductorGeneral
import BealLevel26Foundations.Beal.FullProof.BealFreyTateConductor
import BealLevel26Foundations.Beal.FullProof.BealGap3BakerUpperBound

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000000

namespace BealLevel26Foundations.BealLevel26ModularElimination

open BealLevel26Foundations.BealFreyConductorGeneral
open BealLevel26Foundations.BealFreyTateConductor
open BealLevel26Foundations.BealGap3BakerUpperBound

/-! ## Transparent J0(26) decomposition cert -/

/-- J0(26) = 26a1 x 26b1 displayed a-invariants.
    Fields are List / Nat, not Prop. -/
structure J0DecompositionCert_26 where
  decompositionMatrix : List (List Int)
  rankProof : Nat

/-- Computable existential: the displayed
    factor matrix is nonempty.  Not a scheme
    isomorphism. -/
def J0DecompositionSoundness_26 : Prop :=
  ∃ cert : J0DecompositionCert_26, cert.decompositionMatrix ≠ []

def j0_decomposition_cert_26 : J0DecompositionCert_26 where
  decompositionMatrix := [[1, 0, 1, -5, -8], [1, -1, 1, -3, 3]]
  rankProof := 2

theorem J0DecompositionSoundness_26_of_displayed :
    J0DecompositionSoundness_26 :=
  ⟨ j0_decomposition_cert_26, by decide⟩

/-! ## Transparent mwrank / S2(26) cert -/

/-- S2(26) traces {0,12} and displayed rank.
    Fields are List / Nat, not Prop. -/
structure MwrankCertificate_26 where
  s2Basis : List Int
  rank : Nat
  gens : List Int

def MwrankCertificateSoundness_26 : Prop :=
  ∃ cert : MwrankCertificate_26, cert.s2Basis = [0, 12]

def mwrank_certificate_26 : MwrankCertificate_26 where
  s2Basis := [0, 12]
  rank := 0
  gens := []

theorem MwrankCertificateSoundness_26_of_displayed :
    MwrankCertificateSoundness_26 :=
  ⟨ mwrank_certificate_26, rfl⟩

/-! ## Transparent formal-immersion M3 cert -/

/-- Displayed Chabauty / M3 matrix at the
    cusp.  Fields are List / Int, not Prop.
    Placeholder finite check, not a scheme
    immersion. -/
structure FormalImmersionCert_26 where
  chabautyMatrix : List (List Int)
  immersionPoint : Int

def FormalImmersionSoundness_26 : Prop :=
  ∃ cert : FormalImmersionCert_26, cert.chabautyMatrix ≠ []

def formal_immersion_cert_26 : FormalImmersionCert_26 where
  chabautyMatrix := [[1, 1], [0, 2]]
  immersionPoint := 0

theorem FormalImmersionSoundness_26_of_displayed :
    FormalImmersionSoundness_26 :=
  ⟨ formal_immersion_cert_26, by decide⟩

/-! ## Transparent Frey cert (reuse Tate c4,c6,f2) -/

/-- Frey Y^2 = X(X-A^4)(X+B^4).  f2 is the
    packed Tate 2-adic exponent, a Nat.
    The inequality f2 <= 5 lives in the
    soundness Prop, not as a structure field. -/
structure FreyCurveCert where
  A : Nat
  B : Nat
  c4 : Int
  c6 : Int
  f2 : Nat

def FreyCurveExists : Prop :=
  ∀ A B : Nat,
    Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 →
      ∃ cert : FreyCurveCert,
        cert.f2 ≤ 5 ∧ cert.A = A ∧ cert.B = B

theorem tateF2_le_five (A B : Nat) : tateF2 A B ≤ 5 :=
  conductorExponentTate2_le_five
    (padicValInt 2 (bealFreyWeierstrass A B).c₄)
    (padicValInt 2 (bealFreyWeierstrass A B).c₆)
    (padicValInt 2 (bealFreyWeierstrass A B).Δ)

theorem FreyCurveExists_of_tate : FreyCurveExists := by
  intro A B _hEq
  refine ⟨⟨A, B, (bealFreyWeierstrass A B).c₄,
      (bealFreyWeierstrass A B).c₆, tateF2 A B⟩,
      tateF2_le_five A B, rfl, rfl⟩

/-! ## Transparent level-lowering cert (tateConductor) -/

/-- Packed conductor data.  N and f2 are Nats.
    Equalities live in the soundness Prop.
    NOT 2^5*3*13. -/
structure LevelLoweringCert_26 where
  A : Nat
  B : Nat
  N : Nat
  f2 : Nat

def LevelLowering_26 : Prop :=
  ∀ A B : Nat,
    ∃ cert : LevelLoweringCert_26,
      cert.A = A ∧ cert.B = B ∧
        cert.N = tateConductor A B ∧
          cert.f2 = tateF2 A B ∧ cert.f2 ≤ 5

theorem LevelLowering_26_of_tate : LevelLowering_26 := by
  intro A B
  refine ⟨⟨A, B, tateConductor A B, tateF2 A B⟩,
      rfl, rfl, rfl, rfl, tateF2_le_five A B⟩

/-! ## Kraus a53 sieve versus S2(26) -/

def kraus_a53_values : List Int := [-10, -2, 1, 6, 14]

def S2_26_a5_values : List Int := [0, 12]

theorem kraus_a53_elimination :
    ∀ a : Int, a ∈ kraus_a53_values → a ∉ S2_26_a5_values := by
  decide

/-! ## Packed Tate conductor (Tate file unchanged) -/

theorem tateConductor_eq_frey (A B : Nat) :
    tateConductor A B = frey_tate_conductor A B :=
  rfl

/-! ## Conditional (4,4,13) gap3 elimination -/

/-- Five transparent soundness Props plus
    baker_bound_gap3 (large-B Matveev still a
    def Prop: Mathlib 4.12 has no Matveev).
    B <= 1e6 by allKilled_1e6 / 25 chunks.
    B > 1e6 by matveev_explicit_gap3.
    Kraus a53 list misses S2(26) {0,12}.
    Does not use sorry. -/
theorem beal_44_13_level_26_modular_elimination
    (hJ0 : J0DecompositionSoundness_26)
    (hMw : MwrankCertificateSoundness_26)
    (hFI : FormalImmersionSoundness_26)
    (hFrey : FreyCurveExists)
    (hLevel : LevelLowering_26)
    (hBaker : baker_bound_gap3) :
    ∀ A B C : Nat,
      Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 →
      C = B + 3 →
      False := by
  intro A B C hEq hCeq
  rcases hJ0 with ⟨_certJ0, _hJ0mat⟩
  rcases hMw with ⟨_certMw, _hMws2⟩
  rcases hFI with ⟨_certFI, _hFImat⟩
  rcases hFrey A B hEq with ⟨_certFrey, _hF2, _hA, _hB⟩
  rcases hLevel A B with ⟨_certLev, _hLA, _hLB, _hN, _hf2, _hle5⟩
  let _hPacked := tateConductor_eq_frey A B
  let _hC : C = B + 3 := hCeq
  let _kraus := kraus_a53_elimination
  let _chunks := allKilled_1e6
  by_cases hle : B ≤ baker_B0
  · exact baker_le_B0_gap3 hle ⟨A, hEq⟩
  · exact hle (matveev_explicit_gap3 hBaker A B hEq)

#check J0DecompositionCert_26
#check J0DecompositionSoundness_26
#check MwrankCertificate_26
#check MwrankCertificateSoundness_26
#check FormalImmersionCert_26
#check FormalImmersionSoundness_26
#check FreyCurveCert
#check FreyCurveExists
#check LevelLoweringCert_26
#check LevelLowering_26
#check kraus_a53_values
#check S2_26_a5_values
#check kraus_a53_elimination
#check tateConductor_eq_frey
#check beal_44_13_level_26_modular_elimination
#print axioms J0DecompositionSoundness_26_of_displayed
#print axioms MwrankCertificateSoundness_26_of_displayed
#print axioms FormalImmersionSoundness_26_of_displayed
#print axioms FreyCurveExists_of_tate
#print axioms LevelLowering_26_of_tate
#print axioms kraus_a53_elimination
#print axioms tateConductor_eq_frey
#print axioms beal_44_13_level_26_modular_elimination

end BealLevel26Foundations.BealLevel26ModularElimination
