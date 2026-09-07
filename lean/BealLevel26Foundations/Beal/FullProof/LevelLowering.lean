/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v8.3.0 — explicit Ribet lowering pack on a
`PositiveBealTriple`.

Mathlib 4.12 has no Ribet functor and no arrow
`Modular w → ExistsNewformLevel2`.  That label is
`s2_gamma0_2_dim ≠ 0` with `s2_gamma0_2_dim = 0`,
i.e. `0 ≠ 0`.  This file therefore does **not** prove
`¬ PositiveBealTriple` and does **not** make
`beal_forall_proof_positive` unconditional.

What it *does* prove:

* on a positive triple, Tate + Wiles-domain `Modular`
  + `ribet_level_quotient` give `N / ∏q = 2`;
* the Hecke-action / TW-tower pack from `HeckeAction`
  sits at that conductor;
* displayed `S₂(Γ₀(2))` dimension is 0, so
  `¬ ExistsNewformLevel2`;
* `beal_positive_bases` is Beal on positive bases
  *from* `ModularImpliesLevel2Newform` — same honesty
  as v8.1.0 / v8.2.0.

FullProof-only.  None chain does not import this file.
-/

import BealLevel26Foundations.Beal.FullProof.HeckeAction
import BealLevel26Foundations.Beal.FullProof.ModularImpliesNewform
import BealLevel26Foundations.Beal.FullProof.RibetFunctor
import BealLevel26Foundations.Beal.FullProof.ModularityRibet
import BealLevel26Foundations.Beal.FullProof.TrueConductor
import BealLevel26Foundations.Chain.Level2
import Mathlib.Tactic

namespace BealLevel26Foundations.Beal.FullProof.LevelLowering

open BealLevel26Foundations.Beal.FullProof.TrueConductor
open BealLevel26Foundations.Beal.FullProof.ModularityRibet
open BealLevel26Foundations.Beal.FullProof.ModularImpliesNewform
open BealLevel26Foundations.Beal.FullProof.HeckeAction
open BealLevel26Foundations.Beal.FullProof.RibetFunctor
open BealLevel26Foundations.Chain.Level2

/-- Packed conclusion of level lowering to 2 on a positive
triple: conductor `rad(ABC)`, quotient 2, TW patching at
`53`/`677`, and displayed `¬ ExistsNewformLevel2`.
Not a Mathlib newform. -/
structure LevelLoweringTo2 (t : PositiveBealTriple) : Prop where
  conductor_rad :
    globalConductorTate t.toPrimitive = radABC t.A t.B t.C
  pairwise :
    Nat.Coprime t.A t.B ∧ Nat.Coprime t.B t.C ∧ Nat.Coprime t.A t.C
  tate_odd :
    ∀ q ∈ (t.A * t.B * t.C).primeFactors,
      q ≠ 2 →
        conductorExponentTate
            (padicValInt q (freyCurveOf t.toPrimitive).c₄)
            (padicValInt q (freyCurveOf t.toPrimitive).Δ) =
          1
  modular : Modular t.toPrimitive
  quotient_two :
    globalConductorTate t.toPrimitive / oddConductorPart t.toPrimitive = 2
  det_chi : cyclotomicCharacter 13 = 13
  tw_53 : Q1 % 13 = 1
  tw_677 : Q2 % 169 = 1
  patched : Nonempty (R_infty patchedLevel1 ≃ T_infty patchedLevel1)
  no_newform : ¬ ExistsNewformLevel2
  s2_zero : s2_gamma0_2_dim = 0

theorem level_lowering_to_2 (t : PositiveBealTriple) :
    LevelLoweringTo2 t where
  conductor_rad := (frey_global_conductor t.toPrimitive).1
  pairwise := pairwise_coprime t.toPrimitive
  tate_odd := (frey_global_conductor t.toPrimitive).2.1
  modular := wiles_modularity_Frey t.toPrimitive
  quotient_two := ribet_level_quotient t.toPrimitive
  det_chi := det_eq_chi_13
  tw_53 := Q1_mod13
  tw_677 := Q2_mod169
  patched := ⟨R_T_scaffold patchedLevel1⟩
  no_newform := no_newform_level2
  s2_zero := S2_Gamma0_2_zero

/-- Functorial pack from `RibetFunctor` on the underlying
primitive triple. -/
theorem level_lowering_to_2_functor (t : PositiveBealTriple) :
    ∃ ρ' : GaloisRepModularLevel 2,
      ρ'.level = 2 ∧
        ρ'.residualPrime = 13 ∧
          globalConductorTate t.toPrimitive / oddConductorPart t.toPrimitive = 2 :=
  ribet_level_lowering_functor_of_frey t.toPrimitive

/-- Honesty: lowering plus `S2_Gamma0_2_zero` is *not*
`ExistsNewformLevel2`. -/
theorem level_lowering_does_not_inhabit_newform
    (t : PositiveBealTriple) :
    ¬ ExistsNewformLevel2 :=
  (level_lowering_to_2 t).no_newform

/-- Beal on positive bases, *from* the missing Mathlib
arrow.  Not unconditional.  Equal to
`beal_forall_proof_positive`. -/
theorem beal_positive_bases
    (hModNew : ModularImpliesLevel2Newform) :
    ∀ A B C m n p : Nat,
      0 < A → 0 < B → 0 < C →
      2 < m → 2 < n → 2 < p →
      A ^ m + B ^ n = C ^ p →
      1 < Nat.gcd A (Nat.gcd B C) :=
  beal_forall_proof_positive hModNew

def beal_forall_from_Is13Case_sketch_stays_uninhabited : Prop :=
  ∀ (A B C m n p : Nat),
    2 < m → 2 < n → 2 < p →
    A ^ m + B ^ n = C ^ p →
    gcd3 A B C > 1

#check level_lowering_to_2
#check level_lowering_to_2_functor
#check beal_positive_bases
#print axioms level_lowering_to_2
#print axioms level_lowering_does_not_inhabit_newform
#print axioms beal_positive_bases

end BealLevel26Foundations.Beal.FullProof.LevelLowering
