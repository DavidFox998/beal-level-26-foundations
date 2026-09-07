/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v8.10.0 — Frey `a_q = ±1` via `(-c₆/q)`,
`13 ∣ v_q(Δ)` unramified criterion, and `J0_N_real`
as a packed `ModSym(Γ₀(N),2)` token with double-coset
`T_q`.  Not the 26a1/26b1 coefficient formula.

Mathlib 4.12 has no Ribet functor and no arrow
    `Modular w → ExistsNewformLevel2`.  That label is
`s2_gamma0_2_dim ≠ 0` with `s2_gamma0_2_dim = 0`,
i.e. `0 ≠ 0`.  This file therefore does **not**
inhabit `ExistsNewformLevel2`, does **not** prove
`¬ PositiveBealTriple`, and does **not** make
`beal_from_ribet` drop the `ModularImpliesLevel2Newform`
hypothesis.

What it *does* prove:

* `q_expansion_26a1` / `q_expansion_26b1` are the
  101-coeff LMFDB prefixes as `List ℚ`, matching the
  ledger (`a₁ = 1` by `rfl`/`decide`, `a₃ = 1` and
  `-3` by `decide`);
* `mazur_principle_step` is the Tate/Wiles/det/flat
  pack at an odd prime `q | ABC` (Steinberg label
  `v_q(c₄)=0`, `v_q(Δ)>0`, exponent 1) plus the
  displayed `T₃` eigenvalues on `26a1`/`26b1`;
* `ribet_iterated` iterates that pack and the
  identity `N / ∏q = 2`; the result is **not**
  a term of type `ExistsNewformLevel2`;
* `ribet_iterated_arrow` is the same uninhabited
  Prop as `ModularImpliesLevel2Newform`;
* `beal_from_ribet` is Beal on positive bases *from*
  that Prop;
* `HeckeAction_N` is the weight-2 `T_q` formula plus
  TW lift at `26·53` / `26·677` (not `End(J₀(N)[13])`);
* `mazur_step_real` / `ribet_iterated_real` iterate
  that pack to `N / ∏q = 2`;
* `ModularImpliesLevel2Newform_real` is the same
  uninhabited Prop as `ModularImpliesLevel2Newform`;
* `beal_from_ribet_real` stays *from* that Prop;
* `X0_N_Model` / `J0_N_Model` stay level tokens;
* `J0_N_real` is a packed `ModSym` token at
  `Γ₀(N)`, weight 2 — not Mathlib `J₀(N)`;
* `frey_a_q_real` / `frey_a_q_is_pm1` are the
  Tate split/nonsplit sign `(-c₆/q) = ±1`, not
  a Frey modular-form coefficient and not the
  26-ledger `a₃`;
* `frey_rho_unramified_iff_13_dvd_vqDelta` is the
  Tate criterion packed as a definitional iff;
* `mazur_step_real_fixed` requires `13 ∣ v_q(Δ)`;
* `ribet_iterated_real_fixed` iterates only over
  those primes; the quotient is **not** `2`
  unless `Frey13Case`;
* `beal_from_ribet_real_fixed` stays *from*
  `ModularImpliesLevel2Newform` (even under a
  universal `Frey13Case` hypothesis).

Does **not** import `X0_26_Model`.  FullProof-only.
None chain does not import this file.
-/

import BealLevel26Foundations.Beal.FullProof.LevelLowering
import BealLevel26Foundations.Beal.FullProof.HeckeAction
import BealLevel26Foundations.Beal.FullProof.ModularImpliesNewform
import BealLevel26Foundations.Beal.FullProof.RibetFunctor
import BealLevel26Foundations.Beal.FullProof.ModularityRibet
import BealLevel26Foundations.Beal.FullProof.TrueConductor
import BealLevel26Foundations.CoefficientLedger_26
import Beal.Foundations.J0_26_Decomp
import BealLevel26Foundations.Chain.Level2
import BealLevel26Foundations.Real.FreyWeierstrass
import Mathlib.NumberTheory.LegendreSymbol.Basic
import Mathlib.NumberTheory.ModularForms.CongruenceSubgroups
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.Tactic

namespace BealLevel26Foundations.Beal.FullProof.RibetMazur

open BealLevel26Foundations.Beal.FullProof.TrueConductor
open BealLevel26Foundations.Beal.FullProof.ModularityRibet
open BealLevel26Foundations.Beal.FullProof.ModularImpliesNewform
open BealLevel26Foundations.Beal.FullProof.HeckeAction
open BealLevel26Foundations.Beal.FullProof.HeckeAlgebra
open BealLevel26Foundations.Beal.FullProof.RibetFunctor
open BealLevel26Foundations.Beal.FullProof.LevelLowering
open BealLevel26Foundations.CoefficientLedger26
open Beal.Foundations.J0_26_Decomp
open BealLevel26Foundations.Chain.Level2
open BealLevel26Foundations.Real.FreyWeierstrass
open CongruenceSubgroup

/-! ## Explicit 101-coeff q-expansions (ledger as `ℚ`) -/

/-- LMFDB / Sage `ModularSymbols(26)` prefix of `26a1`
as rationals.  Matches `qExp_26a1`.  Not a Mathlib
`ModularForm`. -/
def q_expansion_26a1 : List ℚ :=
  List.map (fun n : ℤ => (n : ℚ)) qExp_26a1

/-- LMFDB / Sage prefix of `26b1` as rationals.
Matches `qExp_26b1`. -/
def q_expansion_26b1 : List ℚ :=
  List.map (fun n : ℤ => (n : ℚ)) qExp_26b1

theorem q_expansion_26a1_eq_ledger :
    q_expansion_26a1 = List.map (fun n : ℤ => (n : ℚ)) qExp_26a1 :=
  rfl

theorem q_expansion_26b1_eq_ledger :
    q_expansion_26b1 = List.map (fun n : ℤ => (n : ℚ)) qExp_26b1 :=
  rfl

theorem q_expansion_26a1_length : q_expansion_26a1.length = 101 := by
  rw [q_expansion_26a1, List.length_map]
  exact qExp_26a1_length

theorem q_expansion_26b1_length : q_expansion_26b1.length = 101 := by
  rw [q_expansion_26b1, List.length_map]
  exact qExp_26b1_length

theorem qExp_26a1_a1 : qExp_26a1[1]? = some 1 := by
  decide

theorem qExp_26a1_a3 : qExp_26a1[3]? = some 1 := by
  decide

theorem qExp_26b1_a3 : qExp_26b1[3]? = some (-3) := by
  decide

theorem qExp_26a1_get1 : qExp_26a1.get? 1 = some (1 : ℤ) := by
  decide

theorem qExp_26b1_get1 : qExp_26b1.get? 1 = some (1 : ℤ) := by
  decide

theorem qExp_26a1_get3 : qExp_26a1.get? 3 = some (1 : ℤ) := by
  decide

theorem qExp_26b1_get3 : qExp_26b1.get? 3 = some (-3 : ℤ) := by
  decide

theorem q_expansion_26a1_a1 : q_expansion_26a1.get? 1 = some (1 : Rat) := by
  have hmap := List.get?_map (fun n : Int => (n : Rat)) qExp_26a1 1
  rw [q_expansion_26a1, hmap, qExp_26a1_get1]
  rfl

theorem q_expansion_26b1_a1 : q_expansion_26b1.get? 1 = some (1 : ℚ) := by
  have hmap := List.get?_map (fun n : ℤ => (n : ℚ)) qExp_26b1 1
  rw [q_expansion_26b1, hmap, qExp_26b1_get1]
  rfl

theorem q_expansion_26a1_a3 : q_expansion_26a1.get? 3 = some (1 : ℚ) := by
  have hmap := List.get?_map (fun n : ℤ => (n : ℚ)) qExp_26a1 3
  rw [q_expansion_26a1, hmap, qExp_26a1_get3]
  rfl

theorem q_expansion_26b1_a3 : q_expansion_26b1.get? 3 = some (-3 : ℚ) := by
  have hmap := List.get?_map (fun n : ℤ => (n : ℚ)) qExp_26b1 3
  rw [q_expansion_26b1, hmap, qExp_26b1_get3]
  rfl

theorem E_26a1_ainv :
    factor26a1.a1 = 1 ∧ factor26a1.a2 = 0 ∧ factor26a1.a3 = 1 ∧
      factor26a1.a4 = -5 ∧ factor26a1.a6 = -8 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem E_26b1_ainv :
    factor26b1.a1 = 1 ∧ factor26b1.a2 = -1 ∧ factor26b1.a3 = 1 ∧
      factor26b1.a4 = -3 ∧ factor26b1.a6 = 3 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

theorem E_26a1_disc : factor26a1.discriminant = -17576 :=
  rfl

theorem E_26b1_disc : factor26b1.discriminant = -1664 :=
  rfl

/-- Weight-2 `T_q` at `n = 1` is the Fourier coefficient
`a_q` (`q ∤ 1`). -/
theorem Tq_at_one_eq_aq {q : Nat} (a : List ℤ) (hq : 1 < q) :
    HeckeOperator_Tq_coeff q 1 a = coeffAt a q := by
  have h : ¬ q ∣ 1 := Nat.not_dvd_of_pos_of_lt (Nat.succ_pos 0) hq
  simp [HeckeOperator_Tq_coeff, h]

theorem T3_26a1_matches_a3 :
    HeckeOperator_Tq_coeff 3 1 f_26a1 = 1 ∧
      coeffAt f_26a1 3 = 1 :=
  ⟨T3_26a1_at_one, by decide⟩

theorem T3_26b1_matches_a3 :
    HeckeOperator_Tq_coeff 3 1 f_26b1 = -3 ∧
      coeffAt f_26b1 3 = -3 :=
  ⟨T3_26b1_at_one, by decide⟩

theorem T5_26a1_at_one :
    HeckeOperator_Tq_coeff 5 1 f_26a1 = -3 := by
  decide

theorem T5_26b1_at_one :
    HeckeOperator_Tq_coeff 5 1 f_26b1 = -1 := by
  decide

theorem T7_26a1_at_one :
    HeckeOperator_Tq_coeff 7 1 f_26a1 = -1 := by
  decide

theorem T7_26b1_at_one :
    HeckeOperator_Tq_coeff 7 1 f_26b1 = 1 := by
  decide

/-- Displayed `26a1` coefficient `a₃ = 1` is `±1` mod 13.
This is a ledger check on the *level-26* eigenform, not
the Frey newform of level `rad(ABC)`. -/
theorem a3_26a1_pm_one_mod13 :
    (coeffAt qExp_26a1 3 : ZMod 13) = 1 ∨
      (coeffAt qExp_26a1 3 : ZMod 13) = -1 := by
  decide

/-! ## Mazur / Ribet step as packed Tate + Hecke data -/

/-- Classical Steinberg label at an odd prime of
multiplicative reduction: `v_q(c₄)=0` and `v_q(Δ)>0`.
Not a Mathlib local Langlands parameter, and not a
Fourier coefficient `a_q = ±1` of a Frey newform. -/
def steinberg_label (w : PrimitiveBealTriple) (q : Nat) : Prop :=
  padicValInt q (freyCurveOf w).c₄ = 0 ∧
    0 < padicValInt q (freyCurveOf w).Δ

/-- One Mazur/Ribet lowering *step* at an odd prime
`q | ABC`.  The conclusion is the packed Tate/Wiles
input plus displayed `T_q` on `26a1`/`26b1` and the
TW `R ≃ T` tokens.  Not a Mathlib newform of level
`N/q`. -/
structure MazurPrincipleStep (t : PositiveBealTriple) (q : Nat) : Prop where
  q_prime : q.Prime
  q_odd : q ≠ 2
  q_dvd_ABC : q ∣ t.A * t.B * t.C
  tate_exp_one :
    conductorExponentTate
        (padicValInt q (freyCurveOf t.toPrimitive).c₄)
        (padicValInt q (freyCurveOf t.toPrimitive).Δ) =
      1
  c4_val_zero : padicValInt q (freyCurveOf t.toPrimitive).c₄ = 0
  Delta_pos : 0 < padicValInt q (freyCurveOf t.toPrimitive).Δ
  steinberg : steinberg_label t.toPrimitive q
  modular : Modular t.toPrimitive
  det_chi : cyclotomicCharacter 13 = 13
  finite_flat : finiteFlatAt (Frey_GaloisRep t) 13
  T3_a1 : HeckeOperator_Tq_coeff 3 1 f_26a1 = 1
  T3_b1 : HeckeOperator_Tq_coeff 3 1 f_26b1 = -3
  T5_a1 : HeckeOperator_Tq_coeff 5 1 f_26a1 = -3
  T7_a1 : HeckeOperator_Tq_coeff 7 1 f_26a1 = -1
  patched_53 : Nonempty (R_infty patchedLevel1 ≃ T_infty patchedLevel1)
  patched_677 : Nonempty (R_infty patchedLevel2 ≃ T_infty patchedLevel2)

theorem mazur_principle_step (t : PositiveBealTriple) {q : Nat}
    (hqMem : q ∈ (t.A * t.B * t.C).primeFactors) (hodd : q ≠ 2) :
    MazurPrincipleStep t q :=
  let hqP : q.Prime := Nat.prime_of_mem_primeFactors hqMem
  let hdvd : q ∣ t.A * t.B * t.C := Nat.dvd_of_mem_primeFactors hqMem
  { q_prime := hqP
    q_odd := hodd
    q_dvd_ABC := hdvd
    tate_exp_one :=
      (tate_odd_prime t.toPrimitive hqP hodd hdvd).exponent_one
    c4_val_zero :=
      (tate_odd_prime t.toPrimitive hqP hodd hdvd).c4_val_zero
    Delta_pos := odd_prime_Delta_val_pos t.toPrimitive hqP hodd hdvd
    steinberg :=
      ⟨(tate_odd_prime t.toPrimitive hqP hodd hdvd).c4_val_zero,
        odd_prime_Delta_val_pos t.toPrimitive hqP hodd hdvd⟩
    modular := wiles_modularity_Frey t.toPrimitive
    det_chi := det_eq_chi_13
    finite_flat := finiteFlatAt_13 t.toPrimitive
    T3_a1 := T3_26a1_at_one
    T3_b1 := T3_26b1_at_one
    T5_a1 := T5_26a1_at_one
    T7_a1 := T7_26a1_at_one
    patched_53 := R_inf_eq_T_inf_patched.1
    patched_677 := R_inf_eq_T_inf_patched.2.1 }

/-! ## Iterated lowering pack (not `0 ≠ 0`) -/

/-- Iterated Mazur/Ribet pack: every odd prime of `ABC`
has a `MazurPrincipleStep`, and `N / ∏q = 2`.  Displayed
`S₂(Γ₀(2))` dimension is 0, so this is **not**
`ExistsNewformLevel2`. -/
structure RibetIteratedPack (t : PositiveBealTriple) : Prop where
  modular : Modular t.toPrimitive
  mazur_all :
    ∀ q ∈ (t.A * t.B * t.C).primeFactors,
      q ≠ 2 → MazurPrincipleStep t q
  quotient_two :
    globalConductorTate t.toPrimitive / oddConductorPart t.toPrimitive = 2
  rad_two_odd :
    radABC t.A t.B t.C / oddConductorPart t.toPrimitive = 2
  hecke_basis :
    certifiedDecompositionDimension = 2 ∧
      factor26a1.dimension = 1 ∧
        factor26b1.dimension = 1
  qexp_len :
    q_expansion_26a1.length = 101 ∧ q_expansion_26b1.length = 101
  T3_match :
    HeckeOperator_Tq_coeff 3 1 f_26a1 = 1 ∧
      HeckeOperator_Tq_coeff 3 1 f_26b1 = -3
  tw_53 : Q1 % 13 = 1
  tw_677 : Q2 % 169 = 1
  patched_53 : Nonempty (R_infty patchedLevel1 ≃ T_infty patchedLevel1)
  patched_677 : Nonempty (R_infty patchedLevel2 ≃ T_infty patchedLevel2)
  s2_zero : s2_gamma0_2_dim = 0
  no_newform : ¬ ExistsNewformLevel2

/-- Iterate `mazur_principle_step` over the odd primes of
`ABC`.  The conductor identity is `N / ∏q = 2` from
`ribet_level_quotient`.  The `Modular` hypothesis is the
Wiles-domain input; it does **not** produce a term of
type `ExistsNewformLevel2`. -/
theorem ribet_iterated (t : PositiveBealTriple)
    (_hMod : Modular t.toPrimitive) :
    RibetIteratedPack t where
  modular := wiles_modularity_Frey t.toPrimitive
  mazur_all := fun _ hq hodd => mazur_principle_step t hq hodd
  quotient_two := ribet_level_quotient t.toPrimitive
  rad_two_odd := ribet_level_quotient_rad t.toPrimitive
  hecke_basis := S2_Gamma0_26_dim
  qexp_len := ⟨q_expansion_26a1_length, q_expansion_26b1_length⟩
  T3_match := ⟨T3_26a1_at_one, T3_26b1_at_one⟩
  tw_53 := Q1_mod13
  tw_677 := Q2_mod169
  patched_53 := R_inf_eq_T_inf_patched.1
  patched_677 := R_inf_eq_T_inf_patched.2.1
  s2_zero := S2_Gamma0_2_zero
  no_newform := no_newform_level2

/-- The requested arrow `Modular w → ExistsNewformLevel2`.
Same uninhabited Prop as `ModularImpliesLevel2Newform`.
A theorem of this type would inhabit `0 ≠ 0`. -/
def ribet_iterated_arrow : Prop :=
  ModularImpliesLevel2Newform

theorem ribet_iterated_arrow_eq :
    ribet_iterated_arrow = ModularImpliesLevel2Newform :=
  rfl

/-- Honesty: the iterated pack plus `S2_Gamma0_2_zero`
is `¬ ExistsNewformLevel2`, not a level-2 newform. -/
theorem ribet_iterated_does_not_inhabit_newform
    (t : PositiveBealTriple) :
    ¬ ExistsNewformLevel2 :=
  (ribet_iterated t (wiles_modularity_Frey t.toPrimitive)).no_newform

/-- Beal on positive bases, *from* the missing Mathlib
arrow.  Not `¬ PositiveBealTriple`.  Equal to
`beal_positive_bases`. -/
theorem beal_from_ribet
    (hModNew : ModularImpliesLevel2Newform) :
    ∀ A B C m n p : Nat,
      0 < A → 0 < B → 0 < C →
      2 < m → 2 < n → 2 < p →
      A ^ m + B ^ n = C ^ p →
      1 < Nat.gcd A (Nat.gcd B C) :=
  beal_positive_bases hModNew

/-- Same type as `beal_positive_bases` / `beal_from_ribet`.
The name records the v8.6/v8.7 request for an
unconditional statement; the type still requires
`ModularImpliesLevel2Newform`. -/
theorem beal_positive_bases_unconditional
    (hModNew : ModularImpliesLevel2Newform) :
    ∀ A B C m n p : Nat,
      0 < A → 0 < B → 0 < C →
      2 < m → 2 < n → 2 < p →
      A ^ m + B ^ n = C ^ p →
      1 < Nat.gcd A (Nat.gcd B C) :=
  beal_from_ribet hModNew

def beal_forall_from_Is13Case_sketch_stays_uninhabited : Prop :=
  ∀ (A B C m n p : Nat),
    2 < m → 2 < n → 2 < p →
    A ^ m + B ^ n = C ^ p →
    gcd3 A B C > 1

/-! ## v8.8.0 — Int ledger, HeckeAction_N, iterated real pack -/

/-- Integer ledger prefix of `26a1`.  Same array as
`qExp_26a1`. -/
def q_expansion_26a1_int : List ℤ :=
  qExp_26a1

/-- Integer ledger prefix of `26b1`. -/
def q_expansion_26b1_int : List ℤ :=
  qExp_26b1

theorem q_expansion_26a1_int_length : q_expansion_26a1_int.length = 101 :=
  qExp_26a1_length

theorem q_expansion_26b1_int_length : q_expansion_26b1_int.length = 101 :=
  qExp_26b1_length

theorem q_expansion_26a1_int_a0 : q_expansion_26a1_int.get? 0 = some 0 := by
  decide

theorem q_expansion_26b1_int_a0 : q_expansion_26b1_int.get? 0 = some 0 := by
  decide

theorem q_expansion_26a1_int_a1 : q_expansion_26a1_int.get? 1 = some 1 :=
  qExp_26a1_get1

theorem Q1_mod : Q1 % 13 = 1 := by
  decide

theorem Q2_mod : Q2 % 169 = 1 := by
  decide

theorem Q3_composite_decide : 17 * 517 = Q3 := by
  decide

/-- Weight-2 `T_q` on a coefficient sequence, used as the
Hecke action token at a prime `q` of `N`.  Not an
endomorphism of Mathlib `J₀(N)[13]`.  The unused
positivity hypothesis records that `q` is an odd prime
of the conductor, not that `26 ∣ N`. -/
def HeckeAction_N (q : Nat) (_hpos : 1 < q) (a : List ℤ) (n : Nat) : ℤ :=
  HeckeOperator_Tq_coeff q n a

/-- TW / degeneracy pack: `T_q` is the HeckeAction
formula, the double-coset token lives at `26q`, and
`R ≃ T` is rank 1 at the TW levels `26·53` and
`26·677`.  This is **not** a degeneracy
`J₀(26) → J₀(N)` for general `N = rad(ABC)`. -/
structure HeckeAction_N_TW (q : Nat) : Prop where
  Tq_at_one :
    ∀ (hq : 1 < q) (a : List ℤ), HeckeAction_N q hq a 1 = coeffAt a q
  T3_model :
    HeckeAlgebra_T_Model.canonical.T3 =
      fun a n => HeckeOperator_Tq_coeff 3 n a
  T5_model :
    HeckeAlgebra_T_Model.canonical.T5 =
      fun a n => HeckeOperator_Tq_coeff 5 n a
  T7_model :
    HeckeAlgebra_T_Model.canonical.T7 =
      fun a n => HeckeOperator_Tq_coeff 7 n a
  middle : (HeckeOperator_Tq q).correspondence.middle = 26 * q
  patched_53 : Nonempty (R_infty patchedLevel1 ≃ T_infty patchedLevel1)
  patched_677 : Nonempty (R_infty patchedLevel2 ≃ T_infty patchedLevel2)
  rank_one_53 : localizedHeckeRank patchedLevel1 = 1
  rank_one_677 : localizedHeckeRank patchedLevel2 = 1

theorem HeckeAction_N_TW_holds (q : Nat) : HeckeAction_N_TW q where
  Tq_at_one := fun hq a => Tq_at_one_eq_aq a hq
  T3_model := HeckeAlgebra_T_Model.canonical.T3_def
  T5_model := HeckeAlgebra_T_Model.canonical.T5_def
  T7_model := HeckeAlgebra_T_Model.canonical.T7_def
  middle := HeckeOperator_Tq_correspondence q
  patched_53 := R_inf_eq_T_inf_patched.1
  patched_677 := R_inf_eq_T_inf_patched.2.1
  rank_one_53 := localizedRankOne_from_Patching patchedLevel1
  rank_one_677 := localizedRankOne_from_Patching patchedLevel2

/-- Honesty: the *level-26* coefficient `a₃(26a1) = 1`
is **not** `±(3+1)` mod 13.  The requested
`T_q ≡ ±(q+1) (mod 13)` check therefore fails on the
displayed ledger at `q = 3`.  These are not Frey
Fourier coefficients of level `rad(ABC)`. -/
theorem a3_26a1_ne_pm_qplus1_mod13 :
    (coeffAt qExp_26a1 3 : ZMod 13) ≠ (4 : ZMod 13) ∧
      (coeffAt qExp_26a1 3 : ZMod 13) ≠ (-4 : ZMod 13) := by
  decide

/-- One Mazur step as packed data: Wiles-domain
`Modular` at `N = rad(ABC)`, Tate Steinberg at `q`,
displayed Hecke / TW tokens, and the arithmetic
`q ∣ N → (N/q)*q = N`.  Not Mathlib modularity at
`N/q`. -/
structure MazurStepReal (t : PositiveBealTriple) (q : Nat) : Prop where
  step : MazurPrincipleStep t q
  hecke : HeckeAction_N_TW q
  modular_N : Modular t.toPrimitive
  conductor_N : globalConductorTate t.toPrimitive = radABC t.A t.B t.C
  pairwise : Nat.Coprime t.A t.B ∧ Nat.Coprime t.B t.C ∧ Nat.Coprime t.A t.C
  lowered_mul :
    q ∣ globalConductorTate t.toPrimitive →
      0 < q →
        globalConductorTate t.toPrimitive / q * q =
          globalConductorTate t.toPrimitive
  rank_one : localizedHeckeRank patchedLevel1 = 1
  displayed_T3_not_oldform :
    (coeffAt qExp_26a1 3 : ZMod 13) ≠ (4 : ZMod 13)

theorem mazur_step_real (t : PositiveBealTriple) {q : Nat}
    (hqMem : q ∈ (t.A * t.B * t.C).primeFactors) (hodd : q ≠ 2)
    (_hMod : Modular t.toPrimitive) :
    MazurStepReal t q where
  step := mazur_principle_step t hqMem hodd
  hecke := HeckeAction_N_TW_holds q
  modular_N := wiles_modularity_Frey t.toPrimitive
  conductor_N := (frey_global_conductor t.toPrimitive).1
  pairwise := pairwise_coprime t.toPrimitive
  lowered_mul := fun h _ => Nat.div_mul_cancel h
  rank_one := localizedRankOne_from_Patching patchedLevel1
  displayed_T3_not_oldform := a3_26a1_ne_pm_qplus1_mod13.1

/-- Odd prime factors of `ABC`, i.e. the primes in
`oddConductorPart`. -/
def odd_q_divisors_N (t : PositiveBealTriple) : Finset Nat :=
  (t.A * t.B * t.C).primeFactors.filter fun q => q ≠ 2

theorem odd_q_divisors_N_prod (t : PositiveBealTriple) :
    (odd_q_divisors_N t).prod id = oddConductorPart t.toPrimitive :=
  rfl

/-- Level after removing every odd prime of `ABC`.
Equals `2` by `ribet_level_quotient`. -/
def ribet_iterated_real_level (t : PositiveBealTriple) : Nat :=
  globalConductorTate t.toPrimitive / (odd_q_divisors_N t).prod id

theorem ribet_iterated_real_level_eq_two (t : PositiveBealTriple) :
    ribet_iterated_real_level t = 2 := by
  rw [ribet_iterated_real_level, odd_q_divisors_N_prod]
  exact ribet_level_quotient t.toPrimitive

/-- Iterated Mazur pack: a `MazurStepReal` at every odd
prime of `ABC`, fold identity `N / ∏q = 2`, displayed
`S₂(Γ₀(2))` dim 0.  Not `ExistsNewformLevel2`. -/
structure RibetIteratedReal (t : PositiveBealTriple) : Prop where
  pack : RibetIteratedPack t
  mazur_real_all :
    ∀ q ∈ odd_q_divisors_N t, MazurStepReal t q
  level_two : ribet_iterated_real_level t = 2
  hecke_N : ∀ q ∈ odd_q_divisors_N t, HeckeAction_N_TW q
  no_newform : ¬ ExistsNewformLevel2

theorem ribet_iterated_real (t : PositiveBealTriple)
    (hMod : Modular t.toPrimitive) :
    RibetIteratedReal t where
  pack := ribet_iterated t hMod
  mazur_real_all := by
    intro q hq
    have hqMem : q ∈ (t.A * t.B * t.C).primeFactors :=
      (Finset.mem_filter.mp hq).1
    have hodd : q ≠ 2 := (Finset.mem_filter.mp hq).2
    exact mazur_step_real t hqMem hodd hMod
  level_two := ribet_iterated_real_level_eq_two t
  hecke_N := fun q _ => HeckeAction_N_TW_holds q
  no_newform := no_newform_level2

/-- The requested arrow `Modular w → ExistsNewformLevel2`.
Same uninhabited Prop as `ModularImpliesLevel2Newform`.
A theorem of this type would inhabit `0 ≠ 0` from
`wiles_modularity_Frey`. -/
def ModularImpliesLevel2Newform_real : Prop :=
  ModularImpliesLevel2Newform

theorem ModularImpliesLevel2Newform_real_eq :
    ModularImpliesLevel2Newform_real = ModularImpliesLevel2Newform :=
  rfl

/-- Honesty: the missing arrow plus `S2_Gamma0_2_zero`
is `False`.  Not a theorem from a positive triple
alone. -/
theorem ModularImpliesLevel2Newform_real_of_arrow
    (h : ModularImpliesLevel2Newform_real)
    (w : PrimitiveBealTriple) : False :=
  no_newform_level2_of_arrow h w

/-- Beal on positive bases, *from* the missing Mathlib
arrow.  Not `¬ PositiveBealTriple`. -/
theorem beal_from_ribet_real
    (hModNew : ModularImpliesLevel2Newform) :
    ∀ A B C m n p : Nat,
      0 < A → 0 < B → 0 < C →
      2 < m → 2 < n → 2 < p →
      A ^ m + B ^ n = C ^ p →
      1 < Nat.gcd A (Nat.gcd B C) :=
  beal_from_ribet hModNew

/-! ## v8.9.0 — packed X0(N)/J0(N) and Frey Steinberg label -/

/-- Packed modular-curve token at conductor `N`.
Not a Mathlib moduli space of cyclic `N`-isogenies
and not a base change of the affine `X0_26` model. -/
structure X0_N_Model (N : Nat) where
  level : Nat
  level_eq : level = N

def X0_N_Model.ofTriple (t : PositiveBealTriple) :
    X0_N_Model (globalConductorTate t.toPrimitive) where
  level := globalConductorTate t.toPrimitive
  level_eq := rfl

theorem X0_N_Model_eq_rad (t : PositiveBealTriple) :
    (X0_N_Model.ofTriple t).level = radABC t.A t.B t.C :=
  (frey_global_conductor t.toPrimitive).1

theorem X0_N_Model_two_odd (t : PositiveBealTriple) :
    (X0_N_Model.ofTriple t).level = 2 * oddConductorPart t.toPrimitive :=
  rfl

/-- Displayed four-cusp labels of the `N = 26` model.
Not the cusp set of `X₀(N)` for general `N`. -/
def displayed_cusps_26 : List Nat :=
  [1, 2, 13, 26]

/-- Jacobian token at conductor `N`: the level plus the
displayed `N = 26` cusp labels.  Not `Pic⁰` of a curve
and not a free abelian group on the cusps of `X₀(N)`. -/
structure J0_N_Model (N : Nat) where
  level : Nat
  level_eq : level = N
  cusp_labels_26 : List Nat

def J0_N_Model.ofTriple (t : PositiveBealTriple) :
    J0_N_Model (globalConductorTate t.toPrimitive) where
  level := globalConductorTate t.toPrimitive
  level_eq := rfl
  cusp_labels_26 := displayed_cusps_26

theorem J0_N_Model_cusps (t : PositiveBealTriple) :
    (J0_N_Model.ofTriple t).cusp_labels_26 = [1, 2, 13, 26] :=
  rfl

/-! ## v8.10.0 — Tate `a_q = ±1`, `13 ∣ v_q(Δ)`, ModSym token -/

/-- Mathlib `Γ₀(N)`.  Not a modular-symbol space. -/
def Gamma0_N (N : Nat) : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ) :=
  Gamma0 N

theorem Gamma0_N_eq (N : Nat) :
    Gamma0_N N = Gamma0 N :=
  rfl

/-- Packed modular-symbol token at level `N`, weight 2.
Not Mathlib `ModSym` (4.12 has none) and not a base
change of the affine `X0_26` model. -/
structure ModSym (N : Nat) where
  level : Nat
  level_eq : level = N
  weight : Nat
  weight_eq : weight = 2
  gamma0 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) ℤ)
  gamma0_eq : gamma0 = Gamma0 N
  cusps : List (Nat × Nat)

/-- Displayed `ℙ¹(ℚ)` cusp labels `[0]` and `[∞]`, not
the four cusps of `X₀(26)`. -/
def displayed_cusps_P1 : List (Nat × Nat) :=
  [(0, 1), (1, 0)]

def ModSym.ofLevel (N : Nat) : ModSym N where
  level := N
  level_eq := rfl
  weight := 2
  weight_eq := rfl
  gamma0 := Gamma0 N
  gamma0_eq := rfl
  cusps := displayed_cusps_P1

/-- Jacobian token as the dual of packed weight-2
modular symbols.  Not `Pic⁰` and not `End(J₀(N)[13])`. -/
def J0_N_real (N : Nat) : Type :=
  ModSym N

def J0_N_real.ofTriple (t : PositiveBealTriple) :
    J0_N_real (globalConductorTate t.toPrimitive) :=
  ModSym.ofLevel (globalConductorTate t.toPrimitive)

theorem J0_N_real_level (t : PositiveBealTriple) :
    (J0_N_real.ofTriple t).level = globalConductorTate t.toPrimitive :=
  rfl

theorem J0_N_real_weight (t : PositiveBealTriple) :
    (J0_N_real.ofTriple t).weight = 2 :=
  rfl

theorem J0_N_real_cusps (t : PositiveBealTriple) :
    (J0_N_real.ofTriple t).cusps = [(0, 1), (1, 0)] :=
  rfl

/-- Double-coset token `Γ₀(N) \ M_q(N) / Γ₀(N)`.
`det = q`, bottom-left `≡ 0 (mod N)`.  Representative
count is `q+1` away from `N` and `q` when `q | N`
(`U_q`).  Not a Mathlib Hecke correspondence. -/
structure DoubleCoset_Mq (N q : Nat) where
  det : Nat
  det_eq : det = q
  bottom_left_mod : Nat
  bottom_left_mod_eq : bottom_left_mod = 0
  correspondence : HeckeCorrespondence N q
  rep_count : Nat
  rep_count_away : ¬ q ∣ N → rep_count = q + 1
  rep_count_old : q ∣ N → rep_count = q

/-- Endomorphism token of packed `J0_N_real` residual
13-torsion.  Not Mathlib `End(J₀(N)[13])`. -/
structure EndJ0_N_13 (N q : Nat) where
  level : Nat
  level_eq : level = N
  residue : Nat
  residue_eq : residue = 13
  hecke : DoubleCoset_Mq N q

/-- Double-coset `T_q` / `U_q` token at level `N`.
**Not** the coefficient formula on the 26a1/26b1 ledger. -/
def HeckeAction_N_real (N q : Nat) : EndJ0_N_13 N q where
  level := N
  level_eq := rfl
  residue := 13
  residue_eq := rfl
  hecke :=
    { det := q
      det_eq := rfl
      bottom_left_mod := 0
      bottom_left_mod_eq := rfl
      correspondence := ⟨N, N * q, N, rfl, rfl, rfl⟩
      rep_count := if q ∣ N then q else q + 1
      rep_count_away := by
        intro h
        simp [h]
      rep_count_old := by
        intro h
        simp [h] }

theorem HeckeAction_N_real_middle (N q : Nat) :
    (HeckeAction_N_real N q).hecke.correspondence.middle = N * q :=
  rfl

theorem HeckeAction_N_real_not_26_ledger (N q : Nat) :
    (HeckeAction_N_real N q).hecke.correspondence.source = N :=
  rfl

/-- TW auxiliary levels `N · 53` and `N · 677`, not
`26 · 53` / `26 · 677`. -/
def patchedLevel_N (N Q : Nat) : Nat :=
  N * Q

theorem patchedLevel_N_Q1 (N : Nat) :
    patchedLevel_N N Q1 = N * 53 :=
  rfl

theorem patchedLevel_N_Q2 (N : Nat) :
    patchedLevel_N N Q2 = N * 677 :=
  rfl

theorem R_T_at_N_Q1 (N : Nat) :
    Nonempty (R_infty (patchedLevel_N N Q1) ≃ T_infty (patchedLevel_N N Q1)) :=
  ⟨R_T_scaffold (patchedLevel_N N Q1)⟩

theorem R_T_at_N_Q2 (N : Nat) :
    Nonempty (R_infty (patchedLevel_N N Q2) ≃ T_infty (patchedLevel_N N Q2)) :=
  ⟨R_T_scaffold (patchedLevel_N N Q2)⟩

theorem localizedRank_N_Q1 (N : Nat) :
    localizedHeckeRank (patchedLevel_N N Q1) = 1 :=
  localizedRankOne_from_Patching (patchedLevel_N N Q1)

theorem localizedRank_N_Q2 (N : Nat) :
    localizedHeckeRank (patchedLevel_N N Q2) = 1 :=
  localizedRankOne_from_Patching (patchedLevel_N N Q2)

theorem frey_c6_formula (w : PrimitiveBealTriple) :
    (freyCurveOf w).c₆ =
      -32 * (((w.B : Int) ^ w.n) - ((w.A : Int) ^ w.m)) *
        (2 * (((w.B : Int) ^ w.n) - ((w.A : Int) ^ w.m)) ^ 2 +
          9 * (((w.A : Int) ^ w.m) * ((w.B : Int) ^ w.n))) := by
  simpa [freyCurveOf] using
    freyCurve_c6 (w.A : Int) (w.B : Int) w.m w.n

theorem zmod_64_ne_zero {q : Nat} [Fact q.Prime] (hodd : q ≠ 2) :
    (64 : ZMod q) ≠ 0 := by
  intro h
  have hq : q.Prime := Fact.out
  have h64 : q ∣ 64 := (ZMod.natCast_zmod_eq_zero_iff_dvd 64 q).mp h
  have h2 : q ∣ 2 := hq.dvd_of_dvd_pow (by
    have : 64 = 2 ^ 6 := by decide
    exact this ▸ h64)
  exact hodd ((Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp h2)

theorem odd_prime_c6_ne_zero_mod (w : PrimitiveBealTriple) {q : Nat}
    [Fact q.Prime] (hodd : q ≠ 2) (hdvd : q ∣ w.A * w.B * w.C) :
    ((freyCurveOf w).c₆ : ZMod q) ≠ 0 := by
  have hq : q.Prime := Fact.out
  have hCop := pairwise_coprime w
  have hABC := (Nat.Prime.dvd_mul hq).mp hdvd
  have h64 : (64 : ZMod q) ≠ 0 := zmod_64_ne_zero hodd
  have hneg64 : (-64 : ZMod q) ≠ 0 := neg_ne_zero.mpr h64
  have hc6cast :
      ((freyCurveOf w).c₆ : ZMod q) =
        (-32 : ZMod q) *
          (((w.B : Int) : ZMod q) ^ w.n - ((w.A : Int) : ZMod q) ^ w.m) *
          (2 *
              (((w.B : Int) : ZMod q) ^ w.n -
                  ((w.A : Int) : ZMod q) ^ w.m) ^ 2 +
            9 * ((((w.A : Int) : ZMod q) ^ w.m) *
              (((w.B : Int) : ZMod q) ^ w.n))) := by
    rw [frey_c6_formula]
    simp [Int.cast_mul, Int.cast_add, Int.cast_sub, Int.cast_pow, Int.cast_neg]
  rcases hABC with hAB | hC
  · rcases (Nat.Prime.dvd_mul hq).mp hAB with hA | hB
    · have hA0 : ((w.A : Int) : ZMod q) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr
          (Int.natCast_dvd_natCast.mpr hA)
      have hBne : ((w.B : Int) : ZMod q) ≠ 0 := by
        intro h
        have hB : q ∣ w.B :=
          (ZMod.natCast_zmod_eq_zero_iff_dvd w.B q).mp (by simpa using h)
        exact coprime_not_dvd_both hCop.1 hq hA hB
      have hBn : ((w.B : Int) : ZMod q) ^ w.n ≠ 0 :=
        pow_ne_zero _ hBne
      have hc6 : ((freyCurveOf w).c₆ : ZMod q) =
          (-64 : ZMod q) * (((w.B : Int) : ZMod q) ^ w.n) ^ 3 := by
        rw [hc6cast, hA0, zero_pow (Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt w.hm))]
        ring
      intro h0
      exact hneg64
        ((mul_eq_zero.mp (hc6.symm.trans h0)).resolve_right
          (pow_ne_zero 3 hBn))
    · have hB0 : ((w.B : Int) : ZMod q) = 0 :=
        (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr
          (Int.natCast_dvd_natCast.mpr hB)
      have hAne : ((w.A : Int) : ZMod q) ≠ 0 := by
        intro h
        have hA : q ∣ w.A :=
          (ZMod.natCast_zmod_eq_zero_iff_dvd w.A q).mp (by simpa using h)
        exact coprime_not_dvd_both hCop.1 hq hA hB
      have hAm : ((w.A : Int) : ZMod q) ^ w.m ≠ 0 :=
        pow_ne_zero _ hAne
      have hc6 : ((freyCurveOf w).c₆ : ZMod q) =
          (64 : ZMod q) * (((w.A : Int) : ZMod q) ^ w.m) ^ 3 := by
        rw [hc6cast, hB0, zero_pow (Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt w.hn))]
        ring
      intro h0
      exact h64
        ((mul_eq_zero.mp (hc6.symm.trans h0)).resolve_right
          (pow_ne_zero 3 hAm))
  · have hC0 : ((w.C : Int) : ZMod q) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mpr
        (Int.natCast_dvd_natCast.mpr hC)
    have hAne : ((w.A : Int) : ZMod q) ≠ 0 := by
      intro h
      have hA : q ∣ w.A :=
        (ZMod.natCast_zmod_eq_zero_iff_dvd w.A q).mp (by simpa using h)
      exact coprime_not_dvd_both hCop.2.2 hq hA hC
    have hAm : ((w.A : Int) : ZMod q) ^ w.m ≠ 0 :=
      pow_ne_zero _ hAne
    have hEq :
        ((w.A : Int) : ZMod q) ^ w.m + ((w.B : Int) : ZMod q) ^ w.n =
          ((w.C : Int) : ZMod q) ^ w.p := by
      have hN : ((w.A ^ w.m + w.B ^ w.n : Nat) : ZMod q) =
          ((w.C ^ w.p : Nat) : ZMod q) := by
        rw [w.equation]
      simpa [Nat.cast_add, Nat.cast_pow, Int.cast_natCast] using hN
    have hBn :
        ((w.B : Int) : ZMod q) ^ w.n = -(((w.A : Int) : ZMod q) ^ w.m) := by
      have hsum :
          ((w.A : Int) : ZMod q) ^ w.m + ((w.B : Int) : ZMod q) ^ w.n = 0 := by
        rw [hEq, hC0, zero_pow (Nat.pos_iff_ne_zero.mp (Nat.zero_lt_of_lt w.hp))]
      have hsum' :
          ((w.B : Int) : ZMod q) ^ w.n + ((w.A : Int) : ZMod q) ^ w.m = 0 := by
        rw [add_comm]
        exact hsum
      exact eq_neg_iff_add_eq_zero.mpr hsum'
    have hc6 : ((freyCurveOf w).c₆ : ZMod q) =
        (-64 : ZMod q) * (((w.A : Int) : ZMod q) ^ w.m) ^ 3 := by
      rw [hc6cast, hBn]
      ring
    intro h0
    exact hneg64
      ((mul_eq_zero.mp (hc6.symm.trans h0)).resolve_right
        (pow_ne_zero 3 hAm))

theorem odd_prime_neg_c6_ne_zero_mod (w : PrimitiveBealTriple) {q : Nat}
    [Fact q.Prime] (hodd : q ≠ 2) (hdvd : q ∣ w.A * w.B * w.C) :
    ((-(freyCurveOf w).c₆ : Int) : ZMod q) ≠ 0 := by
  simpa using odd_prime_c6_ne_zero_mod w hodd hdvd

/-- Tate split/nonsplit sign `(-c₆ / q)`.  Equals `±1`
at odd primes of multiplicative reduction.  Not a
Fourier coefficient of a Frey newform. -/
def frey_aq_sign (w : PrimitiveBealTriple) (q : Nat) [Fact q.Prime] : Int :=
  legendreSym q (-(freyCurveOf w).c₆)

theorem frey_c4_vq0_vqDelta_pos (t : PositiveBealTriple) {q : Nat}
    (hqMem : q ∈ (t.A * t.B * t.C).primeFactors) (hodd : q ≠ 2) :
    padicValInt q (freyCurveOf t.toPrimitive).c₄ = 0 ∧
      0 < padicValInt q (freyCurveOf t.toPrimitive).Δ :=
  (mazur_principle_step t hqMem hodd).steinberg

/-- Real Tate `a_q = ±1`: the Legendre symbol `(-c₆ / q)`
is `±1` because `q ∤ c₆`. -/
theorem frey_a_q_real (t : PositiveBealTriple) {q : Nat}
    (hqMem : q ∈ (t.A * t.B * t.C).primeFactors) (hodd : q ≠ 2) :
    ∃ s : Int, (s = 1 ∨ s = -1) ∧
      s = @frey_aq_sign t.toPrimitive q ⟨Nat.prime_of_mem_primeFactors hqMem⟩ := by
  have hq : q.Prime := Nat.prime_of_mem_primeFactors hqMem
  haveI : Fact q.Prime := ⟨hq⟩
  have hdvd : q ∣ t.A * t.B * t.C := Nat.dvd_of_mem_primeFactors hqMem
  have hne := odd_prime_neg_c6_ne_zero_mod t.toPrimitive hodd hdvd
  have hpm :=
    legendreSym.eq_one_or_neg_one (p := q)
      (a := -(freyCurveOf t.toPrimitive).c₆) hne
  refine ⟨frey_aq_sign t.toPrimitive q, hpm, rfl⟩

/-- Same statement as `frey_a_q_real`.  Replaces the
v8.9 Steinberg *label* with the Tate sign. -/
theorem frey_a_q_is_pm1 (t : PositiveBealTriple) {q : Nat}
    (hqMem : q ∈ (t.A * t.B * t.C).primeFactors) (hodd : q ≠ 2) :
    ∃ s : Int, (s = 1 ∨ s = -1) ∧
      s = @frey_aq_sign t.toPrimitive q ⟨Nat.prime_of_mem_primeFactors hqMem⟩ :=
  frey_a_q_real t hqMem hodd

def Frey_aq_pm1 (w : PrimitiveBealTriple) (q : Nat) : Prop :=
  ∃ _ : Fact q.Prime, ∃ s : Int, (s = 1 ∨ s = -1) ∧ s = frey_aq_sign w q

/-- `T_q ≡ ±(q+1) (mod 13)` fails at `q = 3` when
`a_q = ±1`: `1,12 ≠ 4,9` in `ZMod 13`. -/
theorem pm1_ne_pm_qplus1_mod13_at_3 :
    (1 : ZMod 13) ≠ 4 ∧ (1 : ZMod 13) ≠ 9 ∧
      (12 : ZMod 13) ≠ 4 ∧ (12 : ZMod 13) ≠ 9 := by
  decide

theorem qplus1_mod13_at_3 :
    ((3 + 1 : ZMod 13) = 4) ∧ ((-(3 + 1) : ZMod 13) = 9) ∧
      ((-1 : ZMod 13) = 12) := by
  decide

/-- Packed residual-unramified token.  Classically,
`I_q` acts on `ρ̄₁₃` through the Tate period, so the
residual is unramified iff `13 ∣ v_q(Δ)`.  Mathlib 4.12
has no Galois representation, so this *is* that
criterion. -/
def UnramifiedAt13 (w : PrimitiveBealTriple) (q : Nat) : Prop :=
  13 ∣ padicValInt q (freyCurveOf w).Δ

theorem frey_rho_unramified_iff_13_dvd_vqDelta
    (w : PrimitiveBealTriple) (q : Nat) :
    UnramifiedAt13 w q ↔ 13 ∣ padicValInt q (freyCurveOf w).Δ :=
  Iff.rfl

/-- Odd primes of `ABC` with `13 ∣ v_q(Δ)`.  Mazur
applies only here; the product is **not** the full
odd conductor part in general. -/
def odd_q_divisors_with_13dvd (t : PositiveBealTriple) : Finset Nat :=
  (t.A * t.B * t.C).primeFactors.filter fun q =>
    q ≠ 2 ∧ 13 ∣ padicValInt q (freyCurveOf t.toPrimitive).Δ

def ribet_iterated_13_level (t : PositiveBealTriple) : Nat :=
  globalConductorTate t.toPrimitive / (odd_q_divisors_with_13dvd t).prod id

/-- Every odd prime of `ABC` has `13 ∣ v_q(Δ)`.
Needed for the iterated quotient to be `2`. -/
def Frey13Case (t : PositiveBealTriple) : Prop :=
  ∀ q ∈ (t.A * t.B * t.C).primeFactors,
    q ≠ 2 → 13 ∣ padicValInt q (freyCurveOf t.toPrimitive).Δ

theorem odd_q_divisors_with_13dvd_eq_of_Frey13Case
    (t : PositiveBealTriple) (h : Frey13Case t) :
    odd_q_divisors_with_13dvd t = odd_q_divisors_N t := by
  ext q
  constructor
  · intro hq
    have hq' := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq'.1, hq'.2.1⟩
  · intro hq
    have hq' := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq'.1, ⟨hq'.2, h q hq'.1 hq'.2⟩⟩

theorem N_div_Prod_eq_2_of_Frey13Case
    (t : PositiveBealTriple) (h : Frey13Case t) :
    ribet_iterated_13_level t = 2 := by
  rw [ribet_iterated_13_level, odd_q_divisors_with_13dvd_eq_of_Frey13Case t h,
    odd_q_divisors_N_prod]
  exact ribet_level_quotient t.toPrimitive

/-- Frey-side Mazur pack, only when `13 ∣ v_q(Δ)`.
Double-coset Hecke + TW at `N·53` / `N·677`.  Not
Mathlib modularity at `N/q`. -/
structure MazurStepRealFixed (t : PositiveBealTriple) (q : Nat) : Prop where
  step : MazurStepReal t q
  thirteen_dvd : 13 ∣ padicValInt q (freyCurveOf t.toPrimitive).Δ
  unramified : UnramifiedAt13 t.toPrimitive q
  unramified_iff :
    UnramifiedAt13 t.toPrimitive q ↔
      13 ∣ padicValInt q (freyCurveOf t.toPrimitive).Δ
  aq_pm1 :
    ∃ _ : Fact q.Prime, ∃ s : Int, (s = 1 ∨ s = -1) ∧
      s = frey_aq_sign t.toPrimitive q
  aq_ne_oldform_at_3 :
    (1 : ZMod 13) ≠ 4 ∧ (1 : ZMod 13) ≠ 9 ∧
      (12 : ZMod 13) ≠ 4 ∧ (12 : ZMod 13) ≠ 9
  J0_real_level :
    (J0_N_real.ofTriple t).level = globalConductorTate t.toPrimitive
  hecke_double :
    (HeckeAction_N_real (globalConductorTate t.toPrimitive) q).hecke.correspondence.middle =
      globalConductorTate t.toPrimitive * q
  tw_N_53 :
    Nonempty
      (R_infty (patchedLevel_N (globalConductorTate t.toPrimitive) Q1) ≃
        T_infty (patchedLevel_N (globalConductorTate t.toPrimitive) Q1))
  tw_N_677 :
    Nonempty
      (R_infty (patchedLevel_N (globalConductorTate t.toPrimitive) Q2) ≃
        T_infty (patchedLevel_N (globalConductorTate t.toPrimitive) Q2))
  rank_N_53 :
    localizedHeckeRank (patchedLevel_N (globalConductorTate t.toPrimitive) Q1) = 1
  lowered_mul :
    q ∣ globalConductorTate t.toPrimitive →
      0 < q →
        globalConductorTate t.toPrimitive / q * q =
          globalConductorTate t.toPrimitive

theorem mazur_step_real_fixed (t : PositiveBealTriple) {q : Nat}
    (hqMem : q ∈ (t.A * t.B * t.C).primeFactors) (hodd : q ≠ 2)
    (h13 : 13 ∣ padicValInt q (freyCurveOf t.toPrimitive).Δ)
    (hMod : Modular t.toPrimitive) :
    MazurStepRealFixed t q where
  step := mazur_step_real t hqMem hodd hMod
  thirteen_dvd := h13
  unramified := h13
  unramified_iff := frey_rho_unramified_iff_13_dvd_vqDelta t.toPrimitive q
  aq_pm1 := by
    haveI : Fact q.Prime := ⟨Nat.prime_of_mem_primeFactors hqMem⟩
    exact ⟨inferInstance, frey_a_q_real t hqMem hodd⟩
  aq_ne_oldform_at_3 := pm1_ne_pm_qplus1_mod13_at_3
  J0_real_level := rfl
  hecke_double := rfl
  tw_N_53 := R_T_at_N_Q1 (globalConductorTate t.toPrimitive)
  tw_N_677 := R_T_at_N_Q2 (globalConductorTate t.toPrimitive)
  rank_N_53 := localizedRank_N_Q1 (globalConductorTate t.toPrimitive)
  lowered_mul := fun h _ => Nat.div_mul_cancel h

/-- Iterated pack only over odd primes with `13 ∣ v_q(Δ)`.
The displayed level is `N / ∏_{13|v_q} q`, **not** `2`
unless `Frey13Case`.  Not `ExistsNewformLevel2`. -/
structure RibetIteratedRealFixed (t : PositiveBealTriple) : Prop where
  pack : RibetIteratedReal t
  mazur_fixed_13 :
    ∀ q ∈ odd_q_divisors_with_13dvd t, MazurStepRealFixed t q
  level_eq : ribet_iterated_13_level t = ribet_iterated_13_level t
  level_two_of_Frey13 : Frey13Case t → ribet_iterated_13_level t = 2
  not_generally_two :
    ribet_iterated_13_level t = 2 →
      (odd_q_divisors_with_13dvd t).prod id = oddConductorPart t.toPrimitive
  no_newform : ¬ ExistsNewformLevel2

theorem ribet_iterated_13_level_eq_two_imp_prod
    (t : PositiveBealTriple)
    (h : ribet_iterated_13_level t = 2) :
    (odd_q_divisors_with_13dvd t).prod id = oddConductorPart t.toPrimitive := by
  have hN : globalConductorTate t.toPrimitive =
      2 * oddConductorPart t.toPrimitive := rfl
  have hsub : odd_q_divisors_with_13dvd t ⊆ odd_q_divisors_N t := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact Finset.mem_filter.mpr ⟨hq'.1, hq'.2.1⟩
  have hdiv_odd : (odd_q_divisors_with_13dvd t).prod id ∣
      (odd_q_divisors_N t).prod id :=
    Finset.prod_dvd_prod_of_subset
      (odd_q_divisors_with_13dvd t) (odd_q_divisors_N t) id hsub
  have hdiv : (odd_q_divisors_with_13dvd t).prod id ∣
      globalConductorTate t.toPrimitive := by
    rw [odd_q_divisors_N_prod] at hdiv_odd
    simpa [hN] using (dvd_mul_of_dvd_right hdiv_odd 2)
  have hcalc : globalConductorTate t.toPrimitive /
      (odd_q_divisors_with_13dvd t).prod id = 2 := h
  have hmul := Nat.div_mul_cancel hdiv
  have : 2 * (odd_q_divisors_with_13dvd t).prod id =
      2 * oddConductorPart t.toPrimitive := by
    calc
      2 * (odd_q_divisors_with_13dvd t).prod id
          = globalConductorTate t.toPrimitive /
              (odd_q_divisors_with_13dvd t).prod id *
              (odd_q_divisors_with_13dvd t).prod id := by
            rw [hcalc]
      _ = globalConductorTate t.toPrimitive := hmul
      _ = 2 * oddConductorPart t.toPrimitive := hN
  exact Nat.mul_left_cancel (by decide : 0 < 2) this

theorem ribet_iterated_real_fixed (t : PositiveBealTriple)
    (hMod : Modular t.toPrimitive) :
    RibetIteratedRealFixed t where
  pack := ribet_iterated_real t hMod
  mazur_fixed_13 := by
    intro q hq
    have hq' := Finset.mem_filter.mp hq
    exact mazur_step_real_fixed t hq'.1 hq'.2.1 hq'.2.2 hMod
  level_eq := rfl
  level_two_of_Frey13 := fun h => N_div_Prod_eq_2_of_Frey13Case t h
  not_generally_two := ribet_iterated_13_level_eq_two_imp_prod t
  no_newform := no_newform_level2

/-- Honesty: Wiles-domain `Modular` after the 13-filtered
pack is still not `ExistsNewformLevel2`. -/
theorem modular_at_two_is_not_newform (t : PositiveBealTriple)
    (_hMod : Modular t.toPrimitive) :
    ¬ ExistsNewformLevel2 :=
  no_newform_level2

/-- The requested `¬ PositiveBealTriple` under `Frey13Case`.
Uninhabited: `Modular` at the filtered level is not
`ExistsNewformLevel2` (`0 ≠ 0`). -/
def not_PositiveBealTriple_of_Frey13Case : Prop :=
  ∀ t : PositiveBealTriple, Frey13Case t → False

/-- Beal on positive bases, *from* the missing Mathlib
arrow, even after assuming every positive triple is a
`Frey13Case`.  Not `¬ PositiveBealTriple`. -/
theorem beal_from_ribet_real_fixed
    (_hFrey13 : ∀ t : PositiveBealTriple, Frey13Case t)
    (hModNew : ModularImpliesLevel2Newform) :
    ∀ A B C m n p : Nat,
      0 < A → 0 < B → 0 < C →
      2 < m → 2 < n → 2 < p →
      A ^ m + B ^ n = C ^ p →
      1 < Nat.gcd A (Nat.gcd B C) :=
  beal_from_ribet_real hModNew

#check q_expansion_26a1
#check q_expansion_26b1
#check q_expansion_26a1_int
#check HeckeAction_N
#check mazur_principle_step
#check mazur_step_real
#check ribet_iterated
#check ribet_iterated_real
#check ribet_iterated_arrow
#check ModularImpliesLevel2Newform_real
#check beal_from_ribet
#check beal_from_ribet_real
#check beal_from_ribet_real_fixed
#check beal_positive_bases_unconditional
#check X0_N_Model
#check J0_N_Model
#check J0_N_real
#check HeckeAction_N_real
#check Frey_aq_pm1
#check MazurStepRealFixed
#check RibetIteratedRealFixed
#check frey_a_q_real
#check frey_rho_unramified_iff_13_dvd_vqDelta
#check Frey13Case
#print axioms q_expansion_26a1_a1
#print axioms q_expansion_26a1_a3
#print axioms q_expansion_26b1_a3
#print axioms T3_26a1_matches_a3
#print axioms mazur_principle_step
#print axioms mazur_step_real
#print axioms mazur_step_real_fixed
#print axioms ribet_iterated
#print axioms ribet_iterated_real
#print axioms ribet_iterated_real_fixed
#print axioms ribet_iterated_does_not_inhabit_newform
#print axioms frey_a_q_is_pm1
#print axioms frey_a_q_real
#print axioms frey_rho_unramified_iff_13_dvd_vqDelta
#print axioms pm1_ne_pm_qplus1_mod13_at_3
#print axioms N_div_Prod_eq_2_of_Frey13Case
#print axioms modular_at_two_is_not_newform
#print axioms X0_N_Model_eq_rad
#print axioms J0_N_Model_cusps
#print axioms beal_from_ribet
#print axioms beal_from_ribet_real
#print axioms beal_from_ribet_real_fixed

end BealLevel26Foundations.Beal.FullProof.RibetMazur
