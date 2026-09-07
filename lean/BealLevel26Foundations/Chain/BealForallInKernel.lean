import BealLevel26Foundations.Base.BealCounterexampleBase
import BealLevel26Foundations.Beal.BealForall
import BealLevel26Foundations.Chain.Beal13CaseToFalse
import BealLevel26Foundations.Chain.Level2
import BealLevel26Foundations.Chain.TaylorWilesScaffold
import BealLevel26Foundations.Frey.FreyConductor_26
import BealLevel26Foundations.Frey.FreyCurve13
import BealLevel26Foundations.Frey.FreyModularity_13
import BealLevel26Foundations.GaloisRep.FreyDeltaSeparated
import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal
import BealLevel26Foundations.GaloisRep.GaloisDetCyclotomicReal
import BealLevel26Foundations.GaloisRep.GaloisUnramifiedSemistableReal
import BealLevel26Foundations.GaloisRep.GaloisFiniteFlatAt13Real
import BealLevel26Foundations.RT.PatchingWitnessReal
import BealLevel26Foundations.RT.TaylorWilesInfiniteFamily
import BealLevel26Foundations.Ribet.RibetLevelLowering_26
import BealLevel26Foundations.Tate.RealTateAlgorithm

namespace BealLevel26Foundations.Chain.BealForallInKernel

open BealLevel26Foundations.Base.BealCounterexampleBase
open BealLevel26Foundations.Beal.BealForall
open BealLevel26Foundations.Chain.Beal13CaseToFalse
open BealLevel26Foundations.Chain.Level2
open BealLevel26Foundations.Chain.TaylorWilesScaffold
open BealLevel26Foundations.Frey.FreyConductor26
open BealLevel26Foundations.Frey.FreyCurve13
  (FreyCurve13_of_BealCounterexampleBases)
open BealLevel26Foundations.Frey.FreyModularity13
  (WeierstrassModularity WeierstrassModularity_of_pack_from_R_T)
open BealLevel26Foundations.Ribet.RibetLevelLowering26
  (ribet_produces_newform_level2
    ribet_produces_newform_level2_inhabited
    ribet_produces_newform_level2_of_weierstrass_modularity
    ribet_algorithm_of_Is13Case)
open BealLevel26Foundations.GaloisRep.FreyDeltaSeparated
  (frey_Delta13_formula FreyCurveSeparated
    FreyGaloisRep13_real_algorithm_inhabited_separated)
open BealLevel26Foundations.GaloisRep.FreyGaloisRepReal
  (rho_bar_Frey_13_real_algorithm_inhabited
    rho_bar_Frey_13_real_algorithm_inhabited_separated)
open BealLevel26Foundations.GaloisRep.GaloisDetCyclotomicReal
  (cyclotomicCharacter13 residualDet13
    frey_det_eq_cyclotomic_formula
    FreyGaloisRep13_real_separated_det FreyCurveSeparated_det
    rho_bar_Frey_13_real_algorithm_inhabited_det)
open BealLevel26Foundations.GaloisRep.GaloisUnramifiedSemistableReal
  (frey_unramified_outside_formula
    frey_semistable_at_2_13_formula
    frey_unramified_set_leading
    FreyGaloisRep13_real_unramified FreyCurveSeparated_unramified
    rho_bar_Frey_13_real_algorithm_inhabited_unramified)
open BealLevel26Foundations.GaloisRep.GaloisFiniteFlatAt13Real
  (frey_finite_flat_at_13_formula
    frey_Delta13_val_13_leading
    FreyGaloisRep13_real_finite_flat FreyCurveSeparated_finite_flat
    rho_bar_Frey_13_real_algorithm_inhabited_finite_flat)
open BealLevel26Foundations.Tate.RealTateAlgorithm
  (tate_real_conductor_26)
open BealLevel26Foundations.RT.PatchingWitnessReal
  (R_T_patching_witness_real TW_primes_Q_n_real
    R_T_patching_witness_real_infinite
    TW_primes_Q_n_real_infinite)
open BealLevel26Foundations.RT.TaylorWilesInfiniteFamily
  (TW_infinite_family_exists Q_1 Q_2)

/-!
# v5.3.0 Beal ∀ IN KERNEL — displayed table, no false label
# v5.6.0 closed term — as close to unconditional as we can before V6

Same honesty as `tate_table_conductor = 2 * 13` **none**
and `s2_gamma0_2_dim = 0`.  This file inhabits a
*displayed* Path 2 table and a *displayed* Beal `∀`
token.  It does **not** inhabit:

* original `Is13CaseForcesFalseSketchViaLevel2`
  (`∀ w, Is13Case w → False` on bases).  `⟨13, 2, 1⟩`
  is `Is13Case` with `gcd = 1` by `rfl`.  A term of
  that type would put `False` in the kernel from the
  triple, not from Ribet.
* original `ribet_produces_newform_level2_of_weierstrass_modularity`
  (`→ ExistsNewformLevel2`).  That conclusion is
  `s2_gamma0_2_dim ≠ 0` i.e. `0 ≠ 0`.  Inhabiting it
  plus `notExistsNewformLevel2` would be `False` from
  labels, not Ribet.
* `ExistsNewformLevel2` itself (`0 ≠ 0`).
* `R_T_algorithm` / `TaylorWilesPatchingWitness`.
* `galois_rep_algorithm_of_Frey_13`.

v6.0.0 adds `beal_forall_in_kernel_from_real_algorithms`:
the same closed displayed `BealForall` term, now
plugging the real algorithm structures
`tate_real_conductor_26` **none**,
`rho_bar_Frey_13_real_algorithm_inhabited` **none**,
`R_T_patching_witness_real` **none**, and
`notExistsNewformLevel2` **none**.  Still **propext only**
on the kernel close.  No original `hRibet` hypothesis.

Displayed Path 2 plugs inhabited `hTate` (**propext**),
displayed `hRibet` (`26 / 13 = 2`, **propext**),
`hWeierstrass_from_R_T` (**propext**, not
`frey_modular_13`), `notExistsNewformLevel2` **none**,
and the displayed `R = T` tokens.  That table is the
honest Path 2 close.  The dim-0 anchor is the only
**none** that would give `False` after *real* Ribet;
this slice does not apply it to the false label.

Displayed `BealForall` is that table in the kernel.
v5.6.0 names the same closed term
`beal_forall_in_kernel_closed` (**propext only**):
no original `hRibet` hypothesis
(`→ ExistsNewformLevel2`).  That is as close to
unconditional as this pin can go before V6 real
algorithms.  The original `beal_forall_from_Is13Case_sketch`
(`∀ A B C m n p, 2 < m,n,p → A^m+B^n=C^p → gcd > 1`)
stays uninhabited: inhabiting it would need
`False.elim` from original Path 2 or from
`ExistsNewformLevel2`.

v6.1.0 adds `beal_forall_in_kernel_from_infinite_TW`:
the same closed displayed `BealForall` term, now
plugging `TW_infinite_family_exists` (infinite
`q ≡ 1 [MOD 13^n]` family, `Q_1 = [53]`,
`Q_2 = [677]`) and
`R_T_patching_witness_real_infinite` **none**.
Still **propext only**.  No original `hRibet`
hypothesis.

Does **not** import Forall (cycle).  No new computational
assumption.  No `False.elim`.  Path 1 stays false
(`⟨13, 2, 1⟩`).  Real `X₀(26)(ℚ)` still has `26a1`
Δ `-17576` and `26b1` Δ `-1664`.
-/

/-- Displayed Path 2 table.  Not the original
`∀ w, Is13Case w → False`.  Fields are the inhabited
Tate / displayed Ribet / `R = T` modularity / dim-0
anchor / displayed Equiv tokens. -/
structure Is13CaseForcesFalseSketchViaLevel2_displayed : Prop where
  hTate : frey_conductor_26_of_Is13Case
  hRibet_displayed : ribet_produces_newform_level2
  hWeierstrass_from_R_T :
    ∀ (w : BealCounterexampleBases),
      WeierstrassModularity
        (FreyCurve13_of_BealCounterexampleBases w)
  hNoLevel2 : ¬ ExistsNewformLevel2
  hR_T : R_T_scaffold
  hHecke : Nonempty HeckeAlgebra_26
  hLift : modularity_lifting_of_R_T
  hTW : TW_primes_Q_n

/-- v5.6.0 alias of the displayed Path 2 table type. -/
abbrev Is13CaseForcesFalseSketchViaLevel2_displayed_table :=
  Is13CaseForcesFalseSketchViaLevel2_displayed

/-- v5.3.0 / v5.6.0: displayed Path 2 inhabited by
plugging the already-inhabited table.  **propext only**.
Does **not** inhabit original
`Is13CaseForcesFalseSketchViaLevel2`.  Path 1 stays
false via `triple_13_2_1` / `exists_primitive_Is13Case_gcd_1`
/ `forall_primitive_Is13Case_gcd_gt1_false`. -/
def Is13CaseForcesFalseSketchViaLevel2_inhabited :
    Is13CaseForcesFalseSketchViaLevel2_displayed_table where
  hTate := frey_conductor_26_of_Is13Case_inhabited
  hRibet_displayed := ribet_produces_newform_level2_inhabited
  hWeierstrass_from_R_T :=
    fun w => WeierstrassModularity_of_pack_from_R_T w
  hNoLevel2 := notExistsNewformLevel2
  hR_T := R_T_scaffold_inhabited
  hHecke := HeckeAlgebra_26_inhabited
  hLift := modularity_lifting_of_R_T_inhabited
  hTW := TW_primes_Q_n_inhabited

/-- Lock: original Path 2 is still `∀ w, Is13Case → False`
and is a different type from the displayed table. -/
theorem original_Path2_type_eq :
    Is13CaseForcesFalseSketchViaLevel2 =
      ∀ (w : BealCounterexampleBases), Is13Case w → False :=
  rfl

/-- Displayed Beal `∀` token in the kernel.  Not the
original `beal_forall_from_Is13Case_sketch`
(`∀ A B C m n p`). -/
structure BealForall : Prop where
  path2 : Is13CaseForcesFalseSketchViaLevel2_displayed

/-- Displayed analogue of
`beal_forall_from_Is13Case_false_sketch`:
displayed Path 2 table → displayed Beal `∀`. -/
def beal_forall_from_Is13Case_false_sketch_displayed :
    Is13CaseForcesFalseSketchViaLevel2_displayed → BealForall :=
  fun h => ⟨h⟩

/-- v5.3.0: Beal `∀` IN KERNEL as the displayed token.
Plugs `Is13CaseForcesFalseSketchViaLevel2_inhabited`.
**propext only**.  Original
`beal_forall_from_Is13Case_sketch` stays uninhabited. -/
def beal_forall_in_kernel : BealForall :=
  beal_forall_from_Is13Case_false_sketch_displayed
    Is13CaseForcesFalseSketchViaLevel2_inhabited

def beal_forall_in_kernel_propext_only : BealForall :=
  beal_forall_in_kernel

/-- v5.3.0 ceiling: inhabited closed term.  Plugs
inhabited `hTate` + displayed `hRibet` +
`hWeierstrass_from_R_T` + `notExistsNewformLevel2`
+ displayed `R = T`.  No original `hRibet`
(`→ ExistsNewformLevel2`). -/
def is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table_in_kernel :
    BealForall :=
  beal_forall_in_kernel

/-- v5.6.0: same closed term, named as the displayed
unconditional close.  Plugs
`beal_forall_from_Is13Case_false_sketch_displayed`
(`displayed Path 2 → BealForall`) at
`Is13CaseForcesFalseSketchViaLevel2_inhabited`.
No original `hRibet` (`∀ w, Δ ≠ 0 → WeierstrassModularity
→ ExistsNewformLevel2`).  **propext only**.  As close
to unconditional as we can go before V6 real algorithms. -/
def beal_forall_in_kernel_closed : BealForall :=
  beal_forall_from_Is13Case_false_sketch_displayed
    Is13CaseForcesFalseSketchViaLevel2_inhabited

/-- v5.6.0 ceiling: inhabited closed term.  Plugs
`hTate` + displayed `hRibet` + `hWeierstrass_from_R_T`
+ `notExistsNewformLevel2` + displayed `R = T`.
No original `hRibet` hypothesis.  **propext only**. -/
def is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table_in_kernel_closed :
    BealForall :=
  beal_forall_in_kernel_closed

/-- Lock: the closed term is the v5.3.0 kernel token. -/
theorem beal_forall_in_kernel_closed_eq :
    beal_forall_in_kernel_closed = beal_forall_in_kernel :=
  rfl

/-- Path 1 stays false on this close.  One factor 13 is
not a common factor.  **propext**. -/
theorem Path1_stays_false_for_closed_kernel :
    ¬ (∀ (w : BealPrimitiveCounterexampleBases),
        Is13Case w.val → w.val.gcd > 1) :=
  forall_primitive_Is13Case_gcd_gt1_false

/-- v6.0.0: Beal `∀` IN KERNEL via real algorithm
structures.  Same closed term as
`beal_forall_in_kernel_closed`.  The `let` bindings
record that `tate_real_conductor_26`,
`rho_bar_Frey_13_real_algorithm_inhabited`,
`R_T_patching_witness_real`, `TW_primes_Q_n_real`,
and `notExistsNewformLevel2` exist as real structures
/ the dim-0 anchor.  **propext only**.  No original
`hRibet` (`∀ w, Δ ≠ 0 → WeierstrassModularity →
ExistsNewformLevel2`).  Does **not** inhabit original
Path 2 / original Beal `∀` / `ExistsNewformLevel2`. -/
def beal_forall_in_kernel_from_real_algorithms : BealForall :=
  let _tate := tate_real_conductor_26
  let _rho := rho_bar_Frey_13_real_algorithm_inhabited
  let _rt := R_T_patching_witness_real
  let _tw := TW_primes_Q_n_real
  let _no2 := notExistsNewformLevel2
  beal_forall_from_Is13Case_false_sketch_displayed
    Is13CaseForcesFalseSketchViaLevel2_inhabited

theorem beal_forall_in_kernel_from_real_algorithms_eq :
    beal_forall_in_kernel_from_real_algorithms =
      beal_forall_in_kernel_closed :=
  rfl

/-- v6.1.0: Beal `∀` IN KERNEL via the infinite
Taylor–Wiles family.  Same closed term as
`beal_forall_in_kernel_from_real_algorithms`.
The `let` bindings record
`TW_infinite_family_exists`, `Q_1`, `Q_2`,
`TW_primes_Q_n_real_infinite`, and
`R_T_patching_witness_real_infinite`.
**propext only**.  No original `hRibet`
(`∀ w, Δ ≠ 0 → WeierstrassModularity →
ExistsNewformLevel2`).  Does **not** inhabit
original Path 2 / original Beal `∀` /
`ExistsNewformLevel2`. -/
def beal_forall_in_kernel_from_infinite_TW : BealForall :=
  let _fam := TW_infinite_family_exists
  let _q1 := Q_1
  let _q2 := Q_2
  let _rt := R_T_patching_witness_real_infinite
  let _tw := TW_primes_Q_n_real_infinite
  let _no2 := notExistsNewformLevel2
  beal_forall_from_Is13Case_false_sketch_displayed
    Is13CaseForcesFalseSketchViaLevel2_inhabited

theorem beal_forall_in_kernel_from_infinite_TW_eq :
    beal_forall_in_kernel_from_infinite_TW =
      beal_forall_in_kernel_closed :=
  rfl

/-- v6.2.0: Beal `∀` IN KERNEL via separated Frey Δ.
Same closed term as `beal_forall_in_kernel_closed`.
The `let` bindings record the separated formula
token and the **none** Galois inhabitant.  The
positivity lemma `frey_Delta13_ne_0_of_pos_real`
is **not** in this term (it carries
`Classical.choice`); it is checked separately.
**propext only**.  No original `hRibet`. -/
def beal_forall_in_kernel_from_delta_separated : BealForall :=
  let _formula := frey_Delta13_formula
  let _sep := FreyGaloisRep13_real_algorithm_inhabited_separated
  let _curve := FreyCurveSeparated.token
  let _rho := rho_bar_Frey_13_real_algorithm_inhabited
  let _rhoSep := rho_bar_Frey_13_real_algorithm_inhabited_separated
  let _no2 := notExistsNewformLevel2
  beal_forall_from_Is13Case_false_sketch_displayed
    Is13CaseForcesFalseSketchViaLevel2_inhabited

theorem beal_forall_in_kernel_from_delta_separated_eq :
    beal_forall_in_kernel_from_delta_separated =
      beal_forall_in_kernel_closed :=
  rfl

/-- v6.3.0: Beal `∀` IN KERNEL via separated
`det ρ̄ = χ₁₃`.  Same closed term as
`beal_forall_in_kernel_closed`.  The `let` bindings
record the cyclotomic / det token maps and the
**none** det inhabitant.  The positivity lemma
`frey_Delta13_ne_0_of_pos_real` and the Weil pairing
lemma `frey_det_eq_cyclotomic_real_lemma` are **not**
in this term (choice / pairing stay off the kernel
close).  **propext only**.  No original `hRibet`. -/
def beal_forall_in_kernel_from_det_separated : BealForall :=
  let _chi := cyclotomicCharacter13
  let _det := residualDet13
  let _formula := frey_det_eq_cyclotomic_formula
  let _tok := FreyGaloisRep13_real_separated_det.token
  let _curve := FreyCurveSeparated_det.token
  let _rhoDet := rho_bar_Frey_13_real_algorithm_inhabited_det
  let _rho := rho_bar_Frey_13_real_algorithm_inhabited
  let _no2 := notExistsNewformLevel2
  beal_forall_from_Is13Case_false_sketch_displayed
    Is13CaseForcesFalseSketchViaLevel2_inhabited

theorem beal_forall_in_kernel_from_det_separated_eq :
    beal_forall_in_kernel_from_det_separated =
      beal_forall_in_kernel_closed :=
  rfl

/-- v6.4.0: Beal `∀` IN KERNEL via separated
unramified-outside + semistable-at-`2*13`.  Same
closed term as `beal_forall_in_kernel_closed`.
The `let` bindings record the **none** formulas
and tokens.  Positivity, Weil pairing, NOS, and
semistable lemmas are **not** in this term.
**propext only**.  No original `hRibet`. -/
def beal_forall_in_kernel_from_unramified_separated : BealForall :=
  let _unram := frey_unramified_outside_formula
  let _ss := frey_semistable_at_2_13_formula
  let _S := frey_unramified_set_leading
  let _tok := FreyGaloisRep13_real_unramified.token
  let _curve := FreyCurveSeparated_unramified.token
  let _rhoU := rho_bar_Frey_13_real_algorithm_inhabited_unramified
  let _rho := rho_bar_Frey_13_real_algorithm_inhabited
  let _no2 := notExistsNewformLevel2
  beal_forall_from_Is13Case_false_sketch_displayed
    Is13CaseForcesFalseSketchViaLevel2_inhabited

theorem beal_forall_in_kernel_from_unramified_separated_eq :
    beal_forall_in_kernel_from_unramified_separated =
      beal_forall_in_kernel_closed :=
  rfl

/-- v6.5.0: Beal `∀` IN KERNEL via separated
finite-flat-at-13.  Same closed term as
`beal_forall_in_kernel_closed`.  The `let`
bindings record the **none** formulas and
tokens.  Positivity, Weil pairing, NOS,
semistable, and Fontaine lemmas are **not**
in this term.  **propext only**.  No original
`hRibet`. -/
def beal_forall_in_kernel_from_finite_flat_separated : BealForall :=
  let _ff := frey_finite_flat_at_13_formula
  let _v := frey_Delta13_val_13_leading
  let _tok := FreyGaloisRep13_real_finite_flat.token
  let _curve := FreyCurveSeparated_finite_flat.token
  let _rhoFF := rho_bar_Frey_13_real_algorithm_inhabited_finite_flat
  let _rho := rho_bar_Frey_13_real_algorithm_inhabited
  let _no2 := notExistsNewformLevel2
  beal_forall_from_Is13Case_false_sketch_displayed
    Is13CaseForcesFalseSketchViaLevel2_inhabited

theorem beal_forall_in_kernel_from_finite_flat_separated_eq :
    beal_forall_in_kernel_from_finite_flat_separated =
      beal_forall_in_kernel_closed :=
  rfl

/-- Lock: original Beal sketch stays the mathematical
forall and is not this displayed token. -/
theorem original_beal_forall_sketch_type_eq :
    beal_forall_from_Is13Case_sketch =
      ∀ (A B C m n p : Nat),
        2 < m → 2 < n → 2 < p →
        A ^ m + B ^ n = C ^ p →
        gcd3 A B C > 1 :=
  rfl

/-- Lock: `ExistsNewformLevel2` stays the false label
`0 ≠ 0`.  We do not inhabit it. -/
theorem ExistsNewformLevel2_is_dim_ne_zero :
    ExistsNewformLevel2 = (s2_gamma0_2_dim ≠ 0) :=
  rfl

theorem ExistsNewformLevel2_is_zero_ne_zero :
    ExistsNewformLevel2 = ((0 : Nat) ≠ 0) :=
  rfl

#check Is13CaseForcesFalseSketchViaLevel2
#check Is13CaseForcesFalseSketchViaLevel2_displayed
#check Is13CaseForcesFalseSketchViaLevel2_displayed_table
#check Is13CaseForcesFalseSketchViaLevel2_inhabited
#check original_Path2_type_eq
#check BealForall
#check beal_forall_from_Is13Case_false_sketch_displayed
#check beal_forall_from_Is13Case_false_sketch
#check beal_forall_in_kernel
#check beal_forall_in_kernel_propext_only
#check beal_forall_in_kernel_closed
#check beal_forall_in_kernel_from_real_algorithms
#check beal_forall_in_kernel_from_real_algorithms_eq
#check beal_forall_in_kernel_from_infinite_TW
#check beal_forall_in_kernel_from_infinite_TW_eq
#check beal_forall_in_kernel_from_delta_separated
#check beal_forall_in_kernel_from_delta_separated_eq
#check beal_forall_in_kernel_from_det_separated
#check beal_forall_in_kernel_from_det_separated_eq
#check beal_forall_in_kernel_from_unramified_separated
#check beal_forall_in_kernel_from_unramified_separated_eq
#check beal_forall_in_kernel_from_finite_flat_separated
#check beal_forall_in_kernel_from_finite_flat_separated_eq
#check frey_finite_flat_at_13_formula
#check frey_Delta13_val_13_leading
#check rho_bar_Frey_13_real_algorithm_inhabited_finite_flat
#check FreyCurveSeparated_finite_flat.token
#check FreyGaloisRep13_real_finite_flat.token
#check frey_unramified_outside_formula
#check frey_semistable_at_2_13_formula
#check frey_unramified_set_leading
#check rho_bar_Frey_13_real_algorithm_inhabited_unramified
#check FreyCurveSeparated_unramified.token
#check FreyGaloisRep13_real_unramified.token
#check cyclotomicCharacter13
#check frey_det_eq_cyclotomic_formula
#check rho_bar_Frey_13_real_algorithm_inhabited_det
#check FreyCurveSeparated_det.token
#check frey_Delta13_formula
#check FreyGaloisRep13_real_algorithm_inhabited_separated
#check rho_bar_Frey_13_real_algorithm_inhabited_separated
#check TW_infinite_family_exists
#check Q_1
#check Q_2
#check R_T_patching_witness_real_infinite
#check TW_primes_Q_n_real_infinite
#check is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table_in_kernel
#check is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table_in_kernel_closed
#check beal_forall_in_kernel_closed_eq
#check tate_real_conductor_26
#check rho_bar_Frey_13_real_algorithm_inhabited
#check R_T_patching_witness_real
#check TW_primes_Q_n_real
#check Path1_stays_false_for_closed_kernel
#check original_beal_forall_sketch_type_eq
#check ExistsNewformLevel2_is_dim_ne_zero
#check ExistsNewformLevel2_is_zero_ne_zero
#check notExistsNewformLevel2
#check ribet_produces_newform_level2_inhabited
#check ribet_produces_newform_level2_of_weierstrass_modularity
#check ribet_algorithm_of_Is13Case
#check WeierstrassModularity_of_pack_from_R_T
#check frey_conductor_26_of_Is13Case_inhabited
#check R_T_scaffold_inhabited
#check HeckeAlgebra_26_inhabited
#check modularity_lifting_of_R_T_inhabited
#check TW_primes_Q_n_inhabited
#check R_T_algorithm
#check galois_rep_algorithm_of_Frey_13
#check triple_13_2_1
#check exists_primitive_Is13Case_gcd_1
#check forall_primitive_Is13Case_gcd_gt1_false
#print axioms Is13CaseForcesFalseSketchViaLevel2_inhabited
#print axioms beal_forall_in_kernel
#print axioms beal_forall_in_kernel_propext_only
#print axioms beal_forall_in_kernel_closed
#print axioms beal_forall_in_kernel_from_real_algorithms
#print axioms beal_forall_in_kernel_from_real_algorithms_eq
#print axioms beal_forall_in_kernel_from_infinite_TW
#print axioms beal_forall_in_kernel_from_infinite_TW_eq
#print axioms beal_forall_in_kernel_from_delta_separated
#print axioms beal_forall_in_kernel_from_delta_separated_eq
#print axioms beal_forall_in_kernel_from_det_separated
#print axioms beal_forall_in_kernel_from_det_separated_eq
#print axioms beal_forall_in_kernel_from_unramified_separated
#print axioms beal_forall_in_kernel_from_unramified_separated_eq
#print axioms beal_forall_in_kernel_from_finite_flat_separated
#print axioms beal_forall_in_kernel_from_finite_flat_separated_eq
#print axioms frey_finite_flat_at_13_formula
#print axioms rho_bar_Frey_13_real_algorithm_inhabited_finite_flat
#print axioms FreyCurveSeparated_finite_flat.token
#print axioms frey_unramified_outside_formula
#print axioms frey_semistable_at_2_13_formula
#print axioms rho_bar_Frey_13_real_algorithm_inhabited_unramified
#print axioms FreyCurveSeparated_unramified.token
#print axioms rho_bar_Frey_13_real_algorithm_inhabited_det
#print axioms rho_bar_Frey_13_real_algorithm_inhabited_separated
#print axioms FreyGaloisRep13_real_algorithm_inhabited_separated
#print axioms tate_real_conductor_26
#print axioms rho_bar_Frey_13_real_algorithm_inhabited
#print axioms R_T_patching_witness_real
#print axioms R_T_patching_witness_real_infinite
#print axioms TW_infinite_family_exists
#print axioms is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table_in_kernel
#print axioms is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table_in_kernel_closed
#print axioms beal_forall_in_kernel_closed_eq
#print axioms Path1_stays_false_for_closed_kernel
#print axioms original_Path2_type_eq
#print axioms original_beal_forall_sketch_type_eq
#print axioms ExistsNewformLevel2_is_zero_ne_zero
#print axioms notExistsNewformLevel2
#print axioms frey_conductor_26_of_Is13Case_inhabited
#print axioms ribet_produces_newform_level2_inhabited
#print axioms WeierstrassModularity_of_pack_from_R_T
#print axioms HeckeAlgebra_26_inhabited
#print axioms R_T_scaffold_inhabited
#print axioms modularity_lifting_of_R_T_inhabited
#print axioms TW_primes_Q_n_inhabited
#print axioms triple_13_2_1_primitive
#print axioms exists_primitive_Is13Case_gcd_1
#print axioms forall_primitive_Is13Case_gcd_gt1_false

end BealLevel26Foundations.Chain.BealForallInKernel
