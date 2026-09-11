/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v8.75.0 — first honest Beal rows.

`beal_4_13_13_gap3_B_196_eliminated` and
`beal_4_13_13_gap3_B_1500003_eliminated`
are `¬ ∃ A, A^4 + B^13 = C^13` for the
two named gap-3 witnesses
`(B,C) = (196,199)` and
`(1500003,1500006)`.

The kill is fourth-power residues
modulo 16 (`A^4 ≡ 0` or `1`), not
Mazur, not Borel, not a Mathlib
residual representation, and **not**
Ribet level-lowering.  The v8.69.0–
v8.74.0 displayed facts
(`exists_newform_level_26_dim2`,
`frey_mod13_irreducible`,
`level26_a_eliminated_by_53` /
`level26_b_eliminated_by_443`) are
recorded as a pack.  They do **not**
inhabit these two Beal negations.

`frey_modular` stays `Classical.em`.
`level_lowering_to_26` stays a Prop.
The inhabited Ribet-Mazur pack remains
`ribet_mazur_pack_q_13_level_26` via
`hK.left` / `hK.right` in RibetMazur
(this file does **not** import
`RibetMazur`; that would cycle).

`beal_4_13_13_gap3_B_le_2M_eliminated`
stays `Classical.em`.  Density/Step
`kraus_elimination_q_13_level_26`
stays the uninhabited `∀`.
Chain `ExistsNewformLevel2` stays
`0 ≠ 0`.  No new Beal `∀`.

Does **not** import `RibetMazur`.
Does **not** import
`Mathlib.NumberTheory.ModularForms.Basic`.
Does **not** import the axiom
`frey_modular_13` from
`Modularity/FreyModularity_13.lean`.
Not imported by the 24-module none chain.
-/

import BealLevel26Foundations.Beal.FullProof.Level26_Newforms
import BealLevel26Foundations.Beal.FullProof.FreyModularity
import Mathlib.Tactic

namespace BealLevel26Foundations.BealElim

open BealLevel26Foundations.Level26_Newforms
open BealLevel26Foundations.FreyModularity

/-- Residues `< 16` have fourth power `0` or `1 [MOD 16]`. -/
theorem fourth_pow_of_lt_16 :
    ∀ a : Nat, a < 16 → a ^ 4 % 16 = 0 ∨ a ^ 4 % 16 = 1
  | 0, _ => Or.inl rfl
  | 1, _ => Or.inr rfl
  | 2, _ => Or.inl rfl
  | 3, _ => Or.inr rfl
  | 4, _ => Or.inl rfl
  | 5, _ => Or.inr rfl
  | 6, _ => Or.inl rfl
  | 7, _ => Or.inr rfl
  | 8, _ => Or.inl rfl
  | 9, _ => Or.inr rfl
  | 10, _ => Or.inl rfl
  | 11, _ => Or.inr rfl
  | 12, _ => Or.inl rfl
  | 13, _ => Or.inr rfl
  | 14, _ => Or.inl rfl
  | 15, _ => Or.inr rfl
  | n + 16, h =>
      absurd h (Nat.not_lt_of_le (Nat.le_add_left 16 n))

/-- `n^k % m = (n % m)^k % m`. -/
theorem pow_mod_eq (n k m : Nat) :
    n ^ k % m = (n % m) ^ k % m := by
  induction k with
  | zero =>
    exact
      (congrArg (fun t => t % m) (Nat.pow_zero n)).trans
        (congrArg (fun t => t % m) (Nat.pow_zero (n % m))).symm
  | succ k ih =>
    have hs : n ^ (k + 1) = n ^ k * n := Nat.pow_succ n k
    have hs' : (n % m) ^ (k + 1) = (n % m) ^ k * (n % m) :=
      Nat.pow_succ (n % m) k
    have h1 : n ^ (k + 1) % m = (n ^ k * n) % m :=
      congrArg (fun t => t % m) hs
    have h2 : (n ^ k * n) % m = (n ^ k % m * (n % m)) % m :=
      Nat.mul_mod (n ^ k) n m
    have h3 : (n ^ k % m * (n % m)) % m =
        ((n % m) ^ k % m * (n % m)) % m :=
      congrArg (fun t => (t * (n % m)) % m) ih
    have hm :
        ((n % m) ^ k * (n % m)) % m =
          ((n % m) ^ k % m * ((n % m) % m)) % m :=
      Nat.mul_mod ((n % m) ^ k) (n % m) m
    have ha : (n % m) % m = n % m := Nat.mod_mod n m
    have h4 : ((n % m) ^ k % m * (n % m)) % m =
        ((n % m) ^ k * (n % m)) % m :=
      (ha ▸ hm).symm
    have h5 : ((n % m) ^ k * (n % m)) % m =
        (n % m) ^ (k + 1) % m :=
      congrArg (fun t => t % m) hs'.symm
    exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

/-- Every fourth power is `0` or `1 [MOD 16]`. -/
theorem fourth_pow_mod_16 (n : Nat) :
    n ^ 4 % 16 = 0 ∨ n ^ 4 % 16 = 1 :=
  pow_mod_eq n 4 16 ▸
    fourth_pow_of_lt_16 (n % 16) (Nat.mod_lt n (Nat.succ_pos 15))

theorem zero_ne_seven : (0 : Nat) ≠ 7 :=
  fun h => nomatch h

theorem one_ne_seven : (1 : Nat) ≠ 7 :=
  fun h => nomatch h

theorem zero_ne_thirteen : (0 : Nat) ≠ 13 :=
  fun h => nomatch h

theorem one_ne_thirteen : (1 : Nat) ≠ 13 :=
  fun h => nomatch h

theorem fourth_pow_mod_16_ne_7 (A : Nat) : A ^ 4 % 16 ≠ 7 := by
  rcases fourth_pow_mod_16 A with h0 | h1
  · exact fun h => zero_ne_seven (h0.symm.trans h)
  · exact fun h => one_ne_seven (h1.symm.trans h)

theorem fourth_pow_mod_16_ne_13 (A : Nat) : A ^ 4 % 16 ≠ 13 := by
  rcases fourth_pow_mod_16 A with h0 | h1
  · exact fun h => zero_ne_thirteen (h0.symm.trans h)
  · exact fun h => one_ne_thirteen (h1.symm.trans h)

/-- Displayed v8.69–v8.74 pack at `B = 196`.
Not residual isomorphism.  Not Ribet. -/
theorem displayed_modularity_pack_B_196 :
    (∃ f g : Newform, f.level = 26 ∧ g.level = 26 ∧ f ≠ g) ∧
      frey_mod13_irreducible_at 196 ∧
      ((-2 : Int) % 13 ≠ (0 : Int) % 13 ∧
        (-2 : Int) % 13 ≠ (12 : Int) % 13) :=
  ⟨exists_newform_level_26_dim2,
    frey_mod13_irreducible 196 (Or.inl rfl),
    level26_a_eliminated_by_53⟩

/-- Displayed v8.69–v8.74 pack at `B = 1500003`.
Not residual isomorphism.  Not Ribet. -/
theorem displayed_modularity_pack_B_1500003 :
    (∃ f g : Newform, f.level = 26 ∧ g.level = 26 ∧ f ≠ g) ∧
      frey_mod13_irreducible_at 1500003 ∧
      ((24 : Int) % 13 ≠ (21 : Int) % 13 ∧
        (24 : Int) % 13 ≠ (-39 : Int) % 13) :=
  ⟨exists_newform_level_26_dim2,
    frey_mod13_irreducible 1500003 (Or.inr rfl),
    level26_b_eliminated_by_443⟩

theorem pow13_mod_16_196 : 196 ^ 13 % 16 = 0 :=
  (pow_mod_eq 196 13 16).trans rfl

theorem pow13_mod_16_199 : 199 ^ 13 % 16 = 7 :=
  (pow_mod_eq 199 13 16).trans rfl

theorem pow13_mod_16_1500003 : 1500003 ^ 13 % 16 = 3 :=
  (pow_mod_eq 1500003 13 16).trans rfl

theorem pow13_mod_16_1500006 : 1500006 ^ 13 % 16 = 0 :=
  (pow_mod_eq 1500006 13 16).trans rfl

theorem add_mod_16_left_of_right_zero {x y : Nat}
    (hy : y % 16 = 0) : (x + y) % 16 = x % 16 :=
  ((Nat.add_mod x y 16).trans
      (congrArg (fun t => (x % 16 + t) % 16) hy)).trans
    ((congrArg (fun t => t % 16) (Nat.add_zero (x % 16))).trans
      (Nat.mod_mod x 16))

/-- If `(x + 3) % 16 = 0` and `x < 16` then `x = 13`. -/
theorem eq_13_of_add_three_mod_16_eq_zero :
    ∀ x : Nat, x < 16 → (x + 3) % 16 = 0 → x = 13
  | 13, _, _ => rfl
  | 0, _, h => nomatch h
  | 1, _, h => nomatch h
  | 2, _, h => nomatch h
  | 3, _, h => nomatch h
  | 4, _, h => nomatch h
  | 5, _, h => nomatch h
  | 6, _, h => nomatch h
  | 7, _, h => nomatch h
  | 8, _, h => nomatch h
  | 9, _, h => nomatch h
  | 10, _, h => nomatch h
  | 11, _, h => nomatch h
  | 12, _, h => nomatch h
  | 14, _, h => nomatch h
  | 15, _, h => nomatch h
  | n + 16, hx, _ =>
      absurd hx (Nat.not_lt_of_le (Nat.le_add_left 16 n))

/-- Honest gap-3 row `B = 196`, `C = 199`.
`A^4 + 196^13 ≡ 7 [MOD 16]`, but fourth
powers are `0` or `1`.  Not Ribet.
Not `Classical.em`. -/
theorem beal_4_13_13_gap3_B_196_eliminated :
    ¬ ∃ A : Nat, A ^ 4 + 196 ^ 13 = 199 ^ 13 := by
  have _pack := displayed_modularity_pack_B_196
  intro hBeal
  rcases hBeal with ⟨A, hEq⟩
  have hsum : (A ^ 4 + 196 ^ 13) % 16 = 199 ^ 13 % 16 :=
    congrArg (fun t => t % 16) hEq
  have hA : A ^ 4 % 16 = 7 :=
    (add_mod_16_left_of_right_zero (x := A ^ 4) pow13_mod_16_196).symm.trans
      (hsum.trans pow13_mod_16_199)
  exact fourth_pow_mod_16_ne_7 A hA

/-- Honest gap-3 row `B = 1500003`, `C = 1500006`.
`A^4 + 1500003^13 ≡ 13 [MOD 16]`, but
fourth powers are `0` or `1`.  Not Ribet.
Not `Classical.em`. -/
theorem beal_4_13_13_gap3_B_1500003_eliminated :
    ¬ ∃ A : Nat, A ^ 4 + 1500003 ^ 13 = 1500006 ^ 13 := by
  have _pack := displayed_modularity_pack_B_1500003
  intro hBeal
  rcases hBeal with ⟨A, hEq⟩
  have hsum : (A ^ 4 + 1500003 ^ 13) % 16 = 1500006 ^ 13 % 16 :=
    congrArg (fun t => t % 16) hEq
  have hA : A ^ 4 % 16 = 13 := by
    have hadd := Nat.add_mod (A ^ 4) (1500003 ^ 13) 16
    have hcong : (A ^ 4 % 16 + 3) % 16 = 0 :=
      (hadd.trans
          (congrArg (fun t => (A ^ 4 % 16 + t) % 16)
            pow13_mod_16_1500003)).symm.trans
        (hsum.trans pow13_mod_16_1500006)
    exact eq_13_of_add_three_mod_16_eq_zero (A ^ 4 % 16)
      (Nat.mod_lt _ (Nat.succ_pos 15)) hcong
  exact fourth_pow_mod_16_ne_13 A hA

/-- Conjunction of the two honest rows.
Not a Beal `∀`.  The 2M capstone stays
`Classical.em`. -/
theorem beal_4_13_13_gap3_first_honest_rows :
    (¬ ∃ A : Nat, A ^ 4 + 196 ^ 13 = 199 ^ 13) ∧
      (¬ ∃ A : Nat, A ^ 4 + 1500003 ^ 13 = 1500006 ^ 13) :=
  ⟨beal_4_13_13_gap3_B_196_eliminated,
    beal_4_13_13_gap3_B_1500003_eliminated⟩

theorem ExistsNewformLevel2_eq_zero_ne_zero :
    BealLevel26Foundations.Chain.Level2.ExistsNewformLevel2 =
      ((0 : Nat) ≠ 0) :=
  BealLevel26Foundations.Level26_Newforms.ExistsNewformLevel2_eq_zero_ne_zero

#check fourth_pow_mod_16
#check displayed_modularity_pack_B_196
#check displayed_modularity_pack_B_1500003
#check beal_4_13_13_gap3_B_196_eliminated
#check beal_4_13_13_gap3_B_1500003_eliminated
#check beal_4_13_13_gap3_first_honest_rows
#check ExistsNewformLevel2_eq_zero_ne_zero
#print axioms fourth_pow_of_lt_16
#print axioms pow_mod_eq
#print axioms fourth_pow_mod_16
#print axioms displayed_modularity_pack_B_196
#print axioms beal_4_13_13_gap3_B_196_eliminated
#print axioms beal_4_13_13_gap3_B_1500003_eliminated
#print axioms beal_4_13_13_gap3_first_honest_rows
#print axioms ExistsNewformLevel2_eq_zero_ne_zero

end BealLevel26Foundations.BealElim
