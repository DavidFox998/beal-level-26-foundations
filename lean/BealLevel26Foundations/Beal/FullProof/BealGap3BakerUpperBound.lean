/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under MIT license as described in the file LICENSE.
Authors: David Fox

Track B v9.3.0 -- Baker-conditional gap-3 forall.

`baker_bound_gap3` stays the uninhabited
Bugeaud / linear-forms Prop (external,
not in Mathlib 4.12).  `baker_B0 = 10^6`.

`baker_conditional_gap3_full` inhabits
  baker_bound_gap3 -> forall B, no A
  with A^4 + B^4 = (B+3)^13.

B <= B0 is the existing residue cover,
extended to 10^6:
* B % 16 != 14 via beal_gap3_mod16_elim_not14
  (the 15/16 class, including the named
  rows 196 and 1500003).
* B == 14 via the 352-pattern fourth-power
  tests at q = 53, 29, 109, expanded by
  q = 17, 5, 7, 11, 13, 19, 23, 31, 37.
  Kernel-checked on the 62500 values
  14, 30, ..., 999998.

B > B0 uses the Baker premise.

Keeps baker_bound_gap3 Prop, the three
Zsig Props, frey_tate_conductor Prop,
conductor_86 Prop, B14_honest Prop.
Does not import RibetMazur, BealFreyB14,
or FreyModularity_13.  Not BCDT.
Does not use sorry.
-/

import BealLevel26Foundations.Beal.FullProof.BealMod16

namespace BealLevel26Foundations.BealGap3BakerUpperBound

open BealLevel26Foundations.BealMod16

/-! ## Displayed Baker cutoff B0 = 10^6 -/

/-- Named cutoff in the requested Baker shape.
    Displayed Nat, not an effective bound. -/
def baker_B0 : Nat := 1000000

theorem baker_B0_eq : baker_B0 = 1000000 :=
  rfl

theorem baker_B0_eq_pow10_6 : baker_B0 = Nat.pow 10 6 :=
  rfl

/-! ## Missing effective bound (uninhabited) -/

/-- Missing Baker / Bugeaud linear-forms-in-logs
    bound: exists B0 = 10^6 such that every B > B0
    has no gap-3 solution.  Uninhabited Prop.
    Bugeaud linear forms external, not in
    Mathlib 4.12.  Not closable from the 5983
    census.  `sorry` is not used. -/
def baker_bound_gap3 : Prop :=
  ∃ B0 : Nat, B0 = Nat.pow 10 6 ∧
    ∀ B : Nat, B0 < B →
      ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13

/-- Same statement at the displayed numeral. -/
def baker_bound_gap3_at_B0 : Prop :=
  ∀ B : Nat, baker_B0 < B →
    ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13

/-! ## Fourth-power obstruction modulo q -/

def rhsMod (q B : Nat) : Nat :=
  (Nat.pow ((B + 3) % q) 13 % q + q - Nat.pow (B % q) 4 % q) % q

def isFourthGo (q r : Nat) : Nat → Bool
  | 0 => Nat.beq (Nat.pow 0 4 % q) (r % q)
  | n + 1 =>
    Nat.beq (Nat.pow (n + 1) 4 % q) (r % q) || isFourthGo q r n

def isFourthMod (q r : Nat) : Bool :=
  isFourthGo q r (q - 1)

def killedBy (q B : Nat) : Bool :=
  !(isFourthMod q (rhsMod q B))

def killedB14 (B : Nat) : Bool :=
  killedBy 53 B || killedBy 29 B || killedBy 109 B || killedBy 17 B ||
    killedBy 5 B || killedBy 7 B || killedBy 11 B || killedBy 13 B ||
    killedBy 19 B || killedBy 23 B || killedBy 31 B || killedBy 37 B

theorem beq_self : ∀ n : Nat, Nat.beq n n = true
  | 0 => rfl
  | n + 1 => beq_self n

theorem ne_of_beq_false {n m : Nat} (h : Nat.beq n m = false) : n ≠ m :=
  fun heq =>
    let htrue : Nat.beq n n = true := beq_self n
    let hfalse : Nat.beq n n = false := heq ▸ h
    Bool.noConfusion (htrue.symm.trans hfalse)

theorem or_eq_false {a b : Bool} (h : (a || b) = false) :
    a = false ∧ b = false :=
  match a, b, h with
  | false, false, _ => ⟨rfl, rfl⟩
  | true, false, h => nomatch h
  | false, true, h => nomatch h
  | true, true, h => nomatch h

theorem isFourthGo_false {q r : Nat} :
    ∀ n : Nat, isFourthGo q r n = false →
      ∀ a : Nat, a ≤ n → Nat.pow a 4 % q ≠ r % q
  | 0, hf, a, ha =>
    let ha0 : a = 0 := Nat.eq_zero_of_le_zero ha
    ne_of_beq_false (by
      rw [ha0]
      simpa [isFourthGo] using hf)
  | n + 1, hf, a, ha =>
    let hpair := or_eq_false hf
    if hlt : a < n + 1 then
      isFourthGo_false n hpair.right a (Nat.lt_succ_iff.mp hlt)
    else
      let heq : a = n + 1 :=
        Nat.le_antisymm ha (Nat.not_lt.mp hlt)
      heq ▸ ne_of_beq_false hpair.left

theorem pow_mod (a n q : Nat) (_hq : 0 < q) :
    Nat.pow a n % q = Nat.pow (a % q) n % q := by
  induction n with
  | zero =>
    simp [Nat.pow]
  | succ n ih =>
    have hpow : Nat.pow a (n + 1) = Nat.pow a n * a := rfl
    have hpow' : Nat.pow (a % q) (n + 1) = Nat.pow (a % q) n * (a % q) :=
      rfl
    rw [hpow, hpow', Nat.mul_mod, ih]
    have hR :
        (Nat.pow (a % q) n * (a % q)) % q =
          (Nat.pow (a % q) n % q * ((a % q) % q)) % q :=
      Nat.mul_mod _ _ q
    rw [hR, Nat.mod_mod]

theorem add_sub_cancel_right (n : Nat) : ∀ k : Nat, n + k - k = n
  | 0 => rfl
  | k + 1 =>
    (Nat.succ_sub_succ (n + k) k).trans (add_sub_cancel_right n k)

theorem sub_add_cancel_of_le {n q : Nat} (h : q ≤ n) : n - q + q = n :=
  Nat.sub_add_cancel h

theorem residue_sub (a b c q : Nat)
    (hq : 1 < q) (ha : a < q) (hb : b < q) (_hc : c < q)
    (h : (a + b) % q = c) :
    a = (c + q - b) % q := by
  have hq0 : 0 < q := Nat.lt_trans (by decide : (0 : Nat) < 1) hq
  have hab2 : a + b < q + q := Nat.add_lt_add ha hb
  cases' Nat.decLe q (a + b) with hnot hle
  · have hlt : a + b < q := Nat.not_le.mp hnot
    have hab : a + b = c := (Nat.mod_eq_of_lt hlt).symm.trans h
    have hsum : c + q - b = a + q := by
      have h1 : c + q - b = a + b + q - b :=
        congrArg (fun t => t + q - b) hab.symm
      have h2 : a + b + q = a + q + b := by
        rw [Nat.add_assoc, Nat.add_comm b q, Nat.add_assoc]
      have h3 : a + q + b - b = a + q := add_sub_cancel_right (a + q) b
      exact h1.trans ((congrArg (fun t => t - b) h2).trans h3)
    have hmod : (c + q - b) % q = a := by
      rw [hsum, Nat.add_mod, Nat.mod_self, Nat.add_zero,
        Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha]
    exact hmod.symm
  · have hsublt : a + b - q < q :=
      Nat.lt_of_add_lt_add_right
        (Eq.subst (motive := fun t => t < q + q)
          (sub_add_cancel_of_le hle).symm hab2)
    have hmod : (a + b) % q = a + b - q := by
      have hcond : 0 < q ∧ q ≤ a + b := ⟨hq0, hle⟩
      have : (a + b) % q =
          if 0 < q ∧ q ≤ a + b then (a + b - q) % q else a + b :=
        Nat.mod_eq (a + b) q
      rw [this, if_pos hcond, Nat.mod_eq_of_lt hsublt]
    have hc' : a + b - q = c := hmod.symm.trans h
    have hsum : c + q - b = a := by
      have h1 : c + q - b = a + b - q + q - b :=
        congrArg (fun t => t + q - b) hc'.symm
      have h2 : a + b - q + q = a + b := sub_add_cancel_of_le hle
      have h3 : a + b - b = a := add_sub_cancel_right a b
      exact h1.trans ((congrArg (fun t => t - b) h2).trans h3)
    have hmod2 : (c + q - b) % q = a := by
      rw [hsum, Nat.mod_eq_of_lt ha]
    exact hmod2.symm

theorem beal_implies_fourth_eq_rhs {A B q : Nat}
    (hq : 1 < q)
    (h : Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13) :
    Nat.pow A 4 % q = rhsMod q B := by
  have hq0 : 0 < q := Nat.lt_trans (by decide : (0 : Nat) < 1) hq
  have hsum : (Nat.pow A 4 + Nat.pow B 4) % q =
      Nat.pow (B + 3) 13 % q :=
    congrArg (fun n => n % q) h
  have hadd : (Nat.pow A 4 % q + Nat.pow B 4 % q) % q =
      Nat.pow (B + 3) 13 % q :=
    (Nat.add_mod (Nat.pow A 4) (Nat.pow B 4) q).symm.trans hsum
  have hrhs : rhsMod q B =
      (Nat.pow (B + 3) 13 % q + q - Nat.pow B 4 % q) % q := by
    unfold rhsMod
    rw [pow_mod (B + 3) 13 q hq0, pow_mod B 4 q hq0]
  rw [hrhs]
  exact residue_sub (Nat.pow A 4 % q) (Nat.pow B 4 % q)
    (Nat.pow (B + 3) 13 % q) q hq
    (Nat.mod_lt _ hq0) (Nat.mod_lt _ hq0) (Nat.mod_lt _ hq0) hadd

theorem of_killedBy {q B : Nat} (hq : 1 < q)
    (h : killedBy q B = true) :
    ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := by
  intro ⟨A, hEq⟩
  have hq0 : 0 < q := Nat.lt_trans (by decide : (0 : Nat) < 1) hq
  have hf : isFourthMod q (rhsMod q B) = false := by
    cases hb : isFourthMod q (rhsMod q B)
    · rfl
    · have hfalse : killedBy q B = false := by
        simp [killedBy, hb]
      exact nomatch (hfalse.symm.trans h)
  have hgo : isFourthGo q (rhsMod q B) (q - 1) = false := hf
  have ha : Nat.pow A 4 % q = rhsMod q B :=
    beal_implies_fourth_eq_rhs hq hEq
  have hpow : Nat.pow A 4 % q = Nat.pow (A % q) 4 % q :=
    pow_mod A 4 q hq0
  have hle : A % q ≤ q - 1 := by
    have hlt : A % q < q := Nat.mod_lt A hq0
    exact Nat.le_pred_of_lt hlt
  have hne : Nat.pow (A % q) 4 % q ≠ rhsMod q B % q :=
    isFourthGo_false (q - 1) hgo (A % q) hle
  have hr : rhsMod q B % q = rhsMod q B := by
    unfold rhsMod
    exact Nat.mod_mod _ q
  exact hne (hpow.symm.trans (ha.trans hr.symm))


theorem not_exists_of_killedB14 (B : Nat) (h : killedB14 B = true) :
    ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := by
  cases h53 : killedBy 53 B
  · cases h29 : killedBy 29 B
    · cases h109 : killedBy 109 B
      · cases h17 : killedBy 17 B
        · cases h5 : killedBy 5 B
          · cases h7 : killedBy 7 B
            · cases h11 : killedBy 11 B
              · cases h13 : killedBy 13 B
                · cases h19 : killedBy 19 B
                  · cases h23 : killedBy 23 B
                    · cases h31 : killedBy 31 B
                      · cases h37 : killedBy 37 B
                        · simp [killedB14, h53, h29, h109, h17, h5, h7,
                            h11, h13, h19, h23, h31, h37] at h
                        · exact of_killedBy (by decide : 1 < 37) h37
                      · exact of_killedBy (by decide : 1 < 31) h31
                    · exact of_killedBy (by decide : 1 < 23) h23
                  · exact of_killedBy (by decide : 1 < 19) h19
                · exact of_killedBy (by decide : 1 < 13) h13
              · exact of_killedBy (by decide : 1 < 11) h11
            · exact of_killedBy (by decide : 1 < 7) h7
          · exact of_killedBy (by decide : 1 < 5) h5
        · exact of_killedBy (by decide : 1 < 17) h17
      · exact of_killedBy (by decide : 1 < 109) h109
    · exact of_killedBy (by decide : 1 < 29) h29
  · exact of_killedBy (by decide : 1 < 53) h53

/-! ## Kernel census of B == 14, B <= 10^6 -/

def allKilledRange (start : Nat) : Nat → Bool
  | 0 => true
  | n + 1 =>
    killedB14 (14 + 16 * (start + n)) && allKilledRange start n

theorem allKilledRange_spec (start : Nat) :
    ∀ n : Nat, allKilledRange start n = true →
      ∀ i : Nat, i < n → killedB14 (14 + 16 * (start + i)) = true
  | 0, _, i, hi => nomatch hi
  | n + 1, hf, i, hi =>
    let hpair : killedB14 (14 + 16 * (start + n)) = true ∧
        allKilledRange start n = true := by
      cases ha : killedB14 (14 + 16 * (start + n))
      · have hfalse : allKilledRange start (n + 1) = false := by
          simp [allKilledRange, ha]
        exact nomatch (hfalse.symm.trans hf)
      · cases hb : allKilledRange start n
        · have hfalse : allKilledRange start (n + 1) = false := by
            simp [allKilledRange, ha, hb]
          exact nomatch (hfalse.symm.trans hf)
        · exact ⟨rfl, rfl⟩
    if hlt : i < n then
      allKilledRange_spec start n hpair.right i hlt
    else
      let heq : i = n :=
        Nat.le_antisymm (Nat.lt_succ_iff.mp hi) (Nat.not_lt.mp hlt)
      heq ▸ hpair.left

set_option maxRecDepth 200000
set_option maxHeartbeats 4000000000

theorem allKilledRange_chunk_0 :
    allKilledRange 0 2500 = true :=
  rfl

theorem allKilledRange_chunk_1 :
    allKilledRange 2500 2500 = true :=
  rfl

theorem allKilledRange_chunk_2 :
    allKilledRange 5000 2500 = true :=
  rfl

theorem allKilledRange_chunk_3 :
    allKilledRange 7500 2500 = true :=
  rfl

theorem allKilledRange_chunk_4 :
    allKilledRange 10000 2500 = true :=
  rfl

theorem allKilledRange_chunk_5 :
    allKilledRange 12500 2500 = true :=
  rfl

theorem allKilledRange_chunk_6 :
    allKilledRange 15000 2500 = true :=
  rfl

theorem allKilledRange_chunk_7 :
    allKilledRange 17500 2500 = true :=
  rfl

theorem allKilledRange_chunk_8 :
    allKilledRange 20000 2500 = true :=
  rfl

theorem allKilledRange_chunk_9 :
    allKilledRange 22500 2500 = true :=
  rfl

theorem allKilledRange_chunk_10 :
    allKilledRange 25000 2500 = true :=
  rfl

theorem allKilledRange_chunk_11 :
    allKilledRange 27500 2500 = true :=
  rfl

theorem allKilledRange_chunk_12 :
    allKilledRange 30000 2500 = true :=
  rfl

theorem allKilledRange_chunk_13 :
    allKilledRange 32500 2500 = true :=
  rfl

theorem allKilledRange_chunk_14 :
    allKilledRange 35000 2500 = true :=
  rfl

theorem allKilledRange_chunk_15 :
    allKilledRange 37500 2500 = true :=
  rfl

theorem allKilledRange_chunk_16 :
    allKilledRange 40000 2500 = true :=
  rfl

theorem allKilledRange_chunk_17 :
    allKilledRange 42500 2500 = true :=
  rfl

theorem allKilledRange_chunk_18 :
    allKilledRange 45000 2500 = true :=
  rfl

theorem allKilledRange_chunk_19 :
    allKilledRange 47500 2500 = true :=
  rfl

theorem allKilledRange_chunk_20 :
    allKilledRange 50000 2500 = true :=
  rfl

theorem allKilledRange_chunk_21 :
    allKilledRange 52500 2500 = true :=
  rfl

theorem allKilledRange_chunk_22 :
    allKilledRange 55000 2500 = true :=
  rfl

theorem allKilledRange_chunk_23 :
    allKilledRange 57500 2500 = true :=
  rfl

theorem allKilledRange_chunk_24 :
    allKilledRange 60000 2500 = true :=
  rfl

theorem chunk_of_quot :
    ∀ i : Nat, i < 25 → allKilledRange (i * 2500) 2500 = true
  | 0, _ => allKilledRange_chunk_0
  | 1, _ => allKilledRange_chunk_1
  | 2, _ => allKilledRange_chunk_2
  | 3, _ => allKilledRange_chunk_3
  | 4, _ => allKilledRange_chunk_4
  | 5, _ => allKilledRange_chunk_5
  | 6, _ => allKilledRange_chunk_6
  | 7, _ => allKilledRange_chunk_7
  | 8, _ => allKilledRange_chunk_8
  | 9, _ => allKilledRange_chunk_9
  | 10, _ => allKilledRange_chunk_10
  | 11, _ => allKilledRange_chunk_11
  | 12, _ => allKilledRange_chunk_12
  | 13, _ => allKilledRange_chunk_13
  | 14, _ => allKilledRange_chunk_14
  | 15, _ => allKilledRange_chunk_15
  | 16, _ => allKilledRange_chunk_16
  | 17, _ => allKilledRange_chunk_17
  | 18, _ => allKilledRange_chunk_18
  | 19, _ => allKilledRange_chunk_19
  | 20, _ => allKilledRange_chunk_20
  | 21, _ => allKilledRange_chunk_21
  | 22, _ => allKilledRange_chunk_22
  | 23, _ => allKilledRange_chunk_23
  | 24, _ => allKilledRange_chunk_24
  | n + 25, hi =>
    nomatch (Nat.not_lt.mpr (Nat.le_add_left 25 n) hi)

theorem killed_of_k_lt_62500 (k : Nat) (hk : k < 62500) :
    killedB14 (14 + 16 * k) = true := by
  have hdecomp : k = 2500 * (k / 2500) + k % 2500 :=
    (Nat.div_add_mod k 2500).symm
  have hq : k / 2500 < 25 := by
    have _hle : 2500 * (k / 2500) ≤ k := Nat.mul_div_le k 2500
    omega
  have hr : k % 2500 < 2500 := Nat.mod_lt k (by decide)
  have hchunk : allKilledRange (2500 * (k / 2500)) 2500 = true := by
    have : 2500 * (k / 2500) = (k / 2500) * 2500 := Nat.mul_comm _ _
    rw [this]
    exact chunk_of_quot (k / 2500) hq
  have hkill :
      killedB14 (14 + 16 * (2500 * (k / 2500) + k % 2500)) = true :=
    allKilledRange_spec (2500 * (k / 2500)) 2500 hchunk (k % 2500) hr
  rw [hdecomp]
  exact hkill

theorem exists_k_of_mod16_14 {B : Nat} (h14 : B % 16 = 14) :
    ∃ k : Nat, B = 14 + 16 * k :=
  ⟨B / 16, by
    have hmod : 16 * (B / 16) + B % 16 = B := Nat.div_add_mod B 16
    rw [h14] at hmod
    have : 16 * (B / 16) + 14 = 14 + 16 * (B / 16) := by
      rw [Nat.add_comm]
    exact hmod.symm.trans this⟩

theorem k_lt_62500_of_le_B0 {B k : Nat}
    (hB : B = 14 + 16 * k) (hle : B ≤ baker_B0) :
    k < 62500 := by
  rw [baker_B0_eq, hB] at hle
  omega

theorem baker_le_B0_gap3 {B : Nat} (hle : B ≤ baker_B0) :
    ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := by
  by_cases h14 : B % 16 = 14
  · rcases exists_k_of_mod16_14 h14 with ⟨k, hk⟩
    have hklt : k < 62500 := k_lt_62500_of_le_B0 hk hle
    have hb : killedB14 B = true := by
      rw [hk]
      exact killed_of_k_lt_62500 k hklt
    exact not_exists_of_killedB14 B hb
  · intro hEx
    rcases hEx with ⟨A, hEq⟩
    exact beal_gap3_mod16_elim_not14 B A h14 hEq

theorem baker_bound_gap3_implies_at_B0
    (h : baker_bound_gap3) : baker_bound_gap3_at_B0 := by
  rcases h with ⟨B0, hEq, hLarge⟩
  intro B hlt
  have hlt' : B0 < B := by
    rw [hEq, ← baker_B0_eq_pow10_6]
    exact hlt
  exact hLarge B hlt'

/-- Conditional gap-3 forall.  B <= B0 by the
    expanded residue cover; B > B0 by the
    Baker / Bugeaud premise.  Not an
    unconditional Beal forall. -/
theorem baker_conditional_gap3_full
    (hBaker : baker_bound_gap3) :
    ∀ B : Nat,
      ¬ ∃ A, Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 := by
  intro B
  by_cases hgt : baker_B0 < B
  · exact baker_bound_gap3_implies_at_B0 hBaker B hgt
  · exact baker_le_B0_gap3 (Nat.not_lt.mp hgt)

#check baker_B0
#check baker_B0_eq
#check baker_B0_eq_pow10_6
#check baker_bound_gap3
#check baker_bound_gap3_at_B0
#check baker_le_B0_gap3
#check baker_conditional_gap3_full
#print axioms baker_B0_eq
#print axioms baker_B0_eq_pow10_6
#print axioms baker_le_B0_gap3
#print axioms baker_conditional_gap3_full

end BealLevel26Foundations.BealGap3BakerUpperBound
