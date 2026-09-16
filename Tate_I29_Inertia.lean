/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Separate Lake target `BealMatveevBealV25B0Search`.
  Do **not** add `Beal/Matveev/Tate_I29_Inertia.lean`:
  `.submodules Beal.Matveev` would pull it into the default glob.
  Do **not** import `Beal.Matveev.MatveevThm14General` or
  `BealTrueV25`. Do **not** add a Tate/inertia axiom: the only
  Darmon–Merel axiom remains
  `BealTrueV25.darmon_merel_4413_axiom` on the default target.
-/
import BealMatveevBealV25B0Search
import DarmonMerelFrey4413
import Level928Table
import MazurIrreducibility13
import Inertia29Unramified
import TateGalois
import LLLTargetB8_C1_lower_bound

/-!
# Gap 2: Tate `I₂₉` inertia stays `def Prop`

Numerics from `9030063` / `TateGalois`: `v₂₉(c₄)=0`,
`v₂₉(Δ)=26k`. Mathlib 4.12 **does** have the field `ℚ_[p]`
(`Padic p`) and `Padic.valuation : ℚ_[p] → ℤ`. This file
inhabits `v₂₉(Δ)` as that field valuation, and the existence
of a unit of the same valuation (`Δ` itself). That is **not**
Tate uniformization `E(ℚ̄_p) ≅ ℚ̄_pˣ / q^ℤ`. No
`InertiaGroup`, no `axiom inertia_via_cyclo`.

A Mathlib Tate-curve module (Loeffler / Vonk direction) would
unblock this gap and the unramified-at-`29` half of Ribet.
Wiles / BCDT is a separate gap.

Does **not** mint v25. 0 sorry. 0 new axioms.
`C1_floor = 143186215390`. `B0_nat = 1000000`.
Tag `v24-v24x-final-rank3-shape-nogo` stays at `c1d173e`.
-/

namespace BealMatveevBeal.Tate_I29_Inertia

open BealMatveevBeal.BealMatveevBealV25B0Search
open BealMatveevBeal.DarmonMerelFrey4413
open BealMatveevBeal.Level928Table
open BealMatveevBeal.MazurIrreducibility13
open BealMatveevBeal.Inertia29Unramified
open BealMatveevBeal.TateGalois
open BealMatveevBeal.LLLTargetB8
open BealMatveevBeal.LLLTargetB8C1LowerBound
open Nat

instance : Fact (Nat.Prime 29) := ⟨twenty_nine_prime⟩

theorem v29_c4_eq_0_thm {A B : ℕ}
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    padicValInt 29 (frey_c4 A B) = 0 :=
  v29_c4_zero_when_29_nmid_AB hA hB

theorem v29_Delta_26k_thm {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    padicValNat 29 (freyDiscNat A B) =
      26 * padicValNat 29 (B + 3) :=
  v29_Delta_eq_26_vC hsol hBpos hA hB

/-! ## `ℚ_[29]` field valuation of the displayed discriminant -/

noncomputable section

/-- Mathlib 4.12 already has this field. It is **not** a Tate
    curve and not `ℚ̄_p`. -/
abbrev Qp (p : ℕ) [Fact p.Prime] := ℚ_[p]

/-- Displayed `Δ` as an element of `ℚ_[29]`. -/
def freyDisc_in_Qp29 (A B : ℕ) : ℚ_[29] :=
  (freyDiscNat A B : ℚ_[29])

theorem freyDisc_in_Qp29_ne_zero {A B : ℕ} (hA : A ≠ 0) (hB : B ≠ 0) :
    freyDisc_in_Qp29 A B ≠ 0 :=
  Nat.cast_ne_zero.mpr (freyDiscNat_pos hA hB).ne'

/-- `Padic.valuation` on a nonzero rational agrees with
    `padicValRat`. -/
theorem valuation_coe_rat {q : ℚ} (hq : q ≠ 0) :
    Padic.valuation (q : ℚ_[29]) = padicValRat 29 q := by
  have hx : (q : ℚ_[29]) ≠ 0 := Rat.cast_ne_zero.mpr hq
  have hp_pos : (0 : ℝ) < 29 := by norm_num
  have hp_ne : (29 : ℝ) ≠ 1 := by norm_num
  have hnorm : ‖(q : ℚ_[29])‖ = (padicNorm 29 q : ℝ) :=
    padicNormE.eq_padicNorm q
  have hpow : padicNorm 29 q = (29 : ℚ) ^ (-padicValRat 29 q) :=
    padicNorm.eq_zpow_of_nonzero hq
  have hcast :
      Rat.cast ((29 : ℚ) ^ (-padicValRat 29 q)) =
        (29 : ℝ) ^ (-padicValRat 29 q) :=
    map_zpow₀ (Rat.castHom ℝ) (29 : ℚ) (-padicValRat 29 q)
  have hL : (29 : ℝ) ^ (-Padic.valuation (q : ℚ_[29])) = ‖(q : ℚ_[29])‖ := by
    have := Padic.norm_eq_pow_val hx
    exact_mod_cast this.symm
  have hR : (29 : ℝ) ^ (-padicValRat 29 q) = ‖(q : ℚ_[29])‖ := by
    rw [hnorm, hpow]
    exact hcast.symm
  exact neg_injective ((zpow_inj hp_pos hp_ne).mp (hL.trans hR.symm))

theorem valuation_natCast_eq_padicValNat {n : ℕ} (hn : n ≠ 0) :
    Padic.valuation (n : ℚ_[29]) = (padicValNat 29 n : ℤ) := by
  have hq : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  have hcast : ((n : ℚ) : ℚ_[29]) = (n : ℚ_[29]) := by
    simp
  have hrat := valuation_coe_rat hq
  rw [hcast] at hrat
  simpa [padicValRat.of_nat] using hrat

theorem padic_valuation_Delta_eq_padicValNat {A B : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    Padic.valuation (freyDisc_in_Qp29 A B) =
      (padicValNat 29 (freyDiscNat A B) : ℤ) :=
  valuation_natCast_eq_padicValNat (freyDiscNat_pos hA hB).ne'

/-- On a solution with `29 ∤ AB`, the field valuation of `Δ` is
    `26 v₂₉(C)`. This is still not a Tate parameter. -/
theorem padic_valuation_Delta_eq_26_vC {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) :
    Padic.valuation (freyDisc_in_Qp29 A B) =
      26 * (padicValNat 29 (B + 3) : ℤ) := by
  have hApos : A ≠ 0 := A_ne_zero_of_sol hBpos hsol
  have hBne : B ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.succ_le_iff.mp hBpos)
  have hval := padic_valuation_Delta_eq_padicValNat hApos hBne
  have hnat := v29_Delta_26k_thm hsol hBpos hA hB
  rw [hval, hnat]
  norm_cast

theorem thirteen_dvd_padic_valuation_Delta {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (_hC : 29 ∣ B + 3) :
    (13 : ℤ) ∣ Padic.valuation (freyDisc_in_Qp29 A B) := by
  rw [padic_valuation_Delta_eq_26_vC hsol hBpos hA hB]
  exact dvd_mul_of_dvd_left (by decide : (13 : ℤ) ∣ 26) _

/-- A unit of `ℚ_[29]` with the same valuation as `Δ`: `Δ`
    itself. This is **not** the Tate parameter `q(E)`. -/
theorem exists_Qp_unit_val_eq_vDelta {A B : ℕ}
    (hA : A ≠ 0) (hB : B ≠ 0) :
    ∃ q : (ℚ_[29])ˣ,
      Padic.valuation (q : ℚ_[29]) =
        Padic.valuation (freyDisc_in_Qp29 A B) :=
  ⟨Units.mk0 _ (freyDisc_in_Qp29_ne_zero hA hB), by simp⟩

/-! ## Tate uniformization stays `def Prop` (no Galois module) -/

/-- Intended Mathlib object: Tate uniformisation
    `E(ℚ̄_ℓ) ≅ ℚ̄_ℓˣ / q^ℤ` with `v_ℓ(q)=v_ℓ(Δ)`.
    Existence of *some* unit of valuation `v(Δ)` is the theorem
    `exists_Qp_unit_val_eq_vDelta`. The missing object is the
    functor from the curve to that `q`. **Not** an axiom. -/
def Tate_uniformization : Prop :=
  tate_curve_at_29

/-- Missing: a Tate parameter `q ∈ ℚ_[p]ˣ` attached to the
    displayed Frey curve, not an arbitrary unit of the same
    valuation. Uninhabited. Mathlib contribution target:
    Tate uniformization over `ℚ_p` (Loeffler / Vonk direction). -/
def Tate_q : Prop :=
  Tate_uniformization

/-- Inertia via `χ_cyc^{v(q)}`. Uninhabited. **Not** an axiom. -/
def inertia_via_cyclo : Prop :=
  inertia_via_cyclotomic

/-- `13 ∣ v₂₉(Δ)` ⇒ `ρ_{E,13}(I_{29})=1`. Uninhabited. The
    integer `13 ∣ Padic.valuation Δ` is a theorem above; the
    Galois action is not. -/
def inertia_trivial_mod13_when_13_dvd_v : Prop :=
  inertia_at_29_trivial_mod13_full

theorem LLL_nogo_persists_after_Tate_I29 :
    LLL_reduces_C1_to_lt_nine ↔
      ∀ {A B : ℕ}, B0_nat ≤ B → A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13 :=
  LLL_reduces_C1_to_lt_nine_iff_no_sol_ge_B0

#check v29_c4_eq_0_thm
#check v29_Delta_26k_thm
#check valuation_natCast_eq_padicValNat
#check padic_valuation_Delta_eq_26_vC
#check thirteen_dvd_padic_valuation_Delta
#check exists_Qp_unit_val_eq_vDelta
#check Tate_q
#check Tate_uniformization
#check inertia_trivial_mod13_when_13_dvd_v
#print axioms v29_c4_eq_0_thm
#print axioms padic_valuation_Delta_eq_26_vC
#print axioms exists_Qp_unit_val_eq_vDelta
#print axioms LLL_nogo_persists_after_Tate_I29

end

end BealMatveevBeal.Tate_I29_Inertia
