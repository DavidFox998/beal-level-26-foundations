/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Root module. Lake's LEAN_PATH puts the relocated kernel's `Beal/`
  prefix first, so `Beal.Matveev.*` cannot be imported from siblings.
  Do **not** import `Beal.Matveev.MatveevThm14General`.
-/
import Mathlib
import BealGenuineV25
import MatveevThreeLogs
import MatveevBugeaud

/-!
# Unconditional v25 mint no-go (`hGen` + `hLLL`)

Successor of `b71eb73` (axiom-relative `baker_bound_gap3_true`).
The minted tag
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`
requires a Mathlib-only close of kernel `baker_bound_gap3` via
`hGen` (Matveev 2000 Thm 1.4 n=2) and `hLLL` (Bugeaud/LLL
reduction). Neither is a theorem in Mathlib 4.12, and the
displayed methods do not force `B ≤ 10⁶`:

* every `C1 ≥ 1` (including `C1_floor`, jet `242`, and `C1 = 1`)
  has `exp(−C1 log A log(B+3)) < B⁴/A⁴` on `B ≥ B0`;
* no scaling `C > 0` yields a Baker–Davenport witness
  `r > 17 + C/B0`; `C/B0 = 10^{24}` vs `‖b₁‖ < 64`;
* a four-factor jet is cubic (`1331` at `0 10 10 10`); Philippon
  is not in Mathlib 4.12.

A vacuous close still needs Darmon–Merel `(4,4,13)` (or FLT 13 /
Ribet-to-32), which stay `def Prop`. The axiom-relative inhabitant
lives in `BealTrueV25`; this module does **not** add that axiom.
`baker_bound_gap3` stays a `def Prop`. 0 sorry.

`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

open Real

namespace BealMatveevBeal.BealUnconditionalV25

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_logs :
    C1_floor = BealMatveevBeal.MatveevThreeLogs.C1_floor := rfl

theorem B0_nat_eq_logs :
    B0_nat = BealMatveevBeal.MatveevThreeLogs.B0_nat := rfl

theorem B0_nat_eq_lll :
    B0_nat = BealMatveevBeal.MatveevLLL.B0_nat := rfl

theorem B0_nat_eq_gv25 :
    B0_nat = BealMatveevBeal.BealGenuineV25.B0_nat := rfl

/-! ## Kernel aliases (stay `def Prop`) -/

def baker_bound_gap3 : Prop :=
  BealMatveevBeal.BealGenuineV25.baker_bound_gap3

def darmon_merel_44_13_no_coprime : Prop :=
  BealMatveevBeal.BealGenuineV25.darmon_merel_44_13_no_coprime

def fermat_last_theorem_thirteen : Prop :=
  BealMatveevBeal.BealGenuineV25.fermat_last_theorem_thirteen

def ribet_level_lowering_to_32 : Prop :=
  BealMatveevBeal.BealGenuineV25.ribet_level_lowering_to_32

def ribet_level_lowering : Prop :=
  BealMatveevBeal.BealGenuineV25.ribet_level_lowering

/-! ## `hGen` / `hLLL` (uninhabited; not in Mathlib 4.12) -/

/-- Matveev 2000 Theorem 1.4, n=2, displayed `C1_floor` exponential
    on a gap-3 solution. Not in Mathlib 4.12. Instantiating it at
    `B ≥ B0` does not beat `B⁴/A⁴`. -/
def hGen : Prop :=
  ∀ A B : ℕ,
    A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
      0 < B →
        |BealMatveevBeal.MatveevLLL.Lambda A B| >
          exp (-(C1_floor : ℝ) * log (A : ℝ) *
            log ((B + 3 : ℕ) : ℝ))

/-- Bugeaud / LLL close: ratio upper bound ⇒ `B ≤ B0`. Same as
    `bugeaud_LLL_reduction_proof`. The displayed lattice does not
    inhabit it (`cfd4794`). -/
def hLLL : Prop :=
  BealMatveevBeal.MatveevBugeaud.bugeaud_LLL_reduction_proof

/-- Composition that would mint unconditional v25. Stays a
    `def Prop`: neither factor is a Mathlib 4.12 theorem, and the
    displayed methods fail on `B ≥ B0`. -/
def baker_bound_gap3_of_hGen_hLLL : Prop :=
  hGen → hLLL → baker_bound_gap3

/-! ## Log-method / LLL / cubic-jet re-exports -/

theorem Lambda3_eq_Lambda (A B : ℕ) :
    BealMatveevBeal.MatveevThreeLogs.Lambda3 A B =
      BealMatveevBeal.MatveevLLL.Lambda A B :=
  BealMatveevBeal.MatveevThreeLogs.Lambda3_eq_Lambda A B

theorem hGen_exp_lt_ratio
    {C1 : ℝ} (hC1 : 1 ≤ C1)
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-C1 * log (A : ℝ) * log ((B + 3 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 := by
  have hB0' : BealMatveevBeal.MatveevThreeLogs.B0_nat ≤ B := by
    simpa [B0_nat_eq_logs] using hB0
  exact BealMatveevBeal.MatveevThreeLogs.baker_bound_gap3_nogo_logs
    hC1 hsol hB hB0'

theorem C1_floor_hGen_loses
    {A B : ℕ} (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    exp (-(C1_floor : ℝ) * log (A : ℝ) * log ((B + 3 : ℕ) : ℝ)) <
      (B : ℝ) ^ 4 / (A : ℝ) ^ 4 :=
  hGen_exp_lt_ratio
    (le_of_lt (by
      simpa [C1_floor_eq_logs] using
        BealMatveevBeal.MatveevThreeLogs.C1_floor_gt_one))
    hsol hB hB0

theorem hLLL_method_fails :
    ∀ C : ℝ, 0 < C →
      ∀ A B : ℕ,
        A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
          0 < B →
            B0_nat ≤ B →
              ¬ ∃ r : ℝ,
                17 + C / (B0_nat : ℝ) < r ∧
                  r ≤ |BealMatveevBeal.MatveevLLL.floorFormThird C A B| := by
  intro C hC A B hsol hB hB0
  have hB0' : BealMatveevBeal.MatveevLLL.B0_nat ≤ B := by
    simpa [B0_nat_eq_lll] using hB0
  simpa [B0_nat_eq_lll] using
    BealMatveevBeal.MatveevBugeaud.bugeaud_LLL_method_fails
      C hC A B hsol hB hB0'

theorem no_uniform_c_cubic_in_N :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 N3 : ℕ,
        (BealMatveevBeal.MatveevThreeLogs.coeffCount3 L N1 N2 N3 : ℝ) ≤
          c * (L + 1 : ℝ) *
            ((N1 + 1 : ℝ) + (N2 + 1 : ℝ) + (N3 + 1 : ℝ)) :=
  BealMatveevBeal.MatveevThreeLogs.no_uniform_c_cubic_in_N

theorem coeffCount3_zero_ten_ten_ten :
    BealMatveevBeal.MatveevThreeLogs.coeffCount3 0 10 10 10 = 1331 :=
  BealMatveevBeal.MatveevThreeLogs.coeffCount3_zero_ten_ten_ten

/-! ## Combined unconditional no-go -/

/-- Even assuming the *shape* of `hGen` and `hLLL`, the displayed
    Baker / LLL methods lose on `B ≥ B0`, and a remaining solution
    is coprime with residual ≠ 32 and `A > B0`. Darmon–Merel
    `(4,4,13)`, FLT 13, and Ribet-to-32 stay `def Prop`, so
    `baker_bound_gap3` stays uninhabited as a named theorem. -/
theorem baker_bound_gap3_unconditional_nogo {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hB : 0 < B) (hB0 : B0_nat ≤ B) :
    (∀ C1 : ℝ, 1 ≤ C1 →
      exp (-C1 * log (A : ℝ) * log ((B + 3 : ℕ) : ℝ)) <
        (B : ℝ) ^ 4 / (A : ℝ) ^ 4) ∧
    (∀ C : ℝ, 0 < C →
      ¬ ∃ r : ℝ,
        17 + C / (B0_nat : ℝ) < r ∧
          r ≤ |BealMatveevBeal.MatveevLLL.floorFormThird C A B|) ∧
    ¬ 3 ∣ B ∧
      Nat.Coprime A B ∧
      BealMatveevBeal.BealKraus.residualLevelEstimate A B ≠ 32 ∧
      B0_nat < A ∧
      ¬ 13 ∣ 8 ∧ 13 ∣ 26 ∧
      (darmon_merel_44_13_no_coprime → False) := by
  have hB0gv : BealMatveevBeal.BealGenuineV25.B0_nat ≤ B := by
    simpa [B0_nat_eq_gv25] using hB0
  have hnogo :=
    BealMatveevBeal.BealGenuineV25.baker_bound_gap3_darmon_merel_4413_3adic_nogo
      hsol hB hB0gv
  obtain ⟨hnot3, hcop, hres, hA, h13⟩ := hnogo
  obtain ⟨h138, hrest⟩ := h13
  obtain ⟨h1326, hDM⟩ := hrest
  refine ⟨?_, ?_, hnot3, hcop, hres, ?_, h138, h1326, ?_⟩
  · intro C1 hC1
    exact hGen_exp_lt_ratio hC1 hsol hB hB0
  · intro C hC
    exact hLLL_method_fails C hC A B hsol hB hB0
  · simpa [B0_nat_eq_gv25] using hA
  · intro hDM'
    exact hDM hDM'

#check C1_floor_eq
#check B0_nat_eq
#check hGen
#check hLLL
#check baker_bound_gap3_of_hGen_hLLL
#check Lambda3_eq_Lambda
#check hGen_exp_lt_ratio
#check C1_floor_hGen_loses
#check hLLL_method_fails
#check no_uniform_c_cubic_in_N
#check coeffCount3_zero_ten_ten_ten
#check baker_bound_gap3_unconditional_nogo
#check baker_bound_gap3
#check darmon_merel_44_13_no_coprime
#check fermat_last_theorem_thirteen
#check ribet_level_lowering_to_32
#print axioms Lambda3_eq_Lambda
#print axioms hGen_exp_lt_ratio
#print axioms C1_floor_hGen_loses
#print axioms hLLL_method_fails
#print axioms no_uniform_c_cubic_in_N
#print axioms baker_bound_gap3_unconditional_nogo

end BealMatveevBeal.BealUnconditionalV25
