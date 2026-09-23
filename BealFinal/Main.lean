/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RequiresTateMazurRibetFor32.ForwardDoc
import BealMatveevBealV25B0Search

/-!
# Final forward Beal interface

This module records the end-of-proof dependency order without turning any
displayed numeral into geometric, Galois, automorphic, analytic, search, or
general Diophantine evidence.

The completed Tate--Mazur--Ribet--Kolyvagin--Conditional-32--Requires table is
retained exactly. Kolyvagin remains a separate analytic line. The full
`B ≤ 10^6` search and the general Beal common-prime theorem remain explicit
fields of the final input data; the proved `B < 1000` search is recorded
separately.
-/

namespace BealMatveevBeal.BealFinal

open BealMatveevBeal.RequiresTateMazurRibetFor32

/-- The general Beal conclusion, kept as an explicit proof boundary.
For positive bases and exponents at least three, a solution has a common
prime divisor. -/
structure BealTheoremData : Prop where
  commonPrime :
    ∀ x y z p q r : ℕ,
      0 < x → 0 < y → 0 < z →
      3 ≤ p → 3 ≤ q → 3 ≤ r →
      x ^ p + y ^ q = z ^ r →
      ∃ l : ℕ, Nat.Prime l ∧ l ∣ x ∧ l ∣ y ∧ l ∣ z

/-- Final dependency package.

`requiresForward` preserves the six-stage forward construction table.
`fullB0Search` is the still-explicit exhaustive-search boundary through
`B0 = 10^6`; it is not inferred from the closed `B < 1000` slice.
`bealTheorem` is the general end-of-proof boundary and is not inferred from
the signature `(4,4,13)` numerical surface. -/
structure BealFinalData : Prop where
  requiresForward : RequiresTateMazurRibetForwardData
  matveevC1 :
    BealMatveevBeal.BealMatveevBealV25B0Search.C1_floor = 143186215390
  bakerB0 :
    BealMatveevBeal.BealMatveevBealV25B0Search.B0_nat = 1000000
  fullB0Search :
    BealMatveevBeal.BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution
  bealTheorem : BealTheoremData

/-- Final forward ledger: the exact six-stage construction table, Matveev
constant, Baker cutoff, full level-26 search boundary, and general theorem
boundary, in that order. -/
theorem beal_final_forward (data : BealFinalData) :
    (BealMatveevBeal.TateCurve.TateClosureContinued ∧
      BealMatveevBeal.TateCurve.TateNeron32_928InertiaQ13 ∧
      BealMatveevBeal.MazurCurve.MazurX0_13FreyJBorel ∧
      BealMatveevBeal.RibetCurve.Ribet32a1KrausA29 ∧
      BealMatveevBeal.KolyvaginCurve.KolyvaginL_OmegaSel2Fintype ∧
      BealMatveevBeal.Conditional32Newform.Conditional32BridgeData) ∧
    BealMatveevBeal.BealMatveevBealV25B0Search.C1_floor = 143186215390 ∧
    BealMatveevBeal.BealMatveevBealV25B0Search.B0_nat = 1000000 ∧
    BealMatveevBeal.BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution ∧
    BealTheoremData :=
  ⟨requires_forward_exact_dependency_table data.requiresForward,
    data.matveevC1, data.bakerB0, data.fullB0Search, data.bealTheorem⟩

/-- General Beal theorem in forward form. Its proof source remains the
explicit `BealTheoremData` field of the final package. -/
theorem beal_main_theorem_forward (data : BealFinalData) :
    ∀ x y z p q r : ℕ,
      0 < x → 0 < y → 0 < z →
      3 ≤ p → 3 ≤ q → 3 ≤ r →
      x ^ p + y ^ q = z ^ r →
      ∃ l : ℕ, Nat.Prime l ∧ l ∣ x ∧ l ∣ y ∧ l ∣ z :=
  data.bealTheorem.commonPrime

/-- Pointwise form of the final theorem. -/
theorem beal_x_p_y_q_z_r_forward (data : BealFinalData)
    {x y z p q r : ℕ}
    (hx : 0 < x) (hy : 0 < y) (hz : 0 < z)
    (hp : 3 ≤ p) (hq : 3 ≤ q) (hr : 3 ≤ r)
    (hsol : x ^ p + y ^ q = z ^ r) :
    ∃ l : ℕ, Nat.Prime l ∧ l ∣ x ∧ l ∣ y ∧ l ∣ z :=
  beal_main_theorem_forward data x y z p q r hx hy hz hp hq hr hsol

/-- The final displayed numerical surface. It combines only proved numerical
facts with the proved `B < 1000` search. Neither this theorem nor its numerals
constructs a field of `BealFinalData`. -/
theorem beal_numerical_surface_final {A B : ℕ}
    (hsol : A ^ 4 + B ^ 4 = (B + 3) ^ 13)
    (hBpos : 1 ≤ B)
    (hA : ¬ 29 ∣ A) (hB : ¬ 29 ∣ B) (hC : 29 ∣ B + 3) :
    (BealMatveevBeal.DarmonMerelFrey4413.freyDiscNat A B =
        16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2 ∧
      Padic.valuation
          (BealMatveevBeal.Tate_I29_Inertia.freyDisc_in_Qp29 A B) =
        26 * (padicValNat 29 (B + 3) : ℤ) ∧
      (13 : ℤ) ∣ Padic.valuation
        (BealMatveevBeal.Tate_I29_Inertia.freyDisc_in_Qp29 A B) ∧
      (928 : ℕ) / 29 = 32 ∧ (32 : ℕ) * 29 = 928 ∧
      (928 : ℕ) ≠ 32 ∧ ¬ (29 : ℕ) ∣ 32 ∧
      (13 : ℕ) * 12 * 14 = 2184 ∧ 48 < 2184 ∧
      BealMatveevBeal.RibetCurve.newform_32a1_ap 29 = some (-10) ∧
      BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26a1 =
        (1 / 3 : ℚ) ∧
      BealMatveevBeal.J0_26_BSD_26a1_26b1.L_over_Omega_26b1 =
        (1 / 7 : ℚ) ∧
      BealMatveevBeal.TwoDescent_26a1_26.Sel2_card_26a1 = 1 ∧
      BealMatveevBeal.TwoDescent_26a1_26.Sel2_card_26b1 = 1 ∧
      (2 : ℕ) ^
          BealMatveevBeal.TwoDescent_26a1_26.Sel2_F2_dim_26a1 =
        1 ∧
      (2 : ℕ) ^
          BealMatveevBeal.TwoDescent_26a1_26.Sel2_F2_dim_26b1 =
        1) ∧
    BealMatveevBeal.BealMatveevBealV25B0Search.C1_floor = 143186215390 ∧
    BealMatveevBeal.BealMatveevBealV25B0Search.B0_nat = 1000000 ∧
    (∀ B < 1000, ∀ A, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13) := by
  exact ⟨numerical_surface_integrated hsol hBpos hA hB hC,
    BealMatveevBeal.BealMatveevBealV25B0Search.C1_floor_eq,
    BealMatveevBeal.BealMatveevBealV25B0Search.B0_nat_eq,
    BealMatveevBeal.BealMatveevBealV25B0Search.gap3_B_lt_1000_no_sol⟩

#check BealFinalData
#check BealTheoremData
#check beal_final_forward
#check beal_main_theorem_forward
#check beal_x_p_y_q_z_r_forward
#check beal_numerical_surface_final

#print axioms beal_final_forward
#print axioms beal_main_theorem_forward
#print axioms beal_x_p_y_q_z_r_forward
#print axioms beal_numerical_surface_final

end BealMatveevBeal.BealFinal