/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import RequiresTateMazurRibetFor32.ForwardDoc
import BealMatveevBealV25B0Search

/-!
# v25 forward Matveev--level-26 interface

This module records the v25 dependency order without using displayed
arithmetic backwards to construct Matveev, level-lowering, or exhaustive
search evidence.

The closed `B < 1000` proposition and the full `B ≤ 10^6` proposition are
separate fields. The latter remains an explicit proof boundary.
-/

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Forward

open BealMatveevBeal.RequiresTateMazurRibetFor32

/-- The numerical Matveev constant and Baker cutoff, kept ahead of the
level-26 and search stages. -/
structure MatveevBoundData : Prop where
  matveevC1 :
    BealMatveevBealV25B0Search.C1_floor = 143186215390
  bakerB0 :
    BealMatveevBealV25B0Search.B0_nat = 1000000

/-- Level-26 arithmetic attached to the gap-3 solution branch.

These facts are a forward numerical surface only. They do not construct
Tate, Mazur, Ribet, modularity, or search evidence. -/
structure Level26SearchData : Prop where
  numerical :
    ∀ {A B : ℕ},
      A ^ 4 + B ^ 4 = (B + 3) ^ 13 →
      1 ≤ B →
      ¬ 29 ∣ A →
      ¬ 29 ∣ B →
      29 ∣ B + 3 →
      BealMatveevBeal.DarmonMerelFrey4413.freyDiscNat A B =
          16 * A ^ 8 * B ^ 8 * (A ^ 4 + B ^ 4) ^ 2 ∧
        Padic.valuation
            (BealMatveevBeal.Tate_I29_Inertia.freyDisc_in_Qp29 A B) =
          26 * (padicValNat 29 (B + 3) : ℤ) ∧
        (13 : ℤ) ∣ Padic.valuation
          (BealMatveevBeal.Tate_I29_Inertia.freyDisc_in_Qp29 A B) ∧
        (928 : ℕ) / 29 = 32 ∧
        (32 : ℕ) * 29 = 928

/-- Complete v25 forward package.

The field order is the proof order: Matveev bound, level-26 arithmetic,
the proved `B < 1000` elimination, and finally the still-explicit
`B ≤ 10^6` boundary. -/
structure MatveevLevel26ForwardData : Prop where
  matveevBound : MatveevBoundData
  level26Search : Level26SearchData
  searchBelow1000 :
    ∀ B < 1000, ∀ A : ℕ, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13
  fullB0Search :
    BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution

/-- Search projections in forward order. The exhaustive `B ≤ 10^6`
conclusion comes only from the explicit final field. -/
theorem B0_search_forward (data : MatveevLevel26ForwardData) :
    (∀ B < 1000, ∀ A : ℕ, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13) ∧
      BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution :=
  ⟨data.searchBelow1000, data.fullB0Search⟩

/-- Exact v25 dependency ledger: Matveev constants, level-26 surface,
closed small search, then explicit full-search boundary. -/
theorem beal_matveev_level26_forward (data : MatveevLevel26ForwardData) :
    MatveevBoundData ∧
      Level26SearchData ∧
      (∀ B < 1000, ∀ A : ℕ, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13) ∧
      BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution :=
  ⟨data.matveevBound, data.level26Search, data.searchBelow1000,
    data.fullB0Search⟩

/-- Parallel numerical projection. No component is used backwards to
manufacture either search field. -/
theorem v25_numerical_surface_forward (data : MatveevLevel26ForwardData)
    {A B : ℕ}
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
      (928 : ℕ) / 29 = 32 ∧
      (32 : ℕ) * 29 = 928) ∧
    BealMatveevBealV25B0Search.C1_floor = 143186215390 ∧
    BealMatveevBealV25B0Search.B0_nat = 1000000 ∧
    (∀ B < 1000, ∀ A : ℕ, A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13) ∧
    BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution :=
  ⟨data.level26Search.numerical hsol hBpos hA hB hC,
    data.matveevBound.matveevC1, data.matveevBound.bakerB0,
    data.searchBelow1000, data.fullB0Search⟩

#check MatveevBoundData
#check Level26SearchData
#check MatveevLevel26ForwardData
#check B0_search_forward
#check beal_matveev_level26_forward
#check v25_numerical_surface_forward

#print axioms B0_search_forward
#print axioms beal_matveev_level26_forward
#print axioms v25_numerical_surface_forward

end BealMatveevBeal.BealMatveevBealV25B0Search.Forward