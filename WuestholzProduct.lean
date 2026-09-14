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
import MatveevInterpolation
import WuestholzSubgroup
import MatveevBugeaud

/-!
# Full-order product theorem packaging (not Philippon, not v25)

Successor of `1353501` (`v24-v24x-final-Wuestholz-no-uniform-c`).
Mathlib 4.12 has no Philippon zero estimate. The uniform product
theorem

  `∃ C1, ∀ X,  T ≥ C1 D  →  X is a coset of a proper subgroup`

is **not** a theorem here. What **is** a theorem:

* `𝐆_a` (dimension 1): multiplicity `≤` degree
  (`wuestholz_product_theorem_Ga`);
* `𝐆_a × 𝐆_m²` at full jet order: `T ≥ (L+1)(N1+1)(N2+1)` forces
  `P = 0 ∨` multiplicative dependence
  (`wuestholz_product_theorem_exp_of_full_order`);
* equivalently `T < coeffCount ∨ P = 0 ∨` dependence;
* the jet-dimension special case of `1353501`
  (`coeffCount ≤ c L K ≤ T`) is the same disjunction;
* no uniform `c` makes `c L K` dominate the jet, so induction on
  dimension inside Mathlib 4.12 cannot lower the threshold.

`wuestholz_product_theorem_exp` and `wuestholz_subgroup_theorem`
stay uninhabited `def Prop`. `baker_davenport_reduction` stays
uninhabited; the proved method-failure is
`bugeaud_LLL_method_fails`. Not v25.
`C1_floor = 143186215390`, `B0_nat = 1000000`.
-/

noncomputable section

open Real Polynomial
open BealMatveevBeal.MatveevInterpolation
open BealMatveevBeal.WuestholzSubgroup
open BealMatveevBeal.MatveevBugeaud

namespace BealMatveevBeal.WuestholzProduct

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_interpolation :
    C1_floor = BealMatveevBeal.MatveevInterpolation.C1_floor := rfl

theorem B0_nat_eq_interpolation :
    B0_nat = BealMatveevBeal.MatveevInterpolation.B0_nat := rfl

/-! ## Dimension-1 product theorem (`𝐆_a`) -/

/-- Base of any dimension induction available in Mathlib 4.12:
    a nonzero univariate polynomial vanishes to order at most its
    degree. -/
theorem wuestholz_product_theorem_exp_Ga_base
    (p : ℝ[X]) (hp : p ≠ 0) (a : ℝ) :
    rootMultiplicity a p ≤ natDegree p :=
  wuestholz_product_theorem_Ga p hp a

/-! ## Full-order product theorem on `𝐆_a × 𝐆_m²` -/

/-- Jet invertibility: vanishing order `T ≥ coeffCount` forces
    `P = 0` or a multiplicative relation. Re-export of
    `wuestholz_product_theorem_exp_of_full_order`. -/
theorem wuestholz_product_theorem_exp_of_full_order_reexport
    {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (L N1 N2 : ℕ)
    (P : MvPolynomial (Fin 3) ℤ)
    (hdeg : MvPolynomial.degreeOf 0 P ≤ L ∧
      MvPolynomial.degreeOf 1 P ≤ N1 ∧
        MvPolynomial.degreeOf 2 P ≤ N2)
    {T : ℕ} (hT : coeffCount L N1 N2 ≤ T)
    (hvan : vanishesToOrder (α1 : ℝ) (α2 : ℝ) P T) :
    P = 0 ∨ multiplicativelyDependent α1 α2 :=
  wuestholz_product_theorem_exp_of_full_order hα1 hα2 L N1 N2 P hdeg
    hT hvan

/-- Equivalent packaging: either `T` is below the jet dimension,
    or `P = 0`, or the frequencies are dependent. This is the
    honest product-theorem disjunction in Mathlib 4.12. -/
theorem wuestholz_product_theorem_exp_or_small_T
    {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (L N1 N2 : ℕ)
    (P : MvPolynomial (Fin 3) ℤ)
    (hdeg : MvPolynomial.degreeOf 0 P ≤ L ∧
      MvPolynomial.degreeOf 1 P ≤ N1 ∧
        MvPolynomial.degreeOf 2 P ≤ N2)
    {T : ℕ}
    (hvan : vanishesToOrder (α1 : ℝ) (α2 : ℝ) P T) :
    T < coeffCount L N1 N2 ∨
      P = 0 ∨ multiplicativelyDependent α1 α2 := by
  by_cases hT : T < coeffCount L N1 N2
  · exact Or.inl hT
  · have hle : coeffCount L N1 N2 ≤ T := Nat.le_of_not_lt hT
    exact Or.inr
      (wuestholz_product_theorem_exp_of_full_order hα1 hα2 L N1 N2 P
        hdeg hle hvan)

/-- Displayed degrees `L = 1`, `N1 = N2 = 10`: either `T < 242`,
    or `P = 0`, or dependence. Not a uniform `C1`. -/
theorem wuestholz_product_theorem_exp_one_ten_ten
    {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (P : MvPolynomial (Fin 3) ℤ)
    (hdeg : MvPolynomial.degreeOf 0 P ≤ 1 ∧
      MvPolynomial.degreeOf 1 P ≤ 10 ∧
        MvPolynomial.degreeOf 2 P ≤ 10)
    {T : ℕ}
    (hvan : vanishesToOrder (α1 : ℝ) (α2 : ℝ) P T) :
    T < 242 ∨ P = 0 ∨ multiplicativelyDependent α1 α2 := by
  have h :=
    wuestholz_product_theorem_exp_or_small_T hα1 hα2 1 10 10 P hdeg
      hvan
  simpa [coeffCount_one_ten_ten] using h

/-- Jet-dimension special case, same inhabitant as
    `wuestholz_subgroup_theorem_of_jet_dim` (`1353501`). This is
    the only inductive step from `c L K` available here: it
    requires the jet dimension to already be `≤ c L K`. -/
theorem wuestholz_product_theorem_exp_of_jet_dim
    {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (L N1 N2 : ℕ)
    (P : MvPolynomial (Fin 3) ℤ)
    (hdeg : MvPolynomial.degreeOf 0 P ≤ L ∧
      MvPolynomial.degreeOf 1 P ≤ N1 ∧
        MvPolynomial.degreeOf 2 P ≤ N2)
    {c : ℝ} {K T : ℕ}
    (hdim : (coeffCount L N1 N2 : ℝ) ≤ c * (L : ℝ) * (K : ℝ))
    (hT : c * (L : ℝ) * (K : ℝ) ≤ (T : ℝ))
    (hvan : vanishesToOrder (α1 : ℝ) (α2 : ℝ) P T) :
    P = 0 ∨ multiplicativelyDependent α1 α2 :=
  wuestholz_subgroup_theorem_of_jet_dim hα1 hα2 L N1 N2 P hdeg
    hdim hT hvan

/-- Induction on `N1,N2` cannot produce a uniform product threshold
    of shape `c L K`: the jet is quadratic in those degrees. -/
theorem no_uniform_c_for_product_theorem (L K : ℕ) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ N1 N2 : ℕ,
        (coeffCount L N1 N2 : ℝ) ≤ c * (L : ℝ) * (K : ℝ) :=
  no_uniform_c_reaches_full_order L K

theorem no_uniform_c_linear_in_N_reexport :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 : ℕ,
        (coeffCount L N1 N2 : ℝ) ≤
          c * (L + 1 : ℝ) * ((N1 + 1 : ℝ) + (N2 + 1 : ℝ)) :=
  no_uniform_c_linear_in_N

/-! ## Locked uninhabited Props (Philippon is not in Mathlib 4.12) -/

/-- Uniform exponential product theorem along `W`. Inhabited on
    `𝐆_a` and at full jet order; the intermediate-`T` / coset form
    stays open. -/
def wuestholz_product_theorem_exp : Prop :=
  BealMatveevBeal.MatveevInterpolation.wuestholz_product_theorem_exp

/-- Uniform intermediate-`T` subgroup theorem. Not a theorem of
    jet invertibility. -/
def wuestholz_subgroup_theorem : Prop :=
  BealMatveevBeal.MatveevInterpolation.wuestholz_subgroup_theorem

def baker_davenport_reduction : Prop :=
  BealMatveevBeal.MatveevBugeaud.baker_davenport_reduction

def bugeaud_LLL_reduction_proof : Prop :=
  BealMatveevBeal.MatveevBugeaud.bugeaud_LLL_reduction_proof

#check C1_floor_eq
#check B0_nat_eq
#check wuestholz_product_theorem_exp_Ga_base
#check wuestholz_product_theorem_exp_of_full_order_reexport
#check wuestholz_product_theorem_exp_or_small_T
#check wuestholz_product_theorem_exp_one_ten_ten
#check wuestholz_product_theorem_exp_of_jet_dim
#check no_uniform_c_for_product_theorem
#check no_uniform_c_linear_in_N_reexport
#check wuestholz_product_theorem_exp
#check wuestholz_subgroup_theorem
#check baker_davenport_reduction
#check bugeaud_LLL_reduction_proof
#check bugeaud_LLL_method_fails
#check baker_davenport_reduction_nogo
#print axioms wuestholz_product_theorem_exp_Ga_base
#print axioms wuestholz_product_theorem_exp_or_small_T
#print axioms wuestholz_product_theorem_exp_one_ten_ten
#print axioms wuestholz_product_theorem_exp_of_jet_dim
#print axioms no_uniform_c_for_product_theorem
#print axioms bugeaud_LLL_method_fails

end BealMatveevBeal.WuestholzProduct
