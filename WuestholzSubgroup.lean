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
import MatveevBugeaud

/-!
# Intermediate-`T` Wüstholz subgroup facts (not a uniform `c`)

Successor of `cfd4794` (`v24-v24x-final-LLL-nogo`). Mathlib 4.12
has no Philippon zero estimate. The uniform statement

  `∃ c > 0, ∀ L,N1,N2,K,T,  T ≥ c L K  →  P = 0 ∨ dependence`

is **not** a theorem: `no_uniform_c_reaches_full_order` already
shows that for every `c`, some `N1,N2` make the jet dimension
`(L+1)(N1+1)(N2+1)` strictly larger than `c L K`. Displayed
examples: `c = 1/2`, `c = 1/242`, `c = 1/1000` all lose to
`coeffCount 1 10 10 = 242`. Linear `K ∼ N1+N2` still has no
uniform `c`.

What **is** a theorem:

* classification of proper candidates for `W ⊂ 𝐆_a × 𝐆_m²`
  (`y1=1`, `y2=1`, `z=0`, graphs `y1^a y2^b=1`);
* easy half: independence keeps `W` out of every candidate;
* full-order jet invertibility `T ≥ (L+1)(N1+1)(N2+1)`;
* the special case `coeffCount ≤ c L K ≤ T` reduces to that
  disjunction (`wuestholz_subgroup_of_jet_dim_le_threshold`);
* Siegel on `𝐆_a` produces a nonzero `P` vanishing only to
  order `N/2 <` jet dimension.

`wuestholz_subgroup_theorem` and `wuestholz_product_theorem_exp`
stay uninhabited `def Prop`. Not v25. `C1_floor = 143186215390`,
`B0_nat = 1000000`.
-/

noncomputable section

open Real
open BealMatveevBeal.MatveevInterpolation

namespace BealMatveevBeal.WuestholzSubgroup

/-! ## Locked numerals -/

def C1_floor : ℕ := 143186215390

def B0_nat : ℕ := 1000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl

theorem B0_nat_eq : B0_nat = 1000000 := rfl

theorem C1_floor_eq_interpolation :
    C1_floor = BealMatveevBeal.MatveevInterpolation.C1_floor := rfl

theorem B0_nat_eq_interpolation :
    B0_nat = BealMatveevBeal.MatveevInterpolation.B0_nat := rfl

/-! ## `𝐆_a × 𝐆_m²` candidates and degree -/

/-- Integer model of a proper algebraic subgroup of `𝐆_a × 𝐆_m²`:
    `isGa` is the factor `{z = 0} × 𝐆_m²`; otherwise
    `y1^a y2^b = 1`. -/
structure AlgebraicSubgroup where
  a : ℤ
  b : ℤ
  isGa : Bool

def degSubgroup (H : AlgebraicSubgroup) : ℕ :=
  Int.natAbs H.a + Int.natAbs H.b + 1

theorem degSubgroup_pos (H : AlgebraicSubgroup) :
    0 < degSubgroup H :=
  Nat.succ_pos _

def candidate_y1 : AlgebraicSubgroup := ⟨1, 0, false⟩
def candidate_y2 : AlgebraicSubgroup := ⟨0, 1, false⟩
def candidate_z : AlgebraicSubgroup := ⟨0, 0, true⟩

def candidateSubgroups : List AlgebraicSubgroup :=
  [candidate_y1, candidate_y2, candidate_z]

theorem candidateSubgroups_length : candidateSubgroups.length = 3 := rfl

theorem deg_candidate_y1 : degSubgroup candidate_y1 = 2 := by
  simp [degSubgroup, candidate_y1]

theorem deg_candidate_y2 : degSubgroup candidate_y2 = 2 := by
  simp [degSubgroup, candidate_y2]

theorem deg_candidate_z : degSubgroup candidate_z = 1 := by
  simp [degSubgroup, candidate_z]

/-- Displayed candidates `y1=1`, `y2=1` keep `W` out when
    `1 < αi` (easy half on the coordinate factors). -/
theorem not_W_in_y1_of_two_three :
    ¬ W_in_candidate 2 3 .vanishY1 :=
  not_W_in_vanishY1 (by decide : (1 : ℕ) < 2)

theorem not_W_in_y2_of_two_three :
    ¬ W_in_candidate 2 3 .vanishY2 :=
  not_W_in_vanishY2 (by decide : (1 : ℕ) < 3)

/-! ## Gap-3 tangent of `W` -/

/-- Lie direction of `t ↦ (t, A^t, (B+3)^t)`. -/
def W_tangent (A B : ℕ) : Fin 3 → ℝ := fun i =>
  if i = 0 then (1 : ℝ)
  else if i = 1 then log (A : ℝ)
  else log ((B + 3 : ℕ) : ℝ)

theorem W_tangent_zero (A B : ℕ) : W_tangent A B 0 = 1 := by
  simp [W_tangent]

theorem W_tangent_one (A B : ℕ) :
    W_tangent A B 1 = log (A : ℝ) := by
  simp [W_tangent]

theorem W_tangent_two (A B : ℕ) :
    W_tangent A B 2 = log ((B + 3 : ℕ) : ℝ) := by
  simp [W_tangent]

/-- Vanishing of `Φ(z) = P(z, α1^z, α2^z)` to order `T` at `0`
    along `W`. Same predicate as the interpolation jet. -/
def vanishesToOrder (α1 α2 : ℝ) (P : MvPolynomial (Fin 3) ℤ)
    (T : ℕ) : Prop :=
  ∀ k < T,
    iteratedDslope (matveevPhi_of_mvPolynomial P α1 α2) k 0 = 0

theorem vanishesToOrder_zero (α1 α2 : ℝ)
    (P : MvPolynomial (Fin 3) ℤ) :
    vanishesToOrder α1 α2 P 0 := by
  intro k hk
  exact (Nat.not_lt_zero k hk).elim

theorem vanishesToOrder_mono {α1 α2 : ℝ}
    {P : MvPolynomial (Fin 3) ℤ} {T U : ℕ}
    (hTU : T ≤ U) (h : vanishesToOrder α1 α2 P U) :
    vanishesToOrder α1 α2 P T := fun k hk =>
  h k (lt_of_lt_of_le hk hTU)

/-! ## Jet dimension versus `c L K` -/

theorem coeffCount_one_ten_ten :
    coeffCount 1 10 10 = 242 := by
  simp [coeffCount]

/-- Easy half from `46bdeea`: `c = 1/2`, `L = K = 1`,
    `N1 = N2 = 10` gives `0.5 < 242`. -/
theorem no_uniform_c_easy_half :
    ((1 : ℝ) / 2) * 1 * 1 < coeffCount 1 10 10 :=
  intermediate_T_example_half

theorem no_uniform_c_one_div_two_forty_two :
    ((1 : ℝ) / 242) * 1 * 1 < coeffCount 1 10 10 := by
  rw [coeffCount_one_ten_ten]
  norm_num

/-- Suggested `c = 1/1000` still loses to the displayed jet. -/
theorem no_uniform_c_one_div_thousand :
    ((1 : ℝ) / 1000) * 1 * 1 < coeffCount 1 10 10 := by
  rw [coeffCount_one_ten_ten]
  norm_num

/-- Re-export: for every `c`, some `G_m` degrees make the jet
    larger than `c L K`. -/
theorem intermediate_threshold_lt_jet_dim_reexport (c : ℝ) (L K : ℕ) :
    ∃ N1 N2 : ℕ, (c : ℝ) * L * K < coeffCount L N1 N2 :=
  intermediate_threshold_lt_jet_dim c L K

/-- No uniform `c` makes `c L K` dominate the jet dimension for
    every `N1,N2`. -/
theorem no_uniform_c_reaches_full_order_reexport (L K : ℕ) :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ N1 N2 : ℕ,
        (coeffCount L N1 N2 : ℝ) ≤ c * (L : ℝ) * (K : ℝ) :=
  no_uniform_c_reaches_full_order L K

/-- Even taking `K` linear in the `G_m` degrees (`N1+N2+2`) there
    is no uniform `c`: the jet is quadratic in those degrees. -/
theorem no_uniform_c_linear_in_N :
    ¬ ∃ c : ℝ, 0 < c ∧
      ∀ L N1 N2 : ℕ,
        (coeffCount L N1 N2 : ℝ) ≤
          c * (L + 1 : ℝ) * ((N1 + 1 : ℝ) + (N2 + 1 : ℝ)) := by
  rintro ⟨c, _hc, hforall⟩
  obtain ⟨n, hn⟩ := exists_nat_gt (2 * c)
  have h := hforall 0 n n
  have hcnt : (coeffCount 0 n n : ℝ) = (n + 1 : ℝ) * (n + 1) := by
    simp [coeffCount]
  have hle : (n + 1 : ℝ) * (n + 1) ≤
      c * (0 + 1 : ℝ) * ((n + 1 : ℝ) + (n + 1 : ℝ)) := by
    simpa [hcnt] using h
  have hrhs : c * (0 + 1 : ℝ) * ((n + 1 : ℝ) + (n + 1 : ℝ)) =
      (2 * c) * (n + 1 : ℝ) := by
    ring
  have hn1 : (2 * c) < (n + 1 : ℝ) := by
    have : (n : ℝ) < n + 1 := lt_add_one _
    linarith [hn]
  have hpos : (0 : ℝ) < n + 1 := by positivity
  have hlt : (2 * c) * (n + 1 : ℝ) < (n + 1 : ℝ) * (n + 1) :=
    (mul_lt_mul_right hpos).mpr hn1
  exact not_le_of_gt (hrhs ▸ hlt) hle

/-- Siegel on `𝐆_a` never reaches full jet order. -/
theorem siegel_T_lt_jet_dim {L N1 N2 : ℕ}
    (hN : 2 ≤ coeffCount L N1 N2) :
    siegel_T L N1 N2 < coeffCount L N1 N2 :=
  siegel_T_lt hN

/-- Easy half, re-exported: independence keeps `W` out of every
    proper candidate. -/
theorem easy_half_W_not_in_candidate {α1 α2 : ℕ}
    (hα1 : 1 < α1) (hα2 : 1 < α2)
    (hindep : ¬ multiplicativelyDependent α1 α2)
    (H : ProperSubgroupCandidate) :
    ¬ W_in_candidate α1 α2 H :=
  W_not_in_proper_candidate_of_indep hα1 hα2 hindep H

/-- Inhabited special case of the subgroup statement: if the jet
    dimension is already `≤ c L K ≤ T`, full-order invertibility
    gives `P = 0 ∨ dependence`. This is **not** uniform in
    `N1,N2`. -/
theorem wuestholz_subgroup_theorem_of_jet_dim
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
  wuestholz_subgroup_of_jet_dim_le_threshold hα1 hα2 L N1 N2 P hdeg
    hdim hT hvan

/-! ## Locked uninhabited Props (Philippon is not in Mathlib 4.12) -/

/-- Uniform intermediate-`T` subgroup theorem. Not a theorem:
    `no_uniform_c_reaches_full_order` / `no_uniform_c_linear_in_N`. -/
def wuestholz_subgroup_theorem : Prop :=
  BealMatveevBeal.MatveevInterpolation.wuestholz_subgroup_theorem

/-- Exponential product theorem along `W`. Inhabited on `𝐆_a` and
    at full jet order; the intermediate-`T` form stays open. -/
def wuestholz_product_theorem_exp : Prop :=
  BealMatveevBeal.MatveevInterpolation.wuestholz_product_theorem_exp

#check C1_floor_eq
#check B0_nat_eq
#check degSubgroup_pos
#check not_W_in_y1_of_two_three
#check W_tangent_zero
#check vanishesToOrder_zero
#check coeffCount_one_ten_ten
#check no_uniform_c_easy_half
#check no_uniform_c_one_div_two_forty_two
#check no_uniform_c_one_div_thousand
#check no_uniform_c_linear_in_N
#check no_uniform_c_reaches_full_order_reexport
#check siegel_T_lt_jet_dim
#check easy_half_W_not_in_candidate
#check wuestholz_subgroup_theorem_of_jet_dim
#check wuestholz_subgroup_theorem
#check wuestholz_product_theorem_exp
#check BealMatveevBeal.MatveevBugeaud.bugeaud_bd_lower_lt_inv_B
#print axioms no_uniform_c_easy_half
#print axioms no_uniform_c_one_div_thousand
#print axioms no_uniform_c_linear_in_N
#print axioms wuestholz_subgroup_theorem_of_jet_dim
#print axioms siegel_T_lt_jet_dim

end BealMatveevBeal.WuestholzSubgroup
