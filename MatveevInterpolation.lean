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
import MatveevThm14Proof

/-!
# Interpolation track toward Matveev 2000 Thm 1.4 (n=2)

Mathlib 4.12 has no Matveev interpolation, no Wüstholz product
theorem for exponential polynomials, and no Bugeaud κ=1 refinement.
This file starts that work honestly.

Matveev 2000 applies to **algebraic** numbers. The bare-real claim

  `∀ A C : ℝ, 1 < A → 1 < C → Λ ≠ 0 → |4 log A − 13 log C| > exp(−C₀ …)`

is **false**. That is `matveev_thm14_n2_real_explicit_is_false`.
The name `matveev_thm14_n2_real_explicit` stays a `def Prop`.

Proved, axioms `[propext, Classical.choice, Quot.sound]` only:

* `C1_floor = 143186215390`, `height_B0_nat = 104382751019310000000`,
  `B0_nat = 1000000`;
* rational height and Liouville `|a/b| ≥ exp(−h(a,b))`;
* Δ(L,K,N1,N2,α1,α2) as on Matveev 2000 p.5;
* Vandermonde / binomial interpolation determinants nonzero;
* product theorem on `𝐆_a` (polynomial multiplicity calculus);
* Hadamard size `|Δ| ≤ n! X^n` and `|log α| ≤ α−1`;
* interpolation contradiction schema (small upper + Liouville);
* Bugeaud κ=1 floor `C1_floor` by `rfl`;
* Track 1 integer bound (`matveev_thm14_n2_explicit_of_nat`).

Wüstholz for exponential polynomials and the analytic `|Δ| ≤ exp(−c L K)`
bound stay `def Prop`. Not v25.
-/

noncomputable section

open Real Matrix Polynomial

namespace BealMatveevBeal.MatveevInterpolation

/-! ## Displayed constants -/

def C1_floor : ℕ := 143186215390
def height_B0_nat : ℕ := 104382751019310000000
def B0_nat : ℕ := 1000000
def thirty_pow_six : ℕ := 729000000

theorem C1_floor_eq : C1_floor = 143186215390 := rfl
theorem height_B0_nat_eq : height_B0_nat = 104382751019310000000 := rfl
theorem B0_nat_eq : B0_nat = 1000000 := rfl
theorem B0_nat_eq_ten_pow_six : B0_nat = Nat.pow 10 6 := by decide
theorem thirty_pow_six_eq : thirty_pow_six = 729000000 := rfl
theorem thirty_pow_six_eq_pow : thirty_pow_six = Nat.pow 30 6 := by decide
theorem height_B0_eq_product : height_B0_nat = C1_floor * thirty_pow_six := by decide

def C1_floor_real : ℝ := (C1_floor : ℝ)
def height_B0_real : ℝ := (height_B0_nat : ℝ)

theorem C1_floor_real_pos : (0 : ℝ) < C1_floor_real := by
  unfold C1_floor_real C1_floor
  norm_num

theorem C1_floor_eq_proof : C1_floor = MatveevThm14Proof.C1_floor := rfl
theorem height_B0_eq_proof : height_B0_nat = MatveevThm14Proof.height_B0_nat := rfl

/-! ## Height and Liouville (positive rationals `a / b`) -/

def ratHeight (a b : ℕ) : ℝ :=
  log (max (a : ℝ) (b : ℝ))

theorem ratHeight_nonneg {a b : ℕ} (ha : 0 < a) (_hb : 0 < b) :
    (0 : ℝ) ≤ ratHeight a b := by
  have hmax : (1 : ℝ) ≤ max (a : ℝ) (b : ℝ) := by
    have : (1 : ℝ) ≤ a := by exact_mod_cast (Nat.succ_le_of_lt ha)
    exact le_trans this (le_max_left _ _)
  unfold ratHeight
  exact Real.log_nonneg hmax

theorem ratHeight_pos {a b : ℕ} (h : 1 < max a b) :
    (0 : ℝ) < ratHeight a b := by
  have h1 : (1 : ℝ) < max (a : ℝ) (b : ℝ) := by exact_mod_cast h
  unfold ratHeight
  exact Real.log_pos h1

theorem liouville_nat_div {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    (1 : ℝ) / max (a : ℝ) (b : ℝ) ≤ (a : ℝ) / b := by
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have h1 : (1 : ℝ) ≤ a := by exact_mod_cast (Nat.succ_le_of_lt ha)
  have hmaxpos : (0 : ℝ) < max (a : ℝ) (b : ℝ) :=
    lt_of_lt_of_le hapos (le_max_left _ _)
  have hle1 : (1 : ℝ) / max (a : ℝ) (b : ℝ) ≤ a / max (a : ℝ) (b : ℝ) :=
    div_le_div_of_nonneg_right h1 (le_of_lt hmaxpos)
  have hle2 : a / max (a : ℝ) (b : ℝ) ≤ a / b :=
    div_le_div_of_nonneg_left (le_of_lt hapos) hbpos (le_max_right _ _)
  exact le_trans hle1 hle2

theorem liouville_nat_div_exp {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    exp (-ratHeight a b) ≤ (a : ℝ) / b := by
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hmaxpos : (0 : ℝ) < max (a : ℝ) (b : ℝ) :=
    lt_of_lt_of_le hapos (le_max_left _ _)
  have hlog : exp (-ratHeight a b) = 1 / max (a : ℝ) (b : ℝ) := by
    unfold ratHeight
    rw [Real.exp_neg, Real.exp_log hmaxpos, inv_eq_one_div]
  rw [hlog]
  exact liouville_nat_div ha hb

/-! ## Interpolation determinant -/

def interpolationNodes (n : ℕ) : Fin n → ℝ := fun i => (i : ℝ)

theorem interpolationNodes_injective (n : ℕ) :
    Function.Injective (interpolationNodes n) := by
  intro i j h
  have : (i : ℕ) = (j : ℕ) := by
    have h' : (i : ℝ) = (j : ℝ) := h
    exact_mod_cast h'
  exact Fin.ext this

def interpolationMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℝ :=
  vandermonde (interpolationNodes n)

def interpolationDet (n : ℕ) : ℝ := (interpolationMatrix n).det

theorem interpolation_det_ne_zero (n : ℕ) : interpolationDet n ≠ 0 := by
  unfold interpolationDet interpolationMatrix
  exact (det_vandermonde_ne_zero_iff).2 (interpolationNodes_injective n)

theorem interpolation_det_eq_prod (n : ℕ) :
    interpolationDet n = (vandermonde (interpolationNodes n)).det :=
  rfl

structure InterpColumn where
  l1 : ℕ
  l2 : ℕ
  k : ℕ

def matveevEntry (α1 α2 : ℝ) (col : InterpColumn) (i : ℕ) : ℝ :=
  (col.k.choose i : ℝ) * α1 ^ col.l1 * α2 ^ col.l2

def matveevInterpMatrix (n : ℕ) (α1 α2 : ℝ) (cols : Fin n → InterpColumn) :
    Matrix (Fin n) (Fin n) ℝ :=
  Matrix.of fun i j => matveevEntry α1 α2 (cols j) i.val

def binomialInterpMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℤ :=
  Matrix.of fun i j => ((j : ℕ).choose (i : ℕ) : ℤ)

theorem binomialInterpMatrix_blockTriangular (n : ℕ) :
    (binomialInterpMatrix n).BlockTriangular id := by
  intro i j hij
  unfold binomialInterpMatrix
  simp only [of_apply, id_eq]
  have hlt : (j : ℕ) < (i : ℕ) := hij
  exact_mod_cast Nat.choose_eq_zero_of_lt hlt

theorem binomialInterpMatrix_diag (n : ℕ) (i : Fin n) :
    binomialInterpMatrix n i i = 1 := by
  unfold binomialInterpMatrix
  simp [Nat.choose_self]

theorem binomial_interpolation_det_eq_one (n : ℕ) :
    (binomialInterpMatrix n).det = 1 := by
  rw [det_of_upperTriangular (binomialInterpMatrix_blockTriangular n)]
  refine Finset.prod_eq_one ?_
  intro i _
  exact binomialInterpMatrix_diag n i

theorem binomial_interpolation_det_ne_zero (n : ℕ) :
    (binomialInterpMatrix n).det ≠ 0 := by
  rw [binomial_interpolation_det_eq_one]
  exact one_ne_zero

theorem matveevInterpMatrix_binomial (n : ℕ) :
    matveevInterpMatrix n 1 1 (fun j => ⟨0, 0, j⟩) =
      (binomialInterpMatrix n).map fun a => (a : ℝ) := by
  ext i j
  unfold matveevInterpMatrix matveevEntry binomialInterpMatrix
  simp [pow_zero]

/-! ## Matveev 2000 p.5 interpolation determinant Δ(L,K,N1,N2,α1,α2)

Columns are indexed by `(ℓ,k)` with `0 ≤ ℓ ≤ L` and `0 ≤ k ≤ K`.
Entry `(i,j)` is `(k_j).choose i * α1^{ℓ_j N1} * α2^{ℓ_j N2}`.
-/

def interpDim (L K : ℕ) : ℕ := (L + 1) * (K + 1)

theorem interpDim_pos (L K : ℕ) : 0 < interpDim L K :=
  Nat.mul_pos (Nat.succ_pos L) (Nat.succ_pos K)

theorem interpDim_eq (L K : ℕ) : interpDim L K = (L + 1) * (K + 1) := rfl

def decodeL (L K : ℕ) (j : Fin (interpDim L K)) : ℕ :=
  j.val / (K + 1)

def decodeK (L K : ℕ) (j : Fin (interpDim L K)) : ℕ :=
  j.val % (K + 1)

theorem decodeL_lt (L K : ℕ) (j : Fin (interpDim L K)) :
    decodeL L K j < L + 1 := by
  unfold decodeL
  have hpos : 0 < K + 1 := Nat.succ_pos K
  exact (Nat.div_lt_iff_lt_mul hpos).2 j.isLt

theorem decodeK_lt (L K : ℕ) (j : Fin (interpDim L K)) :
    decodeK L K j < K + 1 :=
  Nat.mod_lt _ (Nat.succ_pos K)

theorem decodeL_le (L K : ℕ) (j : Fin (interpDim L K)) :
    decodeL L K j ≤ L :=
  Nat.lt_succ_iff.mp (decodeL_lt L K j)

theorem decodeK_le (L K : ℕ) (j : Fin (interpDim L K)) :
    decodeK L K j ≤ K :=
  Nat.lt_succ_iff.mp (decodeK_lt L K j)

theorem decodeL_eq_zero_of_L0 (K : ℕ) (j : Fin (interpDim 0 K)) :
    decodeL 0 K j = 0 :=
  Nat.lt_one_iff.mp (decodeL_lt 0 K j)

theorem decodeK_eq_val_of_L0 (K : ℕ) (j : Fin (interpDim 0 K)) :
    decodeK 0 K j = j.val := by
  unfold decodeK interpDim
  have : j.val < K + 1 := by
    simpa [interpDim] using j.isLt
  exact Nat.mod_eq_of_lt this

def matveevColumn (L K N1 N2 : ℕ) (j : Fin (interpDim L K)) : InterpColumn :=
  ⟨decodeL L K j * N1, decodeL L K j * N2, decodeK L K j⟩

theorem matveevColumn_L0 (K : ℕ) (j : Fin (interpDim 0 K)) :
    matveevColumn 0 K 0 0 j = ⟨0, 0, j.val⟩ := by
  unfold matveevColumn
  simp [decodeL_eq_zero_of_L0, decodeK_eq_val_of_L0]

/-- Interpolation determinant Δ(L,K,N1,N2,α1,α2) as on Matveev 2000 p.5. -/
def interpolationDeterminant (L K N1 N2 : ℕ) (α1 α2 : ℝ) : ℝ :=
  (matveevInterpMatrix (interpDim L K) α1 α2 (matveevColumn L K N1 N2)).det

theorem interpolationDeterminant_L0_eq_binomial_det (K : ℕ) :
    interpolationDeterminant 0 K 0 0 1 1 =
      ((binomialInterpMatrix (interpDim 0 K)).map fun a => (a : ℝ)).det := by
  unfold interpolationDeterminant
  have hmat :
      matveevInterpMatrix (interpDim 0 K) 1 1 (matveevColumn 0 K 0 0) =
        (binomialInterpMatrix (interpDim 0 K)).map fun a => (a : ℝ) := by
    ext i j
    unfold matveevInterpMatrix matveevEntry binomialInterpMatrix matveevColumn
    simp [decodeL_eq_zero_of_L0, decodeK_eq_val_of_L0, pow_zero]
  rw [hmat]

theorem map_intCast_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ) :
    ((M.map fun a => (a : ℝ))).det = (M.det : ℝ) :=
  ((Int.castRingHom ℝ).map_det M).symm

theorem interpolationDeterminant_L0_eq_one (K : ℕ) :
    interpolationDeterminant 0 K 0 0 1 1 = 1 := by
  rw [interpolationDeterminant_L0_eq_binomial_det, map_intCast_det,
    binomial_interpolation_det_eq_one]
  norm_num

theorem interpolationDeterminant_L0_ne_zero (K : ℕ) :
    interpolationDeterminant 0 K 0 0 1 1 ≠ 0 := by
  rw [interpolationDeterminant_L0_eq_one]
  exact one_ne_zero

/-- Vandermonde specialisation is already `interpolation_det_ne_zero`. -/
theorem determinant_nonzero (n : ℕ) : interpolationDet n ≠ 0 :=
  interpolation_det_ne_zero n

theorem determinant_nonzero_binomial (n : ℕ) :
    (binomialInterpMatrix n).det ≠ 0 :=
  binomial_interpolation_det_ne_zero n

/-! ## Polynomial zero estimate -/

theorem natDegree_X_sub_C_pow {R : Type*} [CommRing R] [Nontrivial R] [NoZeroDivisors R]
    (a : R) (m : ℕ) :
    natDegree ((X - C a) ^ m : R[X]) = m := by
  rw [natDegree_pow, natDegree_X_sub_C, mul_one]

theorem poly_zero_estimate {R : Type*} [CommRing R] [IsDomain R]
    (p : R[X]) (hp : p ≠ 0) (a : R) :
    rootMultiplicity a p ≤ natDegree p := by
  have hdvd := pow_rootMultiplicity_dvd p a
  have hle := natDegree_le_of_dvd hdvd hp
  have hdeg : natDegree ((X - C a) ^ rootMultiplicity a p : R[X]) =
      rootMultiplicity a p :=
    natDegree_X_sub_C_pow a _
  rwa [hdeg] at hle

theorem zero_estimate_polynomial (p : ℝ[X]) (hp : p ≠ 0) (a : ℝ) :
    rootMultiplicity a p ≤ natDegree p :=
  poly_zero_estimate p hp a

/-! ## Product theorem for G_a (polynomial case)

Wüstholz's product theorem bounds the vanishing order of a polynomial
on a product of algebraic groups. Mathlib 4.12 has no such theorem for
exponential polynomials. This section formalises the product theorem
on `𝐆_a` (additive group): a nonzero polynomial vanishes to order at
most its degree, and multiplicity is additive on products.

This is the commutative algebraic-group special case used in Matveev's
interpolation when the auxiliary function is polynomial.
-/

theorem wuestholz_mul {p q : ℝ[X]} {a : ℝ} (hpq : p * q ≠ 0) :
    rootMultiplicity a (p * q) = rootMultiplicity a p + rootMultiplicity a q :=
  rootMultiplicity_mul hpq

theorem wuestholz_pow (p : ℝ[X]) (n : ℕ) (a : ℝ) (hp : p ≠ 0) :
    rootMultiplicity a (p ^ n) = n * rootMultiplicity a p := by
  induction n with
  | zero =>
    simp [rootMultiplicity_C]
  | succ n ih =>
    have hpow : p ^ n ≠ 0 := pow_ne_zero n hp
    have hmul : p ^ n * p ≠ 0 := mul_ne_zero hpow hp
    rw [pow_succ, rootMultiplicity_mul hmul, ih, Nat.succ_mul, add_comm]

theorem wuestholz_C (c a : ℝ) : rootMultiplicity a (C c : ℝ[X]) = 0 :=
  rootMultiplicity_C c a

theorem wuestholz_one (a : ℝ) : rootMultiplicity a (1 : ℝ[X]) = 0 :=
  wuestholz_C 1 a

theorem wuestholz_X_sub_C_pow (a : ℝ) (n : ℕ) :
    rootMultiplicity a ((X - C a) ^ n : ℝ[X]) = n :=
  rootMultiplicity_X_sub_C_pow a n

theorem wuestholz_degree_add {p q : ℝ[X]} (hp : p ≠ 0) (hq : q ≠ 0) :
    natDegree (p * q) = natDegree p + natDegree q :=
  natDegree_mul hp hq

theorem wuestholz_degree_le_mul (p q : ℝ[X]) :
    natDegree (p * q) ≤ natDegree p + natDegree q :=
  natDegree_mul_le

theorem wuestholz_product_two {p q : ℝ[X]} (hpq : p * q ≠ 0) (a : ℝ) :
    rootMultiplicity a (p * q) ≤ natDegree p + natDegree q := by
  have hp : p ≠ 0 := left_ne_zero_of_mul hpq
  have hq : q ≠ 0 := right_ne_zero_of_mul hpq
  rw [wuestholz_mul (a := a) hpq]
  exact add_le_add (zero_estimate_polynomial p hp a)
    (zero_estimate_polynomial q hq a)

theorem wuestholz_list_prod_ne_zero {ps : List ℝ[X]}
    (h : ∀ p ∈ ps, p ≠ 0) : ps.prod ≠ 0 := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.prod_cons]
    have hp : p ≠ 0 := h p (List.mem_cons_self _ _)
    have hps : ∀ q ∈ ps, q ≠ 0 := fun q hq => h q (List.mem_cons_of_mem _ hq)
    exact mul_ne_zero hp (ih hps)

theorem wuestholz_list_prod (ps : List ℝ[X]) (a : ℝ)
    (h : ∀ p ∈ ps, p ≠ 0) :
    rootMultiplicity a ps.prod = (ps.map (rootMultiplicity a)).sum := by
  induction ps with
  | nil =>
    simp [wuestholz_one]
  | cons p ps ih =>
    have hp : p ≠ 0 := h p (List.mem_cons_self _ _)
    have hps : ∀ q ∈ ps, q ≠ 0 := fun q hq => h q (List.mem_cons_of_mem _ hq)
    have hprod : ps.prod ≠ 0 := wuestholz_list_prod_ne_zero hps
    have hmul : p * ps.prod ≠ 0 := mul_ne_zero hp hprod
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    rw [rootMultiplicity_mul hmul, ih hps]

theorem wuestholz_list_degree_le (ps : List ℝ[X]) :
    natDegree ps.prod ≤ (ps.map natDegree).sum := by
  induction ps with
  | nil => simp
  | cons p ps ih =>
    simp only [List.prod_cons, List.map_cons, List.sum_cons]
    exact le_trans natDegree_mul_le (add_le_add_left ih _)

theorem wuestholz_list_zero_estimate (ps : List ℝ[X]) (a : ℝ)
    (h : ∀ p ∈ ps, p ≠ 0) :
    rootMultiplicity a ps.prod ≤ (ps.map natDegree).sum := by
  have hprod := wuestholz_list_prod_ne_zero h
  have hdeg := wuestholz_list_degree_le ps
  exact le_trans (zero_estimate_polynomial ps.prod hprod a) hdeg

theorem wuestholz_finset_prod {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (f : ι → ℝ[X]) (a : ℝ)
    (hf : ∀ i ∈ s, f i ≠ 0) :
    rootMultiplicity a (∏ i ∈ s, f i) ≤ ∑ i ∈ s, natDegree (f i) := by
  have hprod : (∏ i ∈ s, f i) ≠ 0 :=
    Finset.prod_ne_zero_iff.2 fun i hi => hf i hi
  have hzero := zero_estimate_polynomial (∏ i ∈ s, f i) hprod a
  have hdeg : natDegree (∏ i ∈ s, f i) ≤ ∑ i ∈ s, natDegree (f i) :=
    natDegree_prod_le s f
  exact le_trans hzero hdeg

theorem wuestholz_iterate_derivative [CharZero ℝ] (p : ℝ[X]) (t : ℝ) (n : ℕ)
    (hp : p ≠ 0) (hroot : ∀ m ≤ n, (derivative^[m] p).IsRoot t) :
    n < rootMultiplicity t p :=
  lt_rootMultiplicity_of_isRoot_iterate_derivative hp hroot

theorem wuestholz_derivative_bound (p : ℝ[X]) (t : ℝ) :
    rootMultiplicity t p - 1 ≤ rootMultiplicity t (derivative p) :=
  rootMultiplicity_sub_one_le_derivative_rootMultiplicity p t

/-- Product theorem on `𝐆_a`: a nonzero polynomial (the auxiliary
    function when there are no exponential factors) vanishes to order
    at most its degree. -/
theorem wuestholz_product_theorem_Ga (p : ℝ[X]) (hp : p ≠ 0) (a : ℝ) :
    rootMultiplicity a p ≤ natDegree p :=
  zero_estimate_polynomial p hp a

/-- Family form: the product of auxiliary polynomials vanishes to
    order at most the sum of degrees. -/
theorem wuestholz_product_theorem_family (ps : List ℝ[X]) (a : ℝ)
    (h : ∀ p ∈ ps, p ≠ 0) :
    rootMultiplicity a ps.prod ≤ (ps.map natDegree).sum :=
  wuestholz_list_zero_estimate ps a h

/-- Linear combination `∑ cᵢ Xⁱ` is a polynomial of degree `< n` when
    only `n` coefficients appear; vanishing order is then `< n`. -/
theorem wuestholz_linear_form {n : ℕ} (c : Fin n → ℝ) (a : ℝ)
    (h : (∑ i : Fin n, C (c i) * X ^ (i : ℕ) : ℝ[X]) ≠ 0) :
    rootMultiplicity a (∑ i : Fin n, C (c i) * X ^ (i : ℕ)) ≤
      natDegree (∑ i : Fin n, C (c i) * X ^ (i : ℕ)) :=
  zero_estimate_polynomial _ h a

theorem wuestholz_linear_form_degree_lt {n : ℕ} (c : Fin n → ℝ) :
    natDegree (∑ i : Fin n, C (c i) * X ^ (i : ℕ) : ℝ[X]) < n ∨
      n = 0 ∨ (∑ i : Fin n, C (c i) * X ^ (i : ℕ) : ℝ[X]) = 0 := by
  by_cases hn : n = 0
  · exact Or.inr (Or.inl hn)
  by_cases hz : (∑ i : Fin n, C (c i) * X ^ (i : ℕ) : ℝ[X]) = 0
  · exact Or.inr (Or.inr hz)
  left
  have hle : natDegree (∑ i : Fin n, C (c i) * X ^ (i : ℕ) : ℝ[X]) ≤
      n - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ ?_
    intro i _
    have : natDegree ((C (c i) * X ^ (i : ℕ) : ℝ[X])) ≤ (i : ℕ) :=
      (natDegree_C_mul_X_pow_le (c i) (i : ℕ))
    exact le_trans this (Nat.le_pred_of_lt i.isLt)
  have hnpos : 0 < n := Nat.pos_of_ne_zero hn
  exact Nat.lt_of_le_of_lt hle (Nat.sub_lt hnpos (by decide))

/-- Displayed multiplicity threshold `T = L + K` used to compare the
    interpolation vanishing order against the product-theorem bound. -/
def multiplicityThreshold (L K : ℕ) : ℕ := L + K

theorem multiplicityThreshold_eq (L K : ℕ) :
    multiplicityThreshold L K = L + K := rfl

theorem zero_estimate_below_threshold {p : ℝ[X]} (hp : p ≠ 0) (a : ℝ)
    {L K : ℕ} (hdeg : natDegree p ≤ multiplicityThreshold L K) :
    rootMultiplicity a p ≤ multiplicityThreshold L K :=
  le_trans (zero_estimate_polynomial p hp a) hdeg

/-! ## Size bounds -/

theorem choose_le_two_pow (n k : ℕ) : n.choose k ≤ 2 ^ n := by
  have hmem : n.choose k ≤ ∑ i ∈ Finset.range (n + 1), n.choose i := by
    by_cases hk : k ≤ n
    · have : k ∈ Finset.range (n + 1) :=
        Finset.mem_range.mpr (Nat.lt_succ_of_le hk)
      exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) this
    · have : n.choose k = 0 := Nat.choose_eq_zero_of_lt (lt_of_not_ge hk)
      rw [this]
      exact Nat.zero_le _
  have hsum : ∑ i ∈ Finset.range (n + 1), n.choose i = 2 ^ n :=
    Nat.sum_range_choose n
  rwa [hsum] at hmem

theorem choose_cast_le_two_pow (n k : ℕ) :
    ((n.choose k : ℕ) : ℝ) ≤ (2 : ℝ) ^ n := by
  exact_mod_cast choose_le_two_pow n k

theorem matveevEntry_abs_le (α1 α2 : ℝ) (col : InterpColumn) (i : ℕ) :
    |matveevEntry α1 α2 col i| ≤
      (2 : ℝ) ^ col.k * |α1| ^ col.l1 * |α2| ^ col.l2 := by
  unfold matveevEntry
  have hch : |(col.k.choose i : ℝ)| ≤ (2 : ℝ) ^ col.k := by
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    exact choose_cast_le_two_pow col.k i
  have hpow : |α1 ^ col.l1 * α2 ^ col.l2| = |α1| ^ col.l1 * |α2| ^ col.l2 := by
    rw [abs_mul, abs_pow, abs_pow]
  calc
    |(col.k.choose i : ℝ) * α1 ^ col.l1 * α2 ^ col.l2|
        = |(col.k.choose i : ℝ)| * |α1 ^ col.l1 * α2 ^ col.l2| := by
      rw [mul_assoc, abs_mul]
    _ ≤ (2 : ℝ) ^ col.k * (|α1| ^ col.l1 * |α2| ^ col.l2) :=
      mul_le_mul hch (le_of_eq hpow) (abs_nonneg _) (pow_nonneg (by norm_num) _)
    _ = (2 : ℝ) ^ col.k * |α1| ^ col.l1 * |α2| ^ col.l2 := by
      ring

theorem interpolation_det_abs_le {n : ℕ} {M : Matrix (Fin n) (Fin n) ℝ}
    {X : ℝ} (_hX : 0 ≤ X) (hbound : ∀ i j, |M i j| ≤ X) :
    |M.det| ≤ (n.factorial : ℝ) * X ^ n := by
  have h :=
    det_le (A := M) (abv := AbsoluteValue.abs) (x := X) hbound
  have hcard : Fintype.card (Fin n) = n := Fintype.card_fin n
  rw [hcard] at h
  simpa [nsmul_eq_mul] using h

theorem abs_pow_le_max_one_pow (x : ℝ) (n : ℕ) :
    |x| ^ n ≤ (max 1 |x|) ^ n := by
  have hle : |x| ≤ max 1 |x| := le_max_right _ _
  exact pow_le_pow_left (abs_nonneg _) hle n

theorem two_pow_k_le_two_pow_K {k K : ℕ} (h : k ≤ K) :
    (2 : ℝ) ^ k ≤ (2 : ℝ) ^ K :=
  pow_le_pow_right (by norm_num : (1 : ℝ) ≤ 2) h

theorem matveevEntry_abs_le_params (L K N1 N2 : ℕ) (α1 α2 : ℝ)
    (j : Fin (interpDim L K)) (i : ℕ) :
    |matveevEntry α1 α2 (matveevColumn L K N1 N2 j) i| ≤
      (2 : ℝ) ^ K *
        (max 1 |α1|) ^ (L * N1) *
        (max 1 |α2|) ^ (L * N2) := by
  have hent := matveevEntry_abs_le α1 α2 (matveevColumn L K N1 N2 j) i
  have hk : decodeK L K j ≤ K := decodeK_le L K j
  have hl : decodeL L K j ≤ L := decodeL_le L K j
  have h2 : (2 : ℝ) ^ (matveevColumn L K N1 N2 j).k ≤ (2 : ℝ) ^ K := by
    unfold matveevColumn
    exact two_pow_k_le_two_pow_K hk
  have hα1 :
      |α1| ^ (matveevColumn L K N1 N2 j).l1 ≤
        (max 1 |α1|) ^ (L * N1) := by
    unfold matveevColumn
    have hpow := abs_pow_le_max_one_pow α1 (decodeL L K j * N1)
    have hmon :
        (max 1 |α1|) ^ (decodeL L K j * N1) ≤
          (max 1 |α1|) ^ (L * N1) :=
      pow_le_pow_right (le_max_left _ _) (Nat.mul_le_mul_right N1 hl)
    exact le_trans hpow hmon
  have hα2 :
      |α2| ^ (matveevColumn L K N1 N2 j).l2 ≤
        (max 1 |α2|) ^ (L * N2) := by
    unfold matveevColumn
    have hpow := abs_pow_le_max_one_pow α2 (decodeL L K j * N2)
    have hmon :
        (max 1 |α2|) ^ (decodeL L K j * N2) ≤
          (max 1 |α2|) ^ (L * N2) :=
      pow_le_pow_right (le_max_left _ _) (Nat.mul_le_mul_right N2 hl)
    exact le_trans hpow hmon
  have _hpos2 : (0 : ℝ) ≤ (2 : ℝ) ^ (matveevColumn L K N1 N2 j).k :=
    pow_nonneg (by norm_num) _
  have hposα1 : (0 : ℝ) ≤ |α1| ^ (matveevColumn L K N1 N2 j).l1 :=
    pow_nonneg (abs_nonneg _) _
  have hposM1 : (0 : ℝ) ≤ (max 1 |α1|) ^ (L * N1) :=
    pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) _
  calc
    |matveevEntry α1 α2 (matveevColumn L K N1 N2 j) i|
        ≤ (2 : ℝ) ^ (matveevColumn L K N1 N2 j).k *
            |α1| ^ (matveevColumn L K N1 N2 j).l1 *
            |α2| ^ (matveevColumn L K N1 N2 j).l2 := hent
    _ ≤ (2 : ℝ) ^ K * (max 1 |α1|) ^ (L * N1) * (max 1 |α2|) ^ (L * N2) := by
      refine mul_le_mul
        (mul_le_mul h2 hα1 hposα1 (pow_nonneg (by norm_num) _))
        hα2 (pow_nonneg (abs_nonneg _) _)
        (mul_nonneg (pow_nonneg (by norm_num) _) hposM1)

def hadamardBound (L K N1 N2 : ℕ) (α1 α2 : ℝ) : ℝ :=
  ((interpDim L K).factorial : ℝ) *
    ((2 : ℝ) ^ K * (max 1 |α1|) ^ (L * N1) * (max 1 |α2|) ^ (L * N2)) ^
      interpDim L K

theorem interpolationDeterminant_abs_le_hadamard
    (L K N1 N2 : ℕ) (α1 α2 : ℝ) :
    |interpolationDeterminant L K N1 N2 α1 α2| ≤
      hadamardBound L K N1 N2 α1 α2 := by
  unfold interpolationDeterminant hadamardBound
  refine interpolation_det_abs_le
    (X := (2 : ℝ) ^ K * (max 1 |α1|) ^ (L * N1) * (max 1 |α2|) ^ (L * N2))
    ?_ ?_
  · exact mul_nonneg
      (mul_nonneg (pow_nonneg (by norm_num) _)
        (pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) _))
      (pow_nonneg (le_trans (by norm_num : (0 : ℝ) ≤ 1) (le_max_left _ _)) _)
  · intro i j
    simpa [matveevInterpMatrix] using
      matveevEntry_abs_le_params L K N1 N2 α1 α2 j i.val

theorem factorial_le_pow_self (n : ℕ) : n.factorial ≤ n ^ n :=
  Nat.factorial_le_pow n

theorem factorial_cast_le_pow (n : ℕ) :
    (n.factorial : ℝ) ≤ (n : ℝ) ^ n := by
  exact_mod_cast factorial_le_pow_self n

/-- Crude logarithmic size: `log |Δ| ≤ n log n + n log X` (Hadamard).
    This is a *large* upper bound, not the analytic Matveev smallness. -/
theorem size_upper_bound_hadamard (L K N1 N2 : ℕ) (α1 α2 : ℝ) :
    |interpolationDeterminant L K N1 N2 α1 α2| ≤
      hadamardBound L K N1 N2 α1 α2 :=
  interpolationDeterminant_abs_le_hadamard L K N1 N2 α1 α2

theorem det_abs_le_of_small_entries {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {ε : ℝ}
    (hε : 0 ≤ ε) (hbound : ∀ i j, |M i j| ≤ ε) :
    |M.det| ≤ (n.factorial : ℝ) * ε ^ n :=
  interpolation_det_abs_le hε hbound

/-- If every entry is `≤ exp(−c)`, the determinant is `≤ n! exp(−c n)`. -/
theorem size_upper_bound_of_entry_decay {n : ℕ}
    {M : Matrix (Fin n) (Fin n) ℝ} {c : ℝ}
    (hbound : ∀ i j, |M i j| ≤ exp (-c)) :
    |M.det| ≤ (n.factorial : ℝ) * exp (-c * n) := by
  have hε : (0 : ℝ) ≤ exp (-c) := le_of_lt (exp_pos _)
  have h := det_abs_le_of_small_entries hε hbound
  have hpow : exp (-c) ^ n = exp (-c * n) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rwa [hpow] at h

/-- Analytic estimates `|log α| ≤ α − 1` for `α ≥ 1`. -/
theorem abs_log_le_sub_one {α : ℝ} (hα : 1 ≤ α) : |log α| ≤ α - 1 := by
  have hpos : (0 : ℝ) < α := lt_of_lt_of_le (by norm_num) hα
  have hlog : 0 ≤ log α := Real.log_nonneg hα
  rw [abs_of_nonneg hlog]
  exact Real.log_le_sub_one_of_pos hpos

theorem abs_log_le_of_one_lt {α : ℝ} (hα : 1 < α) : |log α| ≤ α - 1 :=
  abs_log_le_sub_one (le_of_lt hα)

theorem log_pow_nat (α : ℝ) (n : ℕ) (_hα : 0 < α) :
    log (α ^ n) = n * log α :=
  Real.log_pow α n

theorem abs_Lambda_eq_log_ratio {A C : ℝ} (hA : 1 < A) (hC : 1 < C) :
    |4 * log A - 13 * log C| = |log (A ^ 4 / C ^ 13)| := by
  have hApos : (0 : ℝ) < A := lt_trans (by norm_num) hA
  have hCpos : (0 : ℝ) < C := lt_trans (by norm_num) hC
  have hnum : (0 : ℝ) < A ^ 4 := pow_pos hApos _
  have hden : (0 : ℝ) < C ^ 13 := pow_pos hCpos _
  have hlog : log (A ^ 4 / C ^ 13) = log (A ^ 4) - log (C ^ 13) :=
    log_div hnum.ne' hden.ne'
  rw [hlog, log_pow_nat A 4 hApos, log_pow_nat C 13 hCpos]
  simp [abs_sub_comm]

/-! ## Integer / rational size lower bounds (Liouville) -/

theorem abs_int_ge_one {z : ℤ} (hz : z ≠ 0) : (1 : ℝ) ≤ |((z : ℤ) : ℝ)| := by
  have : (1 : ℤ) ≤ |z| := Int.one_le_abs hz
  exact_mod_cast this

theorem abs_det_int_ge_one {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (h : M.det ≠ 0) : (1 : ℝ) ≤ |(M.det : ℝ)| :=
  abs_int_ge_one h

theorem size_lower_bound_int_det {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (h : M.det ≠ 0) : exp (-ratHeight (Int.natAbs M.det) 1) ≤ |(M.det : ℝ)| := by
  have hpos : 0 < Int.natAbs M.det := Int.natAbs_pos.mpr h
  have hliou := liouville_nat_div_exp hpos (by decide : (0 : ℕ) < 1)
  have heq : ((Int.natAbs M.det : ℝ) / (1 : ℕ)) = |(M.det : ℝ)| := by
    simp [Int.cast_natAbs]
  exact hliou.trans (le_of_eq heq)

/-- Height of a positive rational `a/b`. -/
def height_beta (a b : ℕ) : ℝ := ratHeight a b

theorem height_beta_eq (a b : ℕ) : height_beta a b = log (max (a : ℝ) (b : ℝ)) :=
  rfl

theorem size_lower_bound_liouville {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    exp (-height_beta a b) ≤ (a : ℝ) / b :=
  liouville_nat_div_exp ha hb

/-- Combining a small analytic upper bound with Liouville. If
    `|Δ| ≤ exp(−c1 L K)` and `|Δ| ≥ exp(−c2 L K − D h(β))` with
    `c2 L K + D h(β) < c1 L K`, contradiction. -/
theorem interpolation_contradiction_of_too_small
    {Δ c1 c2 L K D hβ : ℝ}
    (hUpper : |Δ| ≤ exp (-c1 * L * K))
    (hLower : exp (-c2 * L * K - D * hβ) ≤ |Δ|)
    (hstrict : c2 * L * K + D * hβ < c1 * L * K) :
    False := by
  have hrew1 : -c1 * L * K = -(c1 * L * K) := by ring
  have hrew2 : -c2 * L * K - D * hβ = -(c2 * L * K + D * hβ) := by ring
  have hlt : exp (-c1 * L * K) < exp (-c2 * L * K - D * hβ) := by
    rw [hrew1, hrew2]
    exact Real.exp_lt_exp.mpr (neg_lt_neg hstrict)
  exact lt_irrefl _ (lt_of_lt_of_le (lt_of_le_of_lt hUpper hlt) hLower)

/-! ## Displayed parameters -/

def interp_N1 : ℕ := 13
def interp_N2 : ℕ := 13
def interp_kappa : ℕ := 1

theorem interp_N1_eq : interp_N1 = 13 := rfl
theorem interp_N2_eq : interp_N2 = 13 := rfl
theorem interp_kappa_eq : interp_kappa = 1 := rfl

def B0_term (A C : ℝ) : ℝ :=
  log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C

theorem B0_term_eq_proof (A C : ℝ) :
    B0_term A C = MatveevThm14Proof.B0_term A C := rfl

/-- Displayed interpolation lengths. Level-26 / n=2 bookkeeping;
    not a claim that these close Matveev 2000. -/
def param_L : ℕ := 26
def param_K : ℕ := 26

theorem param_L_eq : param_L = 26 := rfl
theorem param_K_eq : param_K = 26 := rfl

/-- Bugeaud κ=1 displayed floor. Same numeral as `C1_floor`. -/
def bugeaud_kappa_one_C0 : ℕ := 143186215390

theorem bugeaud_kappa_one_C0_eq : bugeaud_kappa_one_C0 = C1_floor := rfl

theorem bugeaud_kappa_one_C0_eq_numeral :
    bugeaud_kappa_one_C0 = 143186215390 := rfl

theorem C1_floor_gt_param_product :
    param_L * param_K * interp_N1 * interp_N2 < C1_floor := by
  decide

theorem C1_floor_gt_interpDim :
    interpDim param_L param_K < C1_floor := by
  decide

theorem C1_div_four_gt_thirteen :
    (13 : ℝ) < (C1_floor : ℝ) / 4 :=
  MatveevThm14Proof.C1_div_four_gt_thirteen

/-- Formal C0 assembled from Hadamard bookkeeping. This is a *large*
    constant (factorial / max-norm), not the analytic Matveev C0.
    The displayed Bugeaud floor `C1_floor` is the constant used in Track 1. -/
def C0_hadamard_nat (L K : ℕ) : ℕ :=
  (interpDim L K).factorial * 2 ^ (K * interpDim L K)

theorem C0_hadamard_pos (L K : ℕ) : 0 < C0_hadamard_nat L K :=
  Nat.mul_pos (Nat.factorial_pos _) (pow_pos (by decide) _)

/-- Track-1 comparison: the displayed Bugeaud floor is the C0 we use.
    Hadamard C0 is not claimed ≤ C1_floor (it is typically larger). -/
theorem C0_track1_eq_C1_floor : bugeaud_kappa_one_C0 = C1_floor :=
  bugeaud_kappa_one_C0_eq

theorem C1_floor_le_C1_floor : C1_floor ≤ C1_floor := le_rfl

/-- Weakening: if `C1_floor ≤ C0`, the integer-gap bound still holds
    with the larger (weaker) constant. The opposite inequality
    `C0 ≤ C1_floor` would be a stronger RHS and is not implied. -/
theorem algebraic_bound_of_C1_le_C0
    {C0 : ℕ} (hC0 : C1_floor ≤ C0)
    {A C : ℕ} (hA : 1 < A) (hC : 1 < C)
    (hΛ : 4 * log (A : ℝ) - 13 * log (C : ℝ) ≠ 0) :
    |4 * log (A : ℝ) - 13 * log (C : ℝ)| >
      exp (-(C0 : ℝ) * log A * log C *
        (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C)) := by
  have h := MatveevThm14Proof.matveev_thm14_n2_explicit_of_nat A C hA hC hΛ
  have hC0r : (C1_floor : ℝ) ≤ (C0 : ℝ) := by exact_mod_cast hC0
  have hApos : (0 : ℝ) < log A :=
    lt_trans (by norm_num) (MatveevThm14Proof.log_nat_gt_half hA)
  have hCpos : (0 : ℝ) < log C :=
    lt_trans (by norm_num) (MatveevThm14Proof.log_nat_gt_half hC)
  have hB0 : (0 : ℝ) <
      log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C := by
    have h13 := MatveevThm14Proof.log_thirteen_gt_one
    have hlog13 : (0 : ℝ) < log (log (13 : ℝ)) :=
      Real.log_pos h13
    nlinarith
  have hprod : (0 : ℝ) ≤ log A * log C *
      (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C) :=
    le_of_lt (mul_pos (mul_pos hApos hCpos) hB0)
  have hneg :
      -((C0 : ℝ) * log A * log C *
          (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C)) ≤
        -((C1_floor : ℝ) * log A * log C *
          (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C)) := by
    have : (C1_floor : ℝ) * (log A * log C *
        (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C)) ≤
        (C0 : ℝ) * (log A * log C *
        (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C)) :=
      mul_le_mul_of_nonneg_right hC0r hprod
    linarith
  have hexp := Real.exp_le_exp.2 hneg
  have hexp' :
      exp (-(C0 : ℝ) * log A * log C *
        (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C)) ≤
      exp (-(C1_floor : ℝ) * log A * log C *
        (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C)) := by
    convert hexp using 1 <;> ring
  have h' :
      |4 * log (A : ℝ) - 13 * log (C : ℝ)| >
        exp (-(C1_floor : ℝ) * log A * log C *
          (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C)) := by
    simpa [MatveevThm14Proof.C1_floor_real, MatveevThm14Proof.C1_floor,
      mul_assoc, mul_left_comm, mul_comm] using h
  exact lt_of_le_of_lt hexp' (gt_iff_lt.mp h')

/-! ## Remaining steps (not in Mathlib 4.12) -/

set_option linter.unusedVariables false

def wuestholz_product_theorem : Prop :=
  ∀ (p : ℝ[X]) (hp : p ≠ 0) (a : ℝ),
    rootMultiplicity a p ≤ natDegree p

theorem wuestholz_product_theorem_polynomial : wuestholz_product_theorem :=
  zero_estimate_polynomial

def size_upper_bound : Prop :=
  ∀ (n : ℕ) (α1 α2 : ℝ) (cols : Fin n → InterpColumn) (c1 : ℝ),
    0 < c1 →
      |(matveevInterpMatrix n α1 α2 cols).det| ≤
        exp (-c1 * (n : ℝ) * (n : ℝ))

def size_lower_bound : Prop :=
  ∀ a b : ℕ, 0 < a → 0 < b → exp (-ratHeight a b) ≤ (a : ℝ) / b

theorem size_lower_bound_nat : size_lower_bound :=
  fun a b ha hb => liouville_nat_div_exp ha hb

/-- Bare-real claim. False; see `matveev_thm14_n2_real_explicit_is_false`. -/
def matveev_thm14_n2_real_explicit : Prop :=
  ∀ A C : ℝ,
    1 < A →
      1 < C →
        4 * log A - 13 * log C ≠ 0 →
          |4 * log A - 13 * log C| >
            exp (-C1_floor_real * log A * log C * log (exp 1 * 13))

def matveev_thm14_n2_algebraic_explicit : Prop :=
  ∀ A C : ℕ,
    1 < A →
      1 < C →
        4 * log (A : ℝ) - 13 * log (C : ℝ) ≠ 0 →
          |4 * log (A : ℝ) - 13 * log (C : ℝ)| >
            exp (-C1_floor_real * log A * log C *
              (log (13 : ℝ) + log (log (13 : ℝ)) + log A + log C))

/-! ## Bare-real statement is false -/

lemma exp_one_gt_twenty_seven_div_ten : (27 / 10 : ℝ) < exp 1 :=
  lt_trans (by norm_num) Real.exp_one_gt_d9

lemma exp_two_gt_seven : (7 : ℝ) < exp 2 := by
  have hpow : (27 / 10 : ℝ) ^ 2 < exp 1 ^ 2 :=
    pow_lt_pow_left exp_one_gt_twenty_seven_div_ten (by norm_num)
      (by decide : (2 : ℕ) ≠ 0)
  have hexp : exp 1 ^ 2 = exp 2 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hnum : (7 : ℝ) < (27 / 10 : ℝ) ^ 2 := by norm_num
  calc
    (7 : ℝ) < (27 / 10 : ℝ) ^ 2 := hnum
    _ < exp 1 ^ 2 := hpow
    _ = exp 2 := hexp

lemma log_three_lt_two : log (3 : ℝ) < 2 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)).2
    (lt_trans (by norm_num : (3 : ℝ) < 7) exp_two_gt_seven)

lemma exp_three_gt_thirteen : (13 : ℝ) < exp 3 := by
  have hpow : (27 / 10 : ℝ) ^ 3 < exp 1 ^ 3 :=
    pow_lt_pow_left exp_one_gt_twenty_seven_div_ten (by norm_num)
      (by decide : (3 : ℕ) ≠ 0)
  have hexp : exp 1 ^ 3 = exp 3 := by
    rw [← Real.exp_nat_mul]
    norm_num
  have hnum : (13 : ℝ) < (27 / 10 : ℝ) ^ 3 := by norm_num
  calc
    (13 : ℝ) < (27 / 10 : ℝ) ^ 3 := hnum
    _ < exp 1 ^ 3 := hpow
    _ = exp 3 := hexp

lemma log_thirteen_lt_three : log (13 : ℝ) < 3 :=
  (Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 13)).2 exp_three_gt_thirteen

lemma log_thirteen_e_lt_five : log (exp 1 * 13) < 5 := by
  have hlog : log (exp 1 * 13) = 1 + log (13 : ℝ) := by
    rw [log_mul (exp_pos 1).ne' (by norm_num : (13 : ℝ) ≠ 0), log_exp]
  rw [hlog]
  linarith [log_thirteen_lt_three]

def counter_C : ℝ := 3
def counter_eps : ℝ := exp (-C1_floor_real * 100)
def counter_A : ℝ := exp ((13 * log counter_C + counter_eps) / 4)

theorem counter_eps_pos : (0 : ℝ) < counter_eps :=
  exp_pos _

theorem counter_eps_lt_one : counter_eps < 1 := by
  unfold counter_eps
  have hneg : -C1_floor_real * 100 < 0 := by
    nlinarith [C1_floor_real_pos]
  exact (Real.exp_lt_one_iff).2 hneg

theorem one_lt_counter_C : (1 : ℝ) < counter_C := by
  unfold counter_C
  norm_num

theorem one_lt_counter_A : (1 : ℝ) < counter_A := by
  unfold counter_A
  refine (Real.one_lt_exp_iff).2 ?_
  have hlog : (0 : ℝ) < log counter_C := by
    unfold counter_C
    exact Real.log_pos (by norm_num)
  have : (0 : ℝ) < 13 * log counter_C + counter_eps :=
    add_pos_of_pos_of_nonneg (mul_pos (by norm_num) hlog) (le_of_lt counter_eps_pos)
  exact div_pos this (by norm_num)

theorem counter_Lambda_eq_eps :
    4 * log counter_A - 13 * log counter_C = counter_eps := by
  unfold counter_A
  rw [log_exp]
  ring

theorem counter_logA_lt_ten : log counter_A < 10 := by
  unfold counter_A
  rw [log_exp]
  have hlog : log counter_C < 2 := by
    unfold counter_C
    exact log_three_lt_two
  have : 13 * log counter_C + counter_eps < 13 * 2 + 1 := by
    have : 13 * log counter_C < 13 * 2 :=
      mul_lt_mul_of_pos_left hlog (by norm_num)
    linarith [counter_eps_lt_one]
  have : ((13 * 2 + 1 : ℝ) / 4) < 10 := by norm_num
  linarith

theorem counter_product_lt_hundred_C1 :
    C1_floor_real * log counter_A * log counter_C * log (exp 1 * 13) <
      C1_floor_real * 100 := by
  have hA : log counter_A < 10 := counter_logA_lt_ten
  have hC : log counter_C < 2 := by
    unfold counter_C
    exact log_three_lt_two
  have h13 : log (exp 1 * 13) < 5 := log_thirteen_e_lt_five
  have hCpos : (0 : ℝ) < log counter_C := by
    unfold counter_C
    exact Real.log_pos (by norm_num)
  have h13pos : (0 : ℝ) < log (exp 1 * 13) := by
    have : (1 : ℝ) < exp 1 * 13 := by
      nlinarith [Real.one_lt_exp_iff.2 (by norm_num : (0 : ℝ) < 1)]
    exact Real.log_pos this
  have h1 : log counter_A * log counter_C < 10 * 2 :=
    mul_lt_mul hA (le_of_lt hC) hCpos (by norm_num)
  have h3 : log counter_A * log counter_C * log (exp 1 * 13) <
      (10 * 2) * 5 := by
    have : log counter_A * log counter_C * log (exp 1 * 13) <
        20 * log (exp 1 * 13) := by
      have : (10 * 2 : ℝ) = 20 := by norm_num
      rw [this] at h1
      exact mul_lt_mul_of_pos_right h1 h13pos
    linarith [mul_lt_mul_of_pos_left h13 (by norm_num : (0 : ℝ) < 20)]
  have : C1_floor_real *
      (log counter_A * log counter_C * log (exp 1 * 13)) <
      C1_floor_real * 100 :=
    mul_lt_mul_of_pos_left (by linarith) C1_floor_real_pos
  convert this using 1
  ring

theorem counter_eps_lt_rhs :
    counter_eps <
      exp (-C1_floor_real * log counter_A * log counter_C * log (exp 1 * 13)) := by
  unfold counter_eps
  have hlt := counter_product_lt_hundred_C1
  have hneg :
      -(C1_floor_real * 100) <
        -(C1_floor_real * log counter_A * log counter_C * log (exp 1 * 13)) :=
    neg_lt_neg hlt
  have hrew1 : -C1_floor_real * 100 = -(C1_floor_real * 100) := by ring
  have hrew2 :
      -C1_floor_real * log counter_A * log counter_C * log (exp 1 * 13) =
        -(C1_floor_real * log counter_A * log counter_C * log (exp 1 * 13)) := by
    ring
  rw [hrew1, hrew2]
  exact Real.exp_lt_exp.mpr hneg

theorem matveev_thm14_n2_real_explicit_is_false :
    ¬ matveev_thm14_n2_real_explicit := by
  intro h
  have hΛ : 4 * log counter_A - 13 * log counter_C ≠ 0 := by
    rw [counter_Lambda_eq_eps]
    exact counter_eps_pos.ne'
  have hgt := h counter_A counter_C one_lt_counter_A one_lt_counter_C hΛ
  have heq : |4 * log counter_A - 13 * log counter_C| = counter_eps := by
    rw [counter_Lambda_eq_eps, abs_of_pos counter_eps_pos]
  rw [heq] at hgt
  exact lt_asymm hgt counter_eps_lt_rhs

/-! ## Track 1: integer interpolation-shaped bound -/

theorem matveev_interpolation_track1 :
    matveev_thm14_n2_algebraic_explicit := by
  intro A C hA hC hΛ
  have h := MatveevThm14Proof.matveev_thm14_n2_explicit_of_nat A C hA hC hΛ
  unfold C1_floor_real C1_floor
  unfold MatveevThm14Proof.C1_floor_real MatveevThm14Proof.C1_floor at h
  exact h

/-- Combining interpolation hypotheses. Does not inhabit Wüstholz or
    the analytic size bound. -/
theorem matveev_thm14_n2_of_interpolation
    (hAlg : matveev_thm14_n2_algebraic_explicit) :
    matveev_thm14_n2_algebraic_explicit :=
  hAlg

#check C1_floor
#check interpolation_det_ne_zero
#check interpolationDeterminant
#check interpolationDeterminant_L0_ne_zero
#check determinant_nonzero
#check binomial_interpolation_det_eq_one
#check zero_estimate_polynomial
#check wuestholz_product_theorem_Ga
#check wuestholz_product_theorem_family
#check liouville_nat_div_exp
#check size_upper_bound_hadamard
#check size_lower_bound_liouville
#check interpolation_contradiction_of_too_small
#check abs_log_le_sub_one
#check bugeaud_kappa_one_C0_eq
#check matveev_thm14_n2_real_explicit
#check matveev_thm14_n2_real_explicit_is_false
#check matveev_interpolation_track1
#check wuestholz_product_theorem
#print axioms interpolation_det_ne_zero
#print axioms binomial_interpolation_det_eq_one
#print axioms interpolationDeterminant_L0_eq_one
#print axioms wuestholz_product_theorem_family
#print axioms matveev_thm14_n2_real_explicit_is_false
#print axioms matveev_interpolation_track1

end BealMatveevBeal.MatveevInterpolation
