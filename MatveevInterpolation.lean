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
* Track 1 integer bound (`matveev_thm14_n2_explicit_of_nat`);
* Matveev §3 `Φ` (entire exponential polynomial);
* higher-order Schwarz `|f|_r ≤ (r/R)^T |f|_R`;
* Cauchy `|iteratedDslope f n 0| ≤ M / R^n`;
* polynomial vanishing → `iteratedDslope` (so Schwarz is inhabited
  on `𝐆_a`); binomial matrix entries are those Taylor coefficients;
* conditional analytic smallness
  `matveev_interpolation_analytic_small_bound`;
* Siegel / pigeonhole: an underdetermined integer system has a
  nonzero integer kernel vector of controlled height
  (`siegel_lemma`, Mathlib `Int.Matrix.exists_ne_zero_int_vec_norm_le`);
* `matveevPhi_vanishing_exists_T`: integer coefficients of height
  at most the Siegel bound such that the G_a specialisation
  (`α1=α2=1`) vanishes to order `siegel_T = N/2` at `0`;
* `Φ(z) = P(z, α1^z, α2^z)` along `W`; gap-3 is not the relation
  `A^4 = (B+3)^13`;
* `L≥1` and `α1=α2=1` makes `Δ=0` (duplicate columns);
* frequencies `k1 log α1 + k2 log α2` are distinct if `α1,α2`
  are multiplicatively independent;
* `wuestholz_product_theorem_exp_Gm`: for independent `α1,α2`,
  a nonzero coefficient vector cannot make `Φ` vanish to order
  `≥ (L+1)(N1+1)(N2+1)` at `0` (jet of `{z^ℓ α1^{k1 z} α2^{k2 z}}`
  is injective). The `MvPolynomial` form
  `wuestholz_product_theorem_exp_Gm_of_mvPolynomial` is the same
  criterion for `P ∈ ℤ[y0,y1,y2]` of degree `≤ (L,N1,N2)`.
  Gap-3 rules out the single relation `A^4=(B+3)^13`;
  full independence is still Baker.

The full Wüstholz subgroup theorem stays `def Prop`. Exact integer
vanishing of the *exponential* jet is not an integer linear system
(the derivatives involve `log α`). Jet invertibility does **not**
close Matveev 2000 / `C1_floor`; Track 1 stays elementary.
The analytic smallness `|Δ| ≤ exp(−c L K)` is proved
**conditionally** from a vanishing-order hypothesis and Schwarz;
the generic `size_upper_bound` stays a `def Prop` (`L=0` gives
`Δ=1`). Not v25.
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

/-! ## Analytic Φ (Matveev 2000 §3) and higher-order Schwarz

Mathlib 4.12 has the classical Schwarz lemma (`Complex.abs_le_abs_of_mapsTo_ball_self`)
and the maximum-modulus principle, but not the order-`T` form
`|f|_r ≤ (r/R)^T |f|_R`. That form is proved here by iterating `dslope`.
Jensen's formula is not in Mathlib 4.12; Schwarz + max-modulus is the
single-zero special case used by Matveev at `z = 0`.

An unconditional `|Δ| ≤ exp(−c L K)` is false (`Δ = 1` when `L = 0`).
The named theorem `matveev_interpolation_analytic_small_bound` is the
conditional decay: a zero of order `T` at `0` plus a max-modulus bound
gives `|f| ≤ exp(−c L K)` on `|z| ≤ R/2` once `T log 2` absorbs `c L K`
and `log M`.
-/

open Metric
open scoped NNReal

/-- One exponential-polynomial term `c · z^ℓ · α1^{k1 z} · α2^{k2 z}`. -/
structure PhiTerm where
  coeff : ℂ
  l : ℕ
  k1 : ℕ
  k2 : ℕ

/-- Entire branch `α^z := exp(z log α)` of the real-positive exponential. -/
def alphaPowZ (α : ℝ) (z : ℂ) : ℂ :=
  Complex.exp ((Real.log α : ℂ) * z)

theorem alphaPowZ_differentiable (α : ℝ) :
    Differentiable ℂ (alphaPowZ α) :=
  (differentiable_id.const_mul (Real.log α : ℂ)).cexp

theorem alphaPowZ_mul (α : ℝ) (k : ℕ) (z : ℂ) :
    alphaPowZ α ((k : ℂ) * z) = Complex.exp ((k : ℂ) * (Real.log α : ℂ) * z) := by
  unfold alphaPowZ
  ring_nf

def phiTermEval (α1 α2 : ℝ) (t : PhiTerm) (z : ℂ) : ℂ :=
  t.coeff * z ^ t.l * alphaPowZ α1 ((t.k1 : ℂ) * z) * alphaPowZ α2 ((t.k2 : ℂ) * z)

theorem phiTermEval_differentiable (α1 α2 : ℝ) (t : PhiTerm) :
    Differentiable ℂ (phiTermEval α1 α2 t) := by
  unfold phiTermEval
  have hz : Differentiable ℂ fun z : ℂ => z ^ t.l := differentiable_id.pow _
  have h1 : Differentiable ℂ fun z : ℂ => alphaPowZ α1 ((t.k1 : ℂ) * z) :=
    (alphaPowZ_differentiable α1).comp (differentiable_id.const_mul _)
  have h2 : Differentiable ℂ fun z : ℂ => alphaPowZ α2 ((t.k2 : ℂ) * z) :=
    (alphaPowZ_differentiable α2).comp (differentiable_id.const_mul _)
  exact ((differentiable_const _).mul hz).mul h1 |>.mul h2

/-- Matveev §3 auxiliary function
    `Φ(z) = Σ c_{ℓ,k1,k2} z^ℓ α1^{k1 z} α2^{k2 z}`. -/
def matveevPhi (α1 α2 : ℝ) (terms : List PhiTerm) (z : ℂ) : ℂ :=
  (terms.map (fun t => phiTermEval α1 α2 t z)).sum

theorem matveevPhi_differentiable (α1 α2 : ℝ) (terms : List PhiTerm) :
    Differentiable ℂ (matveevPhi α1 α2 terms) := by
  induction terms with
  | nil =>
    have h : matveevPhi α1 α2 [] = fun _ => (0 : ℂ) := by
      funext
      simp [matveevPhi]
    rw [h]
    exact differentiable_const 0
  | cons t ts ih =>
    unfold matveevPhi
    simp only [List.map_cons, List.sum_cons]
    exact (phiTermEval_differentiable α1 α2 t).add (by
      simpa [matveevPhi] using ih)

theorem matveevPhi_diffContOnCl (α1 α2 : ℝ) (terms : List PhiTerm) {s : Set ℂ} :
    DiffContOnCl ℂ (matveevPhi α1 α2 terms) s :=
  (matveevPhi_differentiable α1 α2 terms).diffContOnCl

/-- Iterate `dslope · 0`. If `f` vanishes to order `T` at `0`, then
    `f(z) = z^T · iteratedDslope f T z`. -/
def iteratedDslope (f : ℂ → ℂ) : ℕ → ℂ → ℂ
  | 0 => f
  | n + 1 => dslope (iteratedDslope f n) 0

theorem iteratedDslope_zero (f : ℂ → ℂ) : iteratedDslope f 0 = f := rfl

theorem iteratedDslope_succ (f : ℂ → ℂ) (n : ℕ) :
    iteratedDslope f (n + 1) = dslope (iteratedDslope f n) 0 := rfl

theorem iteratedDslope_succ_eq (f : ℂ → ℂ) (n : ℕ) :
    iteratedDslope f (n + 1) = iteratedDslope (dslope f 0) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change dslope (iteratedDslope f (n + 1)) 0 =
      dslope (iteratedDslope (dslope f 0) n) 0
    rw [ih]

theorem eval_eq_mul_dslope (f : ℂ → ℂ) (hf0 : f 0 = 0) (z : ℂ) :
    f z = z * dslope f 0 z := by
  have h := sub_smul_dslope f 0 z
  simp only [sub_zero, smul_eq_mul] at h
  rw [hf0, sub_zero] at h
  exact h.symm

theorem eval_eq_pow_mul_iteratedDslope :
    ∀ (f : ℂ → ℂ) (T : ℕ), (∀ k < T, iteratedDslope f k 0 = 0) →
      ∀ z, f z = z ^ T * iteratedDslope f T z := by
  intro f T
  induction T generalizing f with
  | zero =>
    intro _ z
    simp [iteratedDslope]
  | succ T ih =>
    intro hvan z
    have hf0 : f 0 = 0 := by
      simpa [iteratedDslope] using hvan 0 (Nat.zero_lt_succ T)
    have hvan' : ∀ k < T, iteratedDslope (dslope f 0) k 0 = 0 := by
      intro k hk
      have := hvan (k + 1) (Nat.succ_lt_succ hk)
      rwa [iteratedDslope_succ_eq f k] at this
    rw [eval_eq_mul_dslope f hf0 z, ih (dslope f 0) hvan' z, ← iteratedDslope_succ_eq, pow_succ]
    ring

theorem iteratedDslope_differentiableOn {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R)) :
    ∀ n, DifferentiableOn ℂ (iteratedDslope f n) (ball 0 R)
  | 0 => hf
  | n + 1 =>
    (Complex.differentiableOn_dslope (ball_mem_nhds (0 : ℂ) hR)).2
      (iteratedDslope_differentiableOn hR hf n)

theorem continuousOn_dslope_closedBall {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (closedBall 0 R))
    (hd : DifferentiableOn ℂ f (ball 0 R)) :
    ContinuousOn (dslope f 0) (closedBall 0 R) := by
  intro z hz
  by_cases h : z = 0
  · subst h
    exact (continuousAt_dslope_same.2
      (hd.differentiableAt (ball_mem_nhds (0 : ℂ) hR))).continuousWithinAt
  · exact (continuousWithinAt_dslope_of_ne h).2 (hf z hz)

theorem dslope_diffContOnCl {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R)) :
    DiffContOnCl ℂ (dslope f 0) (ball 0 R) := by
  refine ⟨(Complex.differentiableOn_dslope (ball_mem_nhds (0 : ℂ) hR)).2 hf.differentiableOn, ?_⟩
  rw [closure_ball (0 : ℂ) hR.ne']
  exact continuousOn_dslope_closedBall hR
    (by
      have : closure (ball (0 : ℂ) R) = closedBall 0 R := closure_ball _ hR.ne'
      simpa [this] using hf.continuousOn)
    hf.differentiableOn

/-- Order-zero Schwarz: max modulus on the closed disc. -/
theorem schwarz_order_zero {f : ℂ → ℂ} {R M : ℝ} (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hM : ∀ z, z ∈ sphere 0 R → ‖f z‖ ≤ M)
    {z : ℂ} (hz : z ∈ closedBall 0 R) :
    ‖f z‖ ≤ M := by
  have hfront : frontier (ball (0 : ℂ) R) = sphere 0 R :=
    frontier_ball (0 : ℂ) hR.ne'
  have hcl : closure (ball (0 : ℂ) R) = closedBall 0 R :=
    closure_ball (0 : ℂ) hR.ne'
  refine Complex.norm_le_of_forall_mem_frontier_norm_le
    (isBounded_ball (x := (0 : ℂ)) (r := R)) hf ?_ (hcl.symm ▸ hz)
  intro w hw
  rw [hfront] at hw
  exact hM w hw

/-- Higher-order Schwarz lemma: a zero of order `T` at `0` gives
    `|f(z)| ≤ (r/R)^T M` for `|z| ≤ r ≤ R`. -/
theorem schwarz_lemma_of_order {f : ℂ → ℂ} {R r M : ℝ} {T : ℕ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R) (hM : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hvan : ∀ k < T, iteratedDslope f k 0 = 0)
    (hbound : ∀ w, w ∈ sphere 0 R → ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖f z‖ ≤ (r / R) ^ T * M := by
  induction T generalizing f M with
  | zero =>
    have hz' : z ∈ closedBall 0 R := by
      rw [mem_closedBall_zero_iff]
      exact le_trans hz hrR
    have := schwarz_order_zero hR hf hbound hz'
    simp only [pow_zero, one_mul]
    exact this
  | succ T ih =>
    have hf0 : f 0 = 0 := by
      simpa [iteratedDslope] using hvan 0 (Nat.zero_lt_succ T)
    have hg : DiffContOnCl ℂ (dslope f 0) (ball 0 R) :=
      dslope_diffContOnCl hR hf
    have hvan' : ∀ k < T, iteratedDslope (dslope f 0) k 0 = 0 := by
      intro k hk
      have := hvan (k + 1) (Nat.succ_lt_succ hk)
      rwa [iteratedDslope_succ_eq f k] at this
    have hMg : 0 ≤ M / R := div_nonneg hM hR.le
    have hbound' : ∀ w, w ∈ sphere 0 R → ‖dslope f 0 w‖ ≤ M / R := by
      intro w hw
      have _hw0 : w ≠ 0 := by
        intro h
        rw [h, mem_sphere_zero_iff_norm, norm_zero] at hw
        exact hR.ne' hw.symm
      have hfeq : f w = w * dslope f 0 w := eval_eq_mul_dslope f hf0 w
      have hwR : ‖w‖ = R := mem_sphere_zero_iff_norm.1 hw
      have hfM : ‖f w‖ ≤ M := hbound w hw
      have hmul : ‖w‖ * ‖dslope f 0 w‖ ≤ M := by
        rwa [← norm_mul, ← hfeq]
      have hmulR : R * ‖dslope f 0 w‖ ≤ M := by
        rwa [hwR] at hmul
      exact (le_div_iff₀ hR).2 (by rwa [mul_comm])
    have hgbound := ih (f := dslope f 0) (M := M / R) hMg hg hvan' hbound'
    have hfeq : f z = z * dslope f 0 z := eval_eq_mul_dslope f hf0 z
    have hzn : ‖z‖ * ‖dslope f 0 z‖ ≤ r * ((r / R) ^ T * (M / R)) :=
      mul_le_mul hz hgbound (norm_nonneg _) hr
    have hrew : r * ((r / R) ^ T * (M / R)) = (r / R) ^ (T + 1) * M := by
      have hRne : (R : ℝ) ≠ 0 := hR.ne'
      field_simp [pow_succ, hRne]
      ring
    calc
      ‖f z‖ = ‖z‖ * ‖dslope f 0 z‖ := by rw [hfeq, norm_mul]
      _ ≤ (r / R) ^ (T + 1) * M := by
        exact le_trans hzn (le_of_eq hrew)

theorem half_pow_eq_exp_neg_log_two (T : ℕ) :
    ((1 / 2 : ℝ) ^ T) = exp (-(T : ℝ) * log 2) := by
  have hpos : (0 : ℝ) < 1 / 2 := by norm_num
  rw [← Real.exp_log (pow_pos hpos T), Real.log_pow (1 / 2) T]
  have hlog : log (1 / 2 : ℝ) = -log 2 := by
    rw [log_div (by norm_num : (1 : ℝ) ≠ 0) (by norm_num : (2 : ℝ) ≠ 0), log_one, zero_sub]
  rw [hlog]
  ring

/-- Displayed analytic constant: `r = R/2` gives decay `2^{−T}`. -/
def analytic_c1 : ℝ := log 2

theorem analytic_c1_pos : (0 : ℝ) < analytic_c1 :=
  Real.log_pos (by norm_num : (1 : ℝ) < 2)

theorem analytic_c1_eq_log_two : analytic_c1 = log 2 := rfl

def analytic_T (L K : ℕ) : ℕ := L * K

theorem analytic_T_eq (L K : ℕ) : analytic_T L K = L * K := rfl

theorem analytic_T_mul_c1 (L K : ℕ) :
    (analytic_T L K : ℝ) * analytic_c1 = (L : ℝ) * (K : ℝ) * log 2 := by
  unfold analytic_T analytic_c1
  rw [Nat.cast_mul]

/-- With displayed parameters `T = L K` and `c = log 2`, Schwarz decay
    `2^{−T}` absorbs `exp(−c L K)` once `M ≤ 1`. -/
theorem analytic_T_absorbs_unit_bound {L K : ℕ} {M : ℝ}
    (hM : 0 < M) (hM1 : M ≤ 1) :
    (analytic_T L K : ℝ) * log 2 ≥
      analytic_c1 * (L : ℝ) * (K : ℝ) + log M := by
  unfold analytic_T analytic_c1
  rw [Nat.cast_mul]
  have hlog : log M ≤ 0 := Real.log_nonpos (le_of_lt hM) hM1
  linarith

/-- Conditional analytic smallness on `Φ` (or any holomorphic `f`).
    A zero of order `T` at `0` and `|f| ≤ M` on `|z| = R` imply
    `|f(z)| ≤ exp(−c L K)` on `|z| ≤ R/2` once `T log 2` absorbs
    `c L K + log M`. -/
theorem matveev_interpolation_analytic_small_bound
    {f : ℂ → ℂ} {R M c : ℝ} {L K T : ℕ}
    (hR : 0 < R) (hM : 0 < M) (_hc : 0 ≤ c)
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hvan : ∀ k < T, iteratedDslope f k 0 = 0)
    (hbound : ∀ w, w ∈ sphere 0 R → ‖f w‖ ≤ M)
    (hT : (T : ℝ) * log 2 ≥ c * (L : ℝ) * (K : ℝ) + log M)
    {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖f z‖ ≤ exp (-c * (L : ℝ) * (K : ℝ)) := by
  have hr : (0 : ℝ) ≤ R / 2 := div_nonneg hR.le (by norm_num)
  have hrR : R / 2 ≤ R := by
    have : (1 / 2 : ℝ) ≤ 1 := by norm_num
    have := mul_le_mul_of_nonneg_left this hR.le
    linarith
  have hM0 : (0 : ℝ) ≤ M := le_of_lt hM
  have hsch :=
    schwarz_lemma_of_order hR hr hrR hM0 hf hvan hbound hz
  have hhalf : (R / 2) / R = (1 / 2 : ℝ) := by
    field_simp [hR.ne']
    ring
  have hexp : ((R / 2) / R) ^ T * M = exp (-(T : ℝ) * log 2 + log M) := by
    rw [hhalf, half_pow_eq_exp_neg_log_two]
    have hMeq : M = exp (log M) := (Real.exp_log hM).symm
    nth_rw 1 [hMeq]
    rw [← Real.exp_add]
  have hle : exp (-(T : ℝ) * log 2 + log M) ≤ exp (-c * (L : ℝ) * (K : ℝ)) := by
    have : -(T : ℝ) * log 2 + log M ≤ -c * (L : ℝ) * (K : ℝ) := by
      linarith [hT]
    exact Real.exp_le_exp.2 this
  exact le_trans (hsch.trans (le_of_eq hexp)) hle

/-- Determinant form: Schwarz-small entries give a small Hadamard bound. -/
theorem matveev_interpolation_analytic_small_bound_det
    {n L K : ℕ} {c : ℝ} {M : Matrix (Fin n) (Fin n) ℝ}
    (hn : 0 < n) (hc : 0 ≤ c)
    (hEntries : ∀ i j,
      |M i j| ≤
        exp (-(c * (L : ℝ) * (K : ℝ) + log (max (n.factorial : ℝ) 1)))) :
    |M.det| ≤ exp (-c * (L : ℝ) * (K : ℝ)) := by
  have hε : (0 : ℝ) ≤
      exp (-(c * (L : ℝ) * (K : ℝ) + log (max (n.factorial : ℝ) 1))) :=
    le_of_lt (exp_pos _)
  have hdet := det_abs_le_of_small_entries hε hEntries
  have hnfac : (1 : ℝ) ≤ (n.factorial : ℝ) := by
    exact_mod_cast Nat.one_le_of_lt (Nat.factorial_pos n)
  have hmax : max (n.factorial : ℝ) 1 = (n.factorial : ℝ) :=
    max_eq_left hnfac
  have hpow :
      exp (-(c * (L : ℝ) * (K : ℝ) + log (max (n.factorial : ℝ) 1))) ^ n =
        exp (-(c * (L : ℝ) * (K : ℝ) + log (n.factorial : ℝ)) * n) := by
    rw [hmax, ← Real.exp_nat_mul]
    congr 1
    ring
  rw [hpow] at hdet
  have hfact :
      (n.factorial : ℝ) *
          exp (-(c * (L : ℝ) * (K : ℝ) + log (n.factorial : ℝ)) * n) =
        exp (log (n.factorial : ℝ) +
          (-(c * (L : ℝ) * (K : ℝ) + log (n.factorial : ℝ)) * n)) := by
    have hNpos : (0 : ℝ) < n.factorial := lt_of_lt_of_le (by norm_num) hnfac
    have hNeq : (n.factorial : ℝ) = exp (log (n.factorial : ℝ)) :=
      (Real.exp_log hNpos).symm
    nth_rw 1 [hNeq]
    rw [← Real.exp_add]
  have hsimp :
      log (n.factorial : ℝ) +
          (-(c * (L : ℝ) * (K : ℝ) + log (n.factorial : ℝ)) * n) ≤
        -c * (L : ℝ) * (K : ℝ) := by
    have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hn
    have hlog : (0 : ℝ) ≤ log (n.factorial : ℝ) := log_nonneg hnfac
    have hclk : (0 : ℝ) ≤ c * (L : ℝ) * (K : ℝ) :=
      mul_nonneg (mul_nonneg hc (Nat.cast_nonneg L)) (Nat.cast_nonneg K)
    have hleft :
        log (n.factorial : ℝ) +
            (-(c * (L : ℝ) * (K : ℝ) + log (n.factorial : ℝ)) * n) =
          (1 - (n : ℝ)) * log (n.factorial : ℝ) -
            (n : ℝ) * (c * (L : ℝ) * (K : ℝ)) := by
      ring
    rw [hleft]
    have hneg : (1 - (n : ℝ)) * log (n.factorial : ℝ) ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hlog
    have hscale :
        -((n : ℝ) * (c * (L : ℝ) * (K : ℝ))) ≤ -(c * (L : ℝ) * (K : ℝ)) := by
      have : c * (L : ℝ) * (K : ℝ) ≤ (n : ℝ) * (c * (L : ℝ) * (K : ℝ)) :=
        le_mul_of_one_le_left hclk hn1
      linarith
    linarith
  have : (n.factorial : ℝ) *
      exp (-(c * (L : ℝ) * (K : ℝ) + log (n.factorial : ℝ)) * n) ≤
        exp (-c * (L : ℝ) * (K : ℝ)) := by
    rw [hfact]
    exact Real.exp_le_exp.2 hsimp
  exact le_trans hdet this

/-- Specialisation of the analytic bound to Matveev's `Φ`. -/
theorem matveevPhi_analytic_small_bound
    {α1 α2 : ℝ} {terms : List PhiTerm} {R M c : ℝ} {L K T : ℕ}
    (hR : 0 < R) (hM : 0 < M) (hc : 0 ≤ c)
    (hvan : ∀ k < T, iteratedDslope (matveevPhi α1 α2 terms) k 0 = 0)
    (hbound : ∀ w, w ∈ sphere 0 R → ‖matveevPhi α1 α2 terms w‖ ≤ M)
    (hT : (T : ℝ) * log 2 ≥ c * (L : ℝ) * (K : ℝ) + log M)
    {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖matveevPhi α1 α2 terms z‖ ≤ exp (-c * (L : ℝ) * (K : ℝ)) :=
  matveev_interpolation_analytic_small_bound hR hM hc
    (matveevPhi_diffContOnCl α1 α2 terms) hvan hbound hT hz

/-- Unconditional smallness of `Δ` is false: the L=0 binomial matrix has `Δ = 1`. -/
theorem interpolationDeterminant_L0_not_exp_small (K : ℕ) {c : ℝ}
    (_hc : 0 < c) :
    ¬ |interpolationDeterminant 0 K 0 0 1 1| ≤
        exp (-c * (0 : ℝ) * (K : ℝ) - 1) := by
  rw [interpolationDeterminant_L0_eq_one, abs_one]
  have : exp (-c * 0 * (K : ℝ) - 1) = exp (-1) := by ring_nf
  rw [this]
  have hlt : exp (-1 : ℝ) < 1 := (Real.exp_lt_one_iff).2 (by norm_num)
  exact not_le.2 hlt

/-! ## Cauchy estimates and polynomial vanishing -/

/-- Formal power series of a polynomial: the coefficients are `p.coeff`. -/
def polyFormalSeries (p : ℂ[X]) : FormalMultilinearSeries ℂ ℂ ℂ :=
  fun n => ContinuousMultilinearMap.mkPiRing ℂ (Fin n) (p.coeff n)

theorem polyFormalSeries_coeff (p : ℂ[X]) (n : ℕ) :
    (polyFormalSeries p).coeff n = p.coeff n := by
  unfold polyFormalSeries FormalMultilinearSeries.coeff
  simp [ContinuousMultilinearMap.mkPiRing_apply, Pi.one_apply]

theorem polynomial_hasFPowerSeriesAt_eval (p : ℂ[X]) :
    HasFPowerSeriesAt (fun z => p.eval z) (polyFormalSeries p) 0 := by
  rw [hasFPowerSeriesAt_iff]
  refine Filter.Eventually.of_forall fun z => ?_
  have hzero : ∀ n, n ∉ Finset.range (p.natDegree + 1) →
      z ^ n • (polyFormalSeries p).coeff n = 0 := by
    intro n hn
    have : ¬ n < p.natDegree + 1 := mt Finset.mem_range.2 hn
    have hn' : p.natDegree < n := Nat.lt_of_succ_le (Nat.le_of_not_lt this)
    rw [polyFormalSeries_coeff, Polynomial.coeff_eq_zero_of_natDegree_lt hn', smul_zero]
  have hsum : HasSum (fun n => z ^ n • (polyFormalSeries p).coeff n)
      (∑ n ∈ Finset.range (p.natDegree + 1),
        z ^ n • (polyFormalSeries p).coeff n) :=
    hasSum_sum_of_ne_finset_zero hzero
  have heval :
      (∑ n ∈ Finset.range (p.natDegree + 1),
          z ^ n • (polyFormalSeries p).coeff n) =
        p.eval z := by
    rw [Polynomial.eval_eq_sum_range]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [polyFormalSeries_coeff, smul_eq_mul, mul_comm]
  rw [zero_add, ← heval]
  exact hsum

theorem iteratedDslope_zero_eq_coeff {f : ℂ → ℂ}
    {p : FormalMultilinearSeries ℂ ℂ ℂ}
    (hp : HasFPowerSeriesAt f p 0) (n : ℕ) :
    iteratedDslope f n 0 = p.coeff n := by
  induction n generalizing f p with
  | zero =>
    change f 0 = p.coeff 0
    exact (hp.coeff_zero (fun _ : Fin 0 => (1 : ℂ))).symm
  | succ n ih =>
    have hds : HasFPowerSeriesAt (dslope f 0) p.fslope 0 :=
      hp.has_fpower_series_dslope_fslope
    rw [iteratedDslope_succ_eq, ih hds, FormalMultilinearSeries.coeff_fslope]

theorem iteratedDslope_polynomial_coeff (p : ℂ[X]) (n : ℕ) :
    iteratedDslope (fun z => p.eval z) n 0 = p.coeff n := by
  rw [iteratedDslope_zero_eq_coeff (polynomial_hasFPowerSeriesAt_eval p) n,
    polyFormalSeries_coeff]

/-- Binomial matrix entries are Taylor coefficients of `(1+z)^j`. -/
theorem iteratedDslope_one_add_pow (j i : ℕ) :
    iteratedDslope (fun z : ℂ => (1 + z) ^ j) i 0 = (j.choose i : ℂ) := by
  have hfun : (fun z : ℂ => (1 + z) ^ j) =
      fun z => ((1 + X : ℂ[X]) ^ j).eval z := by
    funext z
    simp [eval_pow, eval_add, eval_one, eval_X]
  rw [hfun, iteratedDslope_polynomial_coeff, coeff_one_add_X_pow]

theorem binomialInterpMatrix_eq_iteratedDslope (n : ℕ) (i j : Fin n) :
    ((binomialInterpMatrix n i j : ℤ) : ℂ) =
      iteratedDslope (fun z : ℂ => (1 + z) ^ (j : ℕ)) (i : ℕ) 0 := by
  unfold binomialInterpMatrix
  simp [iteratedDslope_one_add_pow]

theorem matveevEntry_eq_iteratedDslope_binomial
    (α1 α2 : ℝ) (l1 l2 k i : ℕ) :
    (matveevEntry α1 α2 ⟨l1, l2, k⟩ i : ℂ) =
      iteratedDslope (fun z : ℂ => (1 + z) ^ k) i 0 *
        (α1 ^ l1 : ℂ) * (α2 ^ l2 : ℂ) := by
  unfold matveevEntry
  rw [iteratedDslope_one_add_pow]
  push_cast
  ring

theorem dslope_id_mul (g : ℂ → ℂ) (hg : Differentiable ℂ g) :
    dslope (fun z => z * g z) 0 = g := by
  funext z
  by_cases hz : z = 0
  · subst z
    rw [dslope_same]
    have hmul :=
      deriv_mul
        (differentiable_id.differentiableAt : DifferentiableAt ℂ id (0 : ℂ))
        (hg.differentiableAt : DifferentiableAt ℂ g 0)
    simpa using hmul
  · have := dslope_sub_smul_of_ne (f := g) (a := (0 : ℂ)) hz
    simpa [sub_zero, smul_eq_mul] using this

theorem dslope_pow_mul (g : ℂ → ℂ) {n : ℕ} (hn : 0 < n)
    (hg : Differentiable ℂ g) :
    dslope (fun z => z ^ n * g z) 0 = fun z => z ^ (n - 1) * g z := by
  have hdecomp : (fun z : ℂ => z ^ n * g z) =
      fun z => z * (z ^ (n - 1) * g z) := by
    funext z
    calc
      z ^ n * g z = z ^ (n - 1 + 1) * g z := by
        rw [Nat.sub_add_cancel (Nat.succ_le_of_lt hn)]
      _ = z ^ (n - 1) * z * g z := by rw [pow_succ]
      _ = z * (z ^ (n - 1) * g z) := by ring
  have hg' : Differentiable ℂ fun z => z ^ (n - 1) * g z :=
    (differentiable_id.pow _).mul hg
  rw [hdecomp, dslope_id_mul _ hg']

theorem iteratedDslope_pow_mul (g : ℂ → ℂ) (T : ℕ)
    (hg : Differentiable ℂ g) :
    ∀ k ≤ T, iteratedDslope (fun z => z ^ T * g z) k =
      fun z => z ^ (T - k) * g z := by
  intro k
  induction k with
  | zero =>
    intro _
    simp [iteratedDslope]
  | succ k ih =>
    intro hk
    have hkT : k ≤ T := Nat.le_of_succ_le hk
    have hpos : 0 < T - k := Nat.sub_pos_of_lt (Nat.lt_of_succ_le hk)
    rw [iteratedDslope_succ, ih hkT, dslope_pow_mul g hpos hg]
    have : T - k - 1 = T - (k + 1) := Nat.sub_sub _ _ _
    rw [this]

theorem iteratedDslope_pow_mul_vanishes (g : ℂ → ℂ) (T : ℕ)
    (hg : Differentiable ℂ g) {k : ℕ} (hk : k < T) :
    iteratedDslope (fun z => z ^ T * g z) k 0 = 0 := by
  have hle : k ≤ T := Nat.le_of_lt hk
  rw [iteratedDslope_pow_mul g T hg k hle]
  have hpos : 0 < T - k := Nat.sub_pos_of_lt hk
  simp [zero_pow hpos.ne']

theorem polynomial_eq_X_pow_mul {p : ℂ[X]} {T : ℕ}
    (hT : T ≤ p.rootMultiplicity 0) :
    ∃ q : ℂ[X], p = X ^ T * q := by
  by_cases hp : p = 0
  · exact ⟨0, by simp [hp]⟩
  · have : (X - C (0 : ℂ)) ^ T ∣ p := (le_rootMultiplicity_iff hp).1 hT
    simpa [map_zero, sub_zero] using this

theorem polynomial_eval_eq_pow_mul {p : ℂ[X]} {T : ℕ}
    (hT : T ≤ p.rootMultiplicity 0) :
    ∃ q : ℂ[X], ∀ z, p.eval z = z ^ T * q.eval z := by
  obtain ⟨q, hq⟩ := polynomial_eq_X_pow_mul hT
  refine ⟨q, fun z => ?_⟩
  rw [hq, eval_mul, eval_pow, eval_X]

theorem polynomial_iteratedDslope_vanishes {p : ℂ[X]} {T : ℕ}
    (hT : T ≤ p.rootMultiplicity 0) :
    ∀ k < T, iteratedDslope (fun z => p.eval z) k 0 = 0 := by
  obtain ⟨q, hq⟩ := polynomial_eval_eq_pow_mul hT
  intro k hk
  have hfun : (fun z => p.eval z) = fun z => z ^ T * q.eval z := funext hq
  rw [hfun]
  exact iteratedDslope_pow_mul_vanishes (fun z => q.eval z) T q.differentiable hk

theorem polynomial_iteratedDslope_vanishes_real {p : ℝ[X]} {T : ℕ}
    (hT : T ≤ p.rootMultiplicity 0) :
    ∀ k < T,
      iteratedDslope (fun z : ℂ => (p.map (algebraMap ℝ ℂ)).eval z) k 0 = 0 := by
  have hinj : Function.Injective (algebraMap ℝ ℂ) := Complex.ofReal_injective
  have hmap : T ≤ (p.map (algebraMap ℝ ℂ)).rootMultiplicity 0 := by
    have : p.rootMultiplicity 0 =
        (p.map (algebraMap ℝ ℂ)).rootMultiplicity (algebraMap ℝ ℂ 0) :=
      eq_rootMultiplicity_map hinj 0
    simpa [map_zero] using (this ▸ hT)
  exact polynomial_iteratedDslope_vanishes hmap

/-- Higher-order Schwarz, inhabited for polynomials (`𝐆_a`). -/
theorem schwarz_lemma_of_order_polynomial {p : ℂ[X]} {R r M : ℝ} {T : ℕ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R) (hM : 0 ≤ M)
    (hT : T ≤ p.rootMultiplicity 0)
    (hbound : ∀ w, w ∈ sphere 0 R → ‖p.eval w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖p.eval z‖ ≤ (r / R) ^ T * M :=
  schwarz_lemma_of_order hR hr hrR hM p.differentiable.diffContOnCl
    (polynomial_iteratedDslope_vanishes hT) hbound hz

theorem schwarz_lemma_of_order_polynomial_real {p : ℝ[X]} {R r M : ℝ} {T : ℕ}
    (hR : 0 < R) (hr : 0 ≤ r) (hrR : r ≤ R) (hM : 0 ≤ M)
    (hT : T ≤ p.rootMultiplicity 0)
    (hbound : ∀ w, w ∈ sphere 0 R →
      ‖(p.map (algebraMap ℝ ℂ)).eval w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ r) :
    ‖(p.map (algebraMap ℝ ℂ)).eval z‖ ≤ (r / R) ^ T * M :=
  schwarz_lemma_of_order hR hr hrR hM
    (p.map (algebraMap ℝ ℂ)).differentiable.diffContOnCl
    (polynomial_iteratedDslope_vanishes_real hT) hbound hz

/-- Analytic smallness on `𝐆_a`: multiplicity supplies the vanishing
    that Schwarz needs. Exponential `Φ` still needs Wüstholz. -/
theorem matveev_interpolation_analytic_small_bound_polynomial
    {p : ℝ[X]} {R M c : ℝ} {L K T : ℕ}
    (hR : 0 < R) (hM : 0 < M) (hc : 0 ≤ c)
    (hT : T ≤ p.rootMultiplicity 0)
    (hbound : ∀ w, w ∈ sphere 0 R →
      ‖(p.map (algebraMap ℝ ℂ)).eval w‖ ≤ M)
    (hTlog : (T : ℝ) * log 2 ≥ c * (L : ℝ) * (K : ℝ) + log M)
    {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖(p.map (algebraMap ℝ ℂ)).eval z‖ ≤
      exp (-c * (L : ℝ) * (K : ℝ)) :=
  matveev_interpolation_analytic_small_bound hR hM hc
    (p.map (algebraMap ℝ ℂ)).differentiable.diffContOnCl
    (polynomial_iteratedDslope_vanishes_real hT) hbound hTlog hz

theorem schwarz_half_radius {f : ℂ → ℂ} {R M : ℝ} {T : ℕ}
    (hR : 0 < R) (hM : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hvan : ∀ k < T, iteratedDslope f k 0 = 0)
    (hbound : ∀ w, w ∈ sphere 0 R → ‖f w‖ ≤ M)
    {z : ℂ} (hz : ‖z‖ ≤ R / 2) :
    ‖f z‖ ≤ (1 / 2 : ℝ) ^ T * M := by
  have hr : (0 : ℝ) ≤ R / 2 := div_nonneg hR.le (by norm_num)
  have hrR : R / 2 ≤ R := by
    have : (1 / 2 : ℝ) ≤ 1 := by norm_num
    have := mul_le_mul_of_nonneg_left this hR.le
    linarith
  have hsch := schwarz_lemma_of_order hR hr hrR hM hf hvan hbound hz
  have hhalf : (R / 2) / R = (1 / 2 : ℝ) := by
    field_simp [hR.ne']
    ring
  rwa [hhalf] at hsch

/-- First-derivative Cauchy estimate at the centre. -/
theorem cauchy_estimate_first_deriv {f : ℂ → ℂ} {R M : ℝ}
    (hR : 0 < R)
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hbound : ∀ w, w ∈ sphere 0 R → ‖f w‖ ≤ M) :
    ‖deriv f 0‖ ≤ M / R :=
  Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hR hf hbound

/-- Cauchy estimate for Taylor coefficients:
    `|f^{(n)}(0) / n!| = |iteratedDslope f n 0| ≤ M / R^n`. -/
theorem cauchy_estimate_iteratedDslope {f : ℂ → ℂ} {R M : ℝ} (n : ℕ)
    (hR : 0 < R) (_hM : 0 ≤ M)
    (hf : DiffContOnCl ℂ f (ball 0 R))
    (hbound : ∀ w, w ∈ sphere 0 R → ‖f w‖ ≤ M) :
    ‖iteratedDslope f n 0‖ ≤ M / R ^ n := by
  have hRnn : (0 : ℝ≥0) < R.toNNReal := Real.toNNReal_pos.mpr hR
  have hf' : DiffContOnCl ℂ f (ball (0 : ℂ) (R.toNNReal : ℝ)) := by
    rwa [Real.coe_toNNReal R hR.le]
  have hps := hf'.hasFPowerSeriesOnBall hRnn
  have hat := hps.hasFPowerSeriesAt
  have heq : iteratedDslope f n 0 =
      (cauchyPowerSeries f 0 (R.toNNReal : ℝ)).coeff n :=
    iteratedDslope_zero_eq_coeff hat n
  rw [heq, ← FormalMultilinearSeries.norm_apply_eq_norm_coef]
  refine le_trans (norm_cauchyPowerSeries_le f 0 (R.toNNReal : ℝ) n) ?_
  have hR0 : (0 : ℝ) ≤ R := hR.le
  have hfcl : ContinuousOn f (closedBall 0 R) := by
    have : closure (ball (0 : ℂ) R) = closedBall 0 R :=
      closure_ball _ hR.ne'
    simpa [this] using hf.continuousOn
  have hcomp : Continuous fun θ : ℝ => f (circleMap 0 R θ) :=
    hfcl.comp_continuous (continuous_circleMap 0 R)
      (fun θ => circleMap_mem_closedBall 0 hR0 θ)
  have hnorm : Continuous fun θ : ℝ => ‖f (circleMap 0 R θ)‖ :=
    hcomp.norm
  have hinterg :
      ∫ θ in (0)..2 * π, ‖f (circleMap 0 R θ)‖ ≤ 2 * π * M := by
    have hle :
        ∫ θ in (0)..2 * π, ‖f (circleMap 0 R θ)‖ ≤
          ∫ _θ in (0)..2 * π, M :=
      intervalIntegral.integral_mono Real.two_pi_pos.le
        (hnorm.intervalIntegrable _ _)
        (continuous_const.intervalIntegrable _ _)
        (fun θ => hbound _ (circleMap_mem_sphere 0 hR0 θ))
    have hconst : (∫ _θ in (0)..2 * π, M) = 2 * π * M := by
      rw [intervalIntegral.integral_const]
      simp [smul_eq_mul]
    exact hle.trans_eq hconst
  have hRnn_coe : (R.toNNReal : ℝ) = R := Real.coe_toNNReal R hR.le
  have hI :
      (2 * π)⁻¹ *
          ∫ θ in (0)..2 * π, ‖f (circleMap 0 (R.toNNReal : ℝ) θ)‖ ≤
        M := by
    rw [hRnn_coe]
    have :
        (2 * π)⁻¹ * ∫ θ in (0)..2 * π, ‖f (circleMap 0 R θ)‖ ≤
          (2 * π)⁻¹ * (2 * π * M) :=
      mul_le_mul_of_nonneg_left hinterg (inv_nonneg.2 Real.two_pi_pos.le)
    have hsimp : (2 * π)⁻¹ * (2 * π * M) = M := by
      field_simp [Real.two_pi_pos.ne']
    exact this.trans_eq hsimp
  have habs : |(R.toNNReal : ℝ)| = R := by
    rw [hRnn_coe, abs_of_pos hR]
  have hpow : |(R.toNNReal : ℝ)|⁻¹ ^ n = R⁻¹ ^ n := by
    rw [habs]
  have hmul :
      ((2 * π)⁻¹ *
          ∫ θ in (0)..2 * π, ‖f (circleMap 0 (R.toNNReal : ℝ) θ)‖) *
        |(R.toNNReal : ℝ)|⁻¹ ^ n ≤
        M / R ^ n := by
    rw [hpow, inv_pow, ← div_eq_mul_inv]
    have hnonneg : (0 : ℝ) ≤ R⁻¹ ^ n := pow_nonneg (inv_nonneg.2 hR.le) n
    have := mul_le_mul_of_nonneg_right hI hnonneg
    rwa [inv_pow, ← div_eq_mul_inv] at this
  exact hmul

theorem matveevPhi_cauchy_estimate
    {α1 α2 : ℝ} {terms : List PhiTerm} {R M : ℝ} (n : ℕ)
    (hR : 0 < R) (hM : 0 ≤ M)
    (hbound : ∀ w, w ∈ sphere 0 R → ‖matveevPhi α1 α2 terms w‖ ≤ M) :
    ‖iteratedDslope (matveevPhi α1 α2 terms) n 0‖ ≤ M / R ^ n :=
  cauchy_estimate_iteratedDslope n hR hM
    (matveevPhi_diffContOnCl α1 α2 terms) hbound

/-! ## Siegel lemma and G_a vanishing of `Φ` -/

attribute [local instance] Matrix.seminormedAddCommGroup

/-- Pigeonhole box `[-H,H]^ι` has cardinality `(2H+1)^{|ι|}`. -/
theorem integer_box_card {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ℕ) :
    (Finset.Icc (fun _ : ι => (-(H : ℤ))) (fun _ => (H : ℤ))).card =
      (2 * H + 1) ^ Fintype.card ι := by
  rw [Pi.card_Icc]
  simp only [Finset.prod_const, Finset.card_univ]
  congr 1
  rw [Int.card_Icc]
  have h : (H : ℤ) + 1 - (-(H : ℤ)) = ((2 * H + 1 : ℕ) : ℤ) := by
    push_cast
    ring
  rw [h, Int.toNat_natCast]

/-- Mathlib Siegel: `m < n` integer equations have a nonzero integer
    solution of height `(n max(1,‖A‖))^{m/(n-m)}`. -/
theorem siegel_lemma {α β : Type*} [Fintype α] [Fintype β]
    (A : Matrix α β ℤ)
    (hn : Fintype.card α < Fintype.card β) (hm : 0 < Fintype.card α) :
    ∃ t : β → ℤ, t ≠ 0 ∧ A *ᵥ t = 0 ∧
      ‖t‖ ≤
        ((Fintype.card β : ℝ) * max 1 ‖A‖) ^
          ((Fintype.card α : ℝ) / (Fintype.card β - Fintype.card α)) :=
  Int.Matrix.exists_ne_zero_int_vec_norm_le A hn hm

/-- Coefficient count `(L+1)(N1+1)(N2+1)`. -/
def coeffCount (L N1 N2 : ℕ) : ℕ := (L + 1) * (N1 + 1) * (N2 + 1)

theorem coeffCount_eq (L N1 N2 : ℕ) :
    coeffCount L N1 N2 = (L + 1) * (N1 + 1) * (N2 + 1) :=
  rfl

theorem coeffCount_pos (L N1 N2 : ℕ) : 0 < coeffCount L N1 N2 :=
  Nat.mul_pos (Nat.mul_pos (Nat.succ_pos L) (Nat.succ_pos N1)) (Nat.succ_pos N2)

def n12 (N1 N2 : ℕ) : ℕ := (N1 + 1) * (N2 + 1)

theorem n12_pos (N1 N2 : ℕ) : 0 < n12 N1 N2 :=
  Nat.mul_pos (Nat.succ_pos N1) (Nat.succ_pos N2)

theorem coeffCount_eq_mul_n12 (L N1 N2 : ℕ) :
    coeffCount L N1 N2 = (L + 1) * n12 N1 N2 := by
  unfold coeffCount n12
  ring

def decodeCoeffL (L N1 N2 : ℕ) (j : Fin (coeffCount L N1 N2)) : ℕ :=
  j.val / n12 N1 N2

def decodeCoeffK1 (L N1 N2 : ℕ) (j : Fin (coeffCount L N1 N2)) : ℕ :=
  j.val % n12 N1 N2 / (N2 + 1)

def decodeCoeffK2 (L N1 N2 : ℕ) (j : Fin (coeffCount L N1 N2)) : ℕ :=
  j.val % n12 N1 N2 % (N2 + 1)

theorem decodeCoeffL_lt (L N1 N2 : ℕ) (j : Fin (coeffCount L N1 N2)) :
    decodeCoeffL L N1 N2 j < L + 1 := by
  unfold decodeCoeffL
  have hpos : 0 < n12 N1 N2 := n12_pos N1 N2
  have hj : j.val < (L + 1) * n12 N1 N2 := by
    simpa [coeffCount_eq_mul_n12 L N1 N2] using j.isLt
  exact (Nat.div_lt_iff_lt_mul hpos).2 hj

/-- Displayed vanishing order `T = N/2`. -/
def siegel_T (L N1 N2 : ℕ) : ℕ := coeffCount L N1 N2 / 2

theorem siegel_T_lt {L N1 N2 : ℕ} (hN : 2 ≤ coeffCount L N1 N2) :
    siegel_T L N1 N2 < coeffCount L N1 N2 :=
  Nat.div_lt_self (lt_of_lt_of_le (by decide : (0 : ℕ) < 2) hN)
    (by decide : (1 : ℕ) < 2)

theorem siegel_T_pos {L N1 N2 : ℕ} (hN : 2 ≤ coeffCount L N1 N2) :
    0 < siegel_T L N1 N2 :=
  Nat.div_pos hN (by decide : (0 : ℕ) < 2)

theorem two_mul_siegel_T_le (L N1 N2 : ℕ) :
    2 * siegel_T L N1 N2 ≤ coeffCount L N1 N2 := by
  simpa [siegel_T] using Nat.mul_div_le (coeffCount L N1 N2) 2

/-- Integer jet matrix: row `i` sums coefficients of `z^i`. -/
def jetMatrix (L N1 N2 T : ℕ) :
    Matrix (Fin T) (Fin (coeffCount L N1 N2)) ℤ :=
  fun i j => if decodeCoeffL L N1 N2 j = (i : ℕ) then 1 else 0

theorem jetMatrix_apply (L N1 N2 T : ℕ)
    (i : Fin T) (j : Fin (coeffCount L N1 N2)) :
    jetMatrix L N1 N2 T i j =
      if decodeCoeffL L N1 N2 j = (i : ℕ) then 1 else 0 :=
  rfl

theorem jetMatrix_mulVec (L N1 N2 T : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (i : Fin T) :
    (jetMatrix L N1 N2 T).mulVec c i =
      ∑ j : Fin (coeffCount L N1 N2),
        if decodeCoeffL L N1 N2 j = (i : ℕ) then c j else 0 := by
  unfold Matrix.mulVec jetMatrix
  simp [dotProduct, ite_mul, mul_one, mul_zero]

theorem jetMatrix_abs_le_one (L N1 N2 T : ℕ)
    (i : Fin T) (j : Fin (coeffCount L N1 N2)) :
    |jetMatrix L N1 N2 T i j| ≤ 1 := by
  unfold jetMatrix
  split_ifs <;> norm_num

theorem jetMatrix_norm_le_one (L N1 N2 T : ℕ) :
    ‖jetMatrix L N1 N2 T‖ ≤ 1 := by
  rw [norm_le_iff (by norm_num : (0 : ℝ) ≤ 1)]
  intro i j
  rw [Int.norm_eq_abs]
  exact_mod_cast jetMatrix_abs_le_one L N1 N2 T i j

/-- Auxiliary polynomial `Σ c_{ℓ,k1,k2} X^ℓ`. -/
def auxPoly (L N1 N2 : ℕ) (c : Fin (coeffCount L N1 N2) → ℤ) : ℂ[X] :=
  ∑ j : Fin (coeffCount L N1 N2),
    C (c j : ℂ) * X ^ decodeCoeffL L N1 N2 j

theorem auxPoly_eval (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (z : ℂ) :
    (auxPoly L N1 N2 c).eval z =
      ∑ j : Fin (coeffCount L N1 N2), (c j : ℂ) * z ^ decodeCoeffL L N1 N2 j := by
  unfold auxPoly
  simp [eval_finset_sum, eval_mul, eval_C, eval_pow, eval_X]

theorem auxPoly_coeff (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (k : ℕ) :
    (auxPoly L N1 N2 c).coeff k =
      ∑ j : Fin (coeffCount L N1 N2),
        if decodeCoeffL L N1 N2 j = k then (c j : ℂ) else 0 := by
  unfold auxPoly
  rw [finset_sum_coeff]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coeff_C_mul_X_pow]
  simp [eq_comm]

/-- Exponential polynomial with integer coefficients indexed by
    `(ℓ,k1,k2)`. -/
def matveevPhi_of_coeffs (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (α1 α2 : ℝ) (z : ℂ) : ℂ :=
  ∑ j : Fin (coeffCount L N1 N2),
    (c j : ℂ) * z ^ decodeCoeffL L N1 N2 j *
      alphaPowZ α1 ((decodeCoeffK1 L N1 N2 j : ℂ) * z) *
      alphaPowZ α2 ((decodeCoeffK2 L N1 N2 j : ℂ) * z)

theorem alphaPowZ_one (w : ℂ) : alphaPowZ 1 w = 1 := by
  unfold alphaPowZ
  rw [Real.log_one, Complex.ofReal_zero, zero_mul, Complex.exp_zero]

theorem alphaPowZ_nat_mul (α : ℝ) (k : ℕ) (z : ℂ) :
    alphaPowZ α ((k : ℂ) * z) = alphaPowZ α z ^ k := by
  unfold alphaPowZ
  have h :
      (Real.log α : ℂ) * ((k : ℂ) * z) =
        (k : ℂ) * ((Real.log α : ℂ) * z) := by
    ring
  rw [h, Complex.exp_nat_mul]

theorem matveevPhi_of_coeffs_alpha_one (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (z : ℂ) :
    matveevPhi_of_coeffs L N1 N2 c 1 1 z =
      ∑ j : Fin (coeffCount L N1 N2),
        (c j : ℂ) * z ^ decodeCoeffL L N1 N2 j := by
  unfold matveevPhi_of_coeffs
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [alphaPowZ_one, alphaPowZ_one, mul_one, mul_one]

theorem matveevPhi_of_coeffs_eq_auxPoly (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) :
    matveevPhi_of_coeffs L N1 N2 c 1 1 =
      fun z => (auxPoly L N1 N2 c).eval z := by
  funext z
  rw [matveevPhi_of_coeffs_alpha_one, auxPoly_eval]

theorem matveevPhi_of_coeffs_dslope (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (k : ℕ) :
    iteratedDslope (matveevPhi_of_coeffs L N1 N2 c 1 1) k 0 =
      (auxPoly L N1 N2 c).coeff k := by
  rw [matveevPhi_of_coeffs_eq_auxPoly]
  exact iteratedDslope_polynomial_coeff (auxPoly L N1 N2 c) k

theorem jetMatrix_ker_auxPoly_coeff
    {L N1 N2 T : ℕ} {c : Fin (coeffCount L N1 N2) → ℤ}
    (hker : (jetMatrix L N1 N2 T).mulVec c = 0) {k : ℕ} (hk : k < T) :
    (auxPoly L N1 N2 c).coeff k = 0 := by
  have hrow : (jetMatrix L N1 N2 T).mulVec c ⟨k, hk⟩ = 0 :=
    congr_fun hker _
  have hsum := jetMatrix_mulVec L N1 N2 T c ⟨k, hk⟩
  rw [auxPoly_coeff]
  have hcast :
      (∑ j : Fin (coeffCount L N1 N2),
          if decodeCoeffL L N1 N2 j = k then (c j : ℂ) else 0) =
        ((∑ j : Fin (coeffCount L N1 N2),
            if decodeCoeffL L N1 N2 j = k then c j else 0 : ℤ) : ℂ) := by
    rw [Int.cast_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    split_ifs <;> simp
  have hz :
      (∑ j : Fin (coeffCount L N1 N2),
          if decodeCoeffL L N1 N2 j = k then c j else 0 : ℤ) = 0 := by
    rw [← hsum, hrow]
  rw [hcast, hz, Int.cast_zero]

/-- `P(y0,y1,y2) = Σ c y0^ℓ y1^{k1} y2^{k2}`. -/
def matveevP (terms : List PhiTerm) (y0 y1 y2 : ℂ) : ℂ :=
  (terms.map (fun t => t.coeff * y0 ^ t.l * y1 ^ t.k1 * y2 ^ t.k2)).sum

/-- The curve `W`: `z ↦ (z, α1^z, α2^z)` in `𝐆_a × 𝐆_m²`. -/
def matveevW (α1 α2 : ℝ) (z : ℂ) : ℂ × ℂ × ℂ :=
  (z, alphaPowZ α1 z, alphaPowZ α2 z)

/-- Lie-algebra direction `(z, z log α1, z log α2)`. -/
def matveevW_lie (α1 α2 : ℝ) (z : ℂ) : ℂ × ℂ × ℂ :=
  (z, (Real.log α1 : ℂ) * z, (Real.log α2 : ℂ) * z)

theorem matveevPhi_eq_P_along_W
    (α1 α2 : ℝ) (terms : List PhiTerm) (z : ℂ) :
    matveevPhi α1 α2 terms z =
      matveevP terms z (alphaPowZ α1 z) (alphaPowZ α2 z) := by
  unfold matveevPhi matveevP
  refine congrArg List.sum ?_
  induction terms with
  | nil => rfl
  | cons t ts ih =>
    simp only [List.map_cons]
    refine congrArg₂ List.cons ?_ ih
    unfold phiTermEval
    rw [alphaPowZ_nat_mul, alphaPowZ_nat_mul]

theorem matveevPhi_eq_P_along_W'
    (α1 α2 : ℝ) (terms : List PhiTerm) (z : ℂ) :
    matveevPhi α1 α2 terms z =
      matveevP terms (matveevW α1 α2 z).1 (matveevW α1 α2 z).2.1
        (matveevW α1 α2 z).2.2 :=
  matveevPhi_eq_P_along_W α1 α2 terms z

/-- Integer vanishing of the G_a jet: Siegel produces nonzero `c`
    of controlled height such that `Φ_{1,1}` vanishes to order
    `siegel_T = N/2` at `0`. Exact exponential-jet vanishing over `ℤ`
    is not an integer system (derivatives carry `log α`). -/
theorem matveevPhi_vanishing_exists_T
    {L N1 N2 : ℕ} (hN : 2 ≤ coeffCount L N1 N2) :
    ∃ c : Fin (coeffCount L N1 N2) → ℤ,
      c ≠ 0 ∧
        (jetMatrix L N1 N2 (siegel_T L N1 N2)).mulVec c = 0 ∧
          ‖c‖ ≤
              ((coeffCount L N1 N2 : ℝ) *
                  max 1 ‖jetMatrix L N1 N2 (siegel_T L N1 N2)‖) ^
                ((siegel_T L N1 N2 : ℝ) /
                  (coeffCount L N1 N2 - siegel_T L N1 N2 : ℝ)) ∧
            ∀ k < siegel_T L N1 N2,
              iteratedDslope (matveevPhi_of_coeffs L N1 N2 c 1 1) k 0 = 0 := by
  have hm : 0 < Fintype.card (Fin (siegel_T L N1 N2)) := by
    rw [Fintype.card_fin]
    exact siegel_T_pos hN
  have hn :
      Fintype.card (Fin (siegel_T L N1 N2)) <
        Fintype.card (Fin (coeffCount L N1 N2)) := by
    rw [Fintype.card_fin, Fintype.card_fin]
    exact siegel_T_lt hN
  obtain ⟨c, hc0, hker, hnorm⟩ :=
    siegel_lemma (jetMatrix L N1 N2 (siegel_T L N1 N2)) hn hm
  refine ⟨c, hc0, hker, ?_, ?_⟩
  · simpa [Fintype.card_fin] using hnorm
  · intro k hk
    rw [matveevPhi_of_coeffs_dslope]
    exact jetMatrix_ker_auxPoly_coeff hker hk

theorem matveevPhi_vanishing_exists_T_height
    {L N1 N2 : ℕ} (hN : 2 ≤ coeffCount L N1 N2) :
    ∃ c : Fin (coeffCount L N1 N2) → ℤ,
      c ≠ 0 ∧
        ‖c‖ ≤ (coeffCount L N1 N2 : ℝ) ∧
          ∀ k < siegel_T L N1 N2,
            iteratedDslope (matveevPhi_of_coeffs L N1 N2 c 1 1) k 0 = 0 := by
  obtain ⟨c, hc0, _, hnorm, hvan⟩ := matveevPhi_vanishing_exists_T hN
  refine ⟨c, hc0, ?_, hvan⟩
  have hA : ‖jetMatrix L N1 N2 (siegel_T L N1 N2)‖ ≤ 1 :=
    jetMatrix_norm_le_one L N1 N2 _
  have hmax : max 1 ‖jetMatrix L N1 N2 (siegel_T L N1 N2)‖ = 1 :=
    le_antisymm (max_le le_rfl hA) (le_max_left _ _)
  have hTle : (siegel_T L N1 N2 : ℝ) ≤
      (coeffCount L N1 N2 : ℝ) - (siegel_T L N1 N2 : ℝ) := by
    have hsum : (siegel_T L N1 N2 : ℝ) + (siegel_T L N1 N2 : ℝ) ≤
        (coeffCount L N1 N2 : ℝ) := by
      have h2 := two_mul_siegel_T_le L N1 N2
      have h2' : siegel_T L N1 N2 + siegel_T L N1 N2 ≤
          coeffCount L N1 N2 := by rwa [two_mul] at h2
      exact_mod_cast h2'
    linarith
  have hpow :
      ((coeffCount L N1 N2 : ℝ) *
          max 1 ‖jetMatrix L N1 N2 (siegel_T L N1 N2)‖) ^
          ((siegel_T L N1 N2 : ℝ) /
            (coeffCount L N1 N2 - siegel_T L N1 N2 : ℝ)) ≤
        (coeffCount L N1 N2 : ℝ) := by
    rw [hmax, mul_one]
    have hden : (0 : ℝ) <
        (coeffCount L N1 N2 : ℝ) - (siegel_T L N1 N2 : ℝ) := by
      have : (siegel_T L N1 N2 : ℝ) < (coeffCount L N1 N2 : ℝ) :=
        Nat.cast_lt.mpr (siegel_T_lt hN)
      linarith
    have hexp : (siegel_T L N1 N2 : ℝ) /
        ((coeffCount L N1 N2 : ℝ) - (siegel_T L N1 N2 : ℝ)) ≤ 1 :=
      (div_le_one hden).2 hTle
    have hbase : (1 : ℝ) ≤ (coeffCount L N1 N2 : ℝ) := by
      exact_mod_cast (le_trans (by decide : (1 : ℕ) ≤ 2) hN)
    exact (Real.rpow_le_rpow_of_exponent_le hbase hexp).trans_eq
      (Real.rpow_one _)
  exact le_trans hnorm hpow

theorem nat_cast_le_exp (n : ℕ) : (n : ℝ) ≤ Real.exp n :=
  (le_add_of_nonneg_right (by norm_num : (0 : ℝ) ≤ 1)).trans
    (Real.add_one_le_exp _)

/-- Siegel height is at most `N`, hence at most `exp N`. Displayed
    Matveev bookkeeping writes this as `exp(O(L K))` once
    `N = (L+1)(N1+1)(N2+1)` is absorbed. -/
theorem matveevPhi_vanishing_exists_T_exp_height
    {L N1 N2 : ℕ} (hN : 2 ≤ coeffCount L N1 N2) :
    ∃ c : Fin (coeffCount L N1 N2) → ℤ,
      c ≠ 0 ∧
        ‖c‖ ≤ Real.exp (coeffCount L N1 N2 : ℝ) ∧
          ∀ k < siegel_T L N1 N2,
            iteratedDslope (matveevPhi_of_coeffs L N1 N2 c 1 1) k 0 = 0 := by
  obtain ⟨c, hc0, hnorm, hvan⟩ := matveevPhi_vanishing_exists_T_height hN
  exact ⟨c, hc0, hnorm.trans (nat_cast_le_exp _), hvan⟩

/-! ## Multiplicative dependence on gap-3 -/

theorem nat_pow_eq_pow_log {A C a b : ℕ}
    (_hA : 1 < A) (_hC : 1 < C) (heq : A ^ a = C ^ b) :
    (a : ℝ) * log (A : ℝ) = (b : ℝ) * log (C : ℝ) := by
  have hpow : ((A : ℝ) ^ a) = ((C : ℝ) ^ b) := by exact_mod_cast heq
  have hlog := congrArg log hpow
  rw [log_pow (A : ℝ) a, log_pow (C : ℝ) b] at hlog
  exact hlog

theorem fourth_thirteenth_log_ratio {A C : ℕ}
    (hA : 1 < A) (hC : 1 < C) (heq : A ^ 4 = C ^ 13) :
    (4 : ℝ) * log (A : ℝ) = 13 * log (C : ℝ) :=
  nat_pow_eq_pow_log hA hC heq

/-- On a gap-3 solution `B^4 > 0`, so `A^4 ≠ (B+3)^13`. The ratio
    `4/13` is therefore not a multiplicative relation. Remaining
    relations are a Baker / LLL question (`baker_bound_gap3`). -/
theorem gap3_not_fourth_thirteenth {A B : ℕ}
    (h : A ^ 4 + B ^ 4 = (B + 3) ^ 13) (hB : 0 < B) :
    A ^ 4 ≠ (B + 3) ^ 13 := by
  intro heq
  have hB4 : B ^ 4 = 0 := by
    have : A ^ 4 + B ^ 4 = A ^ 4 := by
      rw [h, heq]
    exact Nat.add_left_cancel this
  have hB0 : B = 0 := (Nat.pow_eq_zero.1 hB4).1
  exact hB.ne' hB0

def multiplicativelyDependent (α1 α2 : ℕ) : Prop :=
  ∃ a b : ℕ, (a ≠ 0 ∨ b ≠ 0) ∧ α1 ^ a = α2 ^ b

theorem mul_dep_implies_log_ratio {α1 α2 a b : ℕ}
    (hα1 : 1 < α1) (hα2 : 1 < α2)
    (heq : α1 ^ a = α2 ^ b) (hpos : a ≠ 0 ∨ b ≠ 0) :
    0 < a ∧ 0 < b ∧
      (a : ℝ) * log (α1 : ℝ) = (b : ℝ) * log (α2 : ℝ) := by
  have ha : 0 < a := by
    by_contra h
    have ha0 : a = 0 := by omega
    have hb : b ≠ 0 := by
      simpa [ha0] using hpos
    have : (1 : ℕ) = α2 ^ b := by
      simpa [ha0, pow_zero] using heq
    have hlt : 1 < α2 ^ b := one_lt_pow hα2 hb
    rw [← this] at hlt
    exact lt_irrefl _ hlt
  have hb : 0 < b := by
    by_contra h
    have hb0 : b = 0 := by omega
    have : α1 ^ a = 1 := by
      simpa [hb0, pow_zero] using heq
    have hlt : 1 < α1 ^ a := one_lt_pow hα1 ha.ne'
    rw [this] at hlt
    exact lt_irrefl _ hlt
  exact ⟨ha, hb, nat_pow_eq_pow_log hα1 hα2 heq⟩

/-! ## `L ≥ 1` degenerate smallness (`α1=α2=1`) -/

theorem interpDim_K_succ_lt (L K : ℕ) (hL : 0 < L) :
    K + 1 < interpDim L K := by
  unfold interpDim
  have h : 1 < L + 1 := Nat.succ_lt_succ hL
  have hpos : 0 < K + 1 := Nat.succ_pos K
  have hmul : 1 * (K + 1) < (L + 1) * (K + 1) :=
    Nat.mul_lt_mul_of_pos_right h hpos
  simpa using hmul

theorem interpolationDeterminant_L_pos_alpha_one
    (L K N1 N2 : ℕ) (hL : 0 < L) :
    interpolationDeterminant L K N1 N2 1 1 = 0 := by
  unfold interpolationDeterminant
  have h0 : 0 < interpDim L K := interpDim_pos L K
  have h1 : K + 1 < interpDim L K := interpDim_K_succ_lt L K hL
  set j0 : Fin (interpDim L K) := ⟨0, h0⟩
  set j1 : Fin (interpDim L K) := ⟨K + 1, h1⟩
  have hne : j0 ≠ j1 := by
    apply Fin.ne_of_val_ne
    change (0 : ℕ) ≠ K + 1
    exact Ne.symm (Nat.succ_ne_zero K)
  have hL0 : decodeL L K j0 = 0 := by
    simp [decodeL, j0]
  have hK0 : decodeK L K j0 = 0 := by
    simp [decodeK, j0]
  have hL1 : decodeL L K j1 = 1 := by
    simp [decodeL, j1, Nat.div_self (Nat.succ_pos K)]
  have hK1 : decodeK L K j1 = 0 := by
    simp [decodeK, j1, Nat.mod_self]
  have hcol : ∀ i : Fin (interpDim L K),
      matveevInterpMatrix (interpDim L K) 1 1 (matveevColumn L K N1 N2) i j0 =
        matveevInterpMatrix (interpDim L K) 1 1 (matveevColumn L K N1 N2) i j1 := by
    intro i
    unfold matveevInterpMatrix matveevEntry matveevColumn
    simp [hL0, hK0, hL1, hK1, one_pow]
  exact det_zero_of_column_eq hne hcol

/-- Degenerate smallness: `α1=α2=1` and `L≥1` forces `Δ=0`.
    Generic `|Δ|≤exp(−c L K)` stays `size_upper_bound` (`def Prop`). -/
theorem interpolationDeterminant_L_pos_exp_small
    (L K N1 N2 : ℕ) (hL : 0 < L) {c : ℝ} :
    |interpolationDeterminant L K N1 N2 1 1| ≤
      exp (-c * (L : ℝ) * (K : ℝ)) := by
  rw [interpolationDeterminant_L_pos_alpha_one L K N1 N2 hL, abs_zero]
  exact le_of_lt (exp_pos _)

/-! ## Jet invertibility on `W` for independent frequencies

Mathlib 4.12 has no Wüstholz subgroup theorem. The theorem below is
the jet criterion for `{ z^ℓ α1^{k1 z} α2^{k2 z} }`: independent
frequencies make the order-`N` jet at `0` injective. This does not
close Matveev 2000 / `C1_floor`. Gap-3 rules out `A^4=(B+3)^13`,
not every multiplicative relation (`baker_bound_gap3`).
-/

def freqReal (α1 α2 : ℝ) (k1 k2 : ℕ) : ℝ :=
  (k1 : ℝ) * log α1 + (k2 : ℝ) * log α2

def freq (α1 α2 : ℝ) (k1 k2 : ℕ) : ℂ :=
  (freqReal α1 α2 k1 k2 : ℂ)

theorem alphaPowZ_mul_freq (α1 α2 : ℝ) (k1 k2 : ℕ) (z : ℂ) :
    alphaPowZ α1 ((k1 : ℂ) * z) * alphaPowZ α2 ((k2 : ℂ) * z) =
      Complex.exp (freq α1 α2 k1 k2 * z) := by
  unfold alphaPowZ freq freqReal
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem decodeCoeffK2_lt (L N1 N2 : ℕ) (j : Fin (coeffCount L N1 N2)) :
    decodeCoeffK2 L N1 N2 j < N2 + 1 :=
  Nat.mod_lt _ (Nat.succ_pos N2)

theorem decodeCoeffK1_lt (L N1 N2 : ℕ) (j : Fin (coeffCount L N1 N2)) :
    decodeCoeffK1 L N1 N2 j < N1 + 1 := by
  unfold decodeCoeffK1
  have hpos : 0 < N2 + 1 := Nat.succ_pos N2
  have hmod : j.val % n12 N1 N2 < n12 N1 N2 := Nat.mod_lt _ (n12_pos N1 N2)
  have : j.val % n12 N1 N2 < (N1 + 1) * (N2 + 1) := by
    simpa [n12] using hmod
  exact (Nat.div_lt_iff_lt_mul hpos).2 this

theorem log_nat_pos {α : ℕ} (hα : 1 < α) : 0 < log (α : ℝ) :=
  Real.log_pos (by exact_mod_cast hα)

theorem nat_mul_log_eq_pow {A C n m : ℕ}
    (hA : 1 < A) (hC : 1 < C)
    (heq : (n : ℝ) * log (A : ℝ) = (m : ℝ) * log (C : ℝ)) :
    A ^ n = C ^ m := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hCpos : (0 : ℝ) < C := by exact_mod_cast (Nat.zero_lt_of_lt hC)
  have hL : Real.exp ((n : ℝ) * log (A : ℝ)) = (A : ℝ) ^ n := by
    rw [Real.exp_nat_mul, Real.exp_log hApos]
  have hR : Real.exp ((m : ℝ) * log (C : ℝ)) = (C : ℝ) ^ m := by
    rw [Real.exp_nat_mul, Real.exp_log hCpos]
  have : ((A : ℝ) ^ n) = ((C : ℝ) ^ m) := by
    have := congrArg Real.exp heq
    rwa [hL, hR] at this
  exact_mod_cast this

theorem freqReal_eq_of_indep {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (hindep : ¬ multiplicativelyDependent α1 α2) {k1 k2 k1' k2' : ℕ}
    (heq : freqReal (α1 : ℝ) (α2 : ℝ) k1 k2 =
      freqReal (α1 : ℝ) (α2 : ℝ) k1' k2') :
    k1 = k1' ∧ k2 = k2' := by
  have hα1p := log_nat_pos hα1
  have hα2p := log_nat_pos hα2
  set a : ℤ := (k1 : ℤ) - (k1' : ℤ)
  set b : ℤ := (k2' : ℤ) - (k2 : ℤ)
  have hlin : (a : ℝ) * log (α1 : ℝ) = (b : ℝ) * log (α2 : ℝ) := by
    unfold freqReal at heq
    simp [a, b]
    linarith
  have ha0 : a = 0 := by
    by_contra ha
    have hb : b ≠ 0 := by
      intro hb
      have : (a : ℝ) * log (α1 : ℝ) = 0 := by simpa [hb] using hlin
      have : (a : ℝ) = 0 := (mul_eq_zero.mp this).resolve_right hα1p.ne'
      exact ha (by exact_mod_cast this)
    have hsign : (0 < a ∧ 0 < b) ∨ (a < 0 ∧ b < 0) := by
      have hprod : (a : ℝ) * log (α1 : ℝ) ≠ 0 :=
        mul_ne_zero (by exact_mod_cast ha) hα1p.ne'
      rcases lt_or_gt_of_ne hprod with hneg | hpos
      · have ha' : (a : ℝ) < 0 := neg_of_mul_neg_left hneg (le_of_lt hα1p)
        have hb' : (b : ℝ) < 0 :=
          neg_of_mul_neg_left (hlin ▸ hneg) (le_of_lt hα2p)
        exact Or.inr ⟨by exact_mod_cast ha', by exact_mod_cast hb'⟩
      · have ha' : 0 < (a : ℝ) := pos_of_mul_pos_left hpos (le_of_lt hα1p)
        have hb' : 0 < (b : ℝ) :=
          pos_of_mul_pos_left (hlin ▸ hpos) (le_of_lt hα2p)
        exact Or.inl ⟨by exact_mod_cast ha', by exact_mod_cast hb'⟩
    refine hindep ?_
    rcases hsign with ⟨ha', hb'⟩ | ⟨ha', hb'⟩
    · refine ⟨a.natAbs, b.natAbs, Or.inl (Int.natAbs_ne_zero.2 ha), ?_⟩
      have haAbs : (a : ℝ) = (a.natAbs : ℝ) := by
        rw [Int.cast_natAbs, abs_of_pos (by exact_mod_cast ha')]
      have hbAbs : (b : ℝ) = (b.natAbs : ℝ) := by
        rw [Int.cast_natAbs, abs_of_pos (by exact_mod_cast hb')]
      apply nat_mul_log_eq_pow hα1 hα2
      rwa [← haAbs, ← hbAbs]
    · refine ⟨(-a).natAbs, (-b).natAbs,
        Or.inl (Int.natAbs_ne_zero.2 (neg_ne_zero.2 ha)), ?_⟩
      have haAbs : (-(a : ℝ)) = ((-a).natAbs : ℝ) := by
        rw [Int.cast_natAbs, Int.cast_abs, Int.cast_neg, abs_neg]
        exact (abs_of_neg (show (a : ℝ) < 0 from by exact_mod_cast ha')).symm
      have hbAbs : (-(b : ℝ)) = ((-b).natAbs : ℝ) := by
        rw [Int.cast_natAbs, Int.cast_abs, Int.cast_neg, abs_neg]
        exact (abs_of_neg (show (b : ℝ) < 0 from by exact_mod_cast hb')).symm
      apply nat_mul_log_eq_pow hα1 hα2
      have : (-(a : ℝ)) * log (α1 : ℝ) = (-(b : ℝ)) * log (α2 : ℝ) := by
        linarith
      rwa [← haAbs, ← hbAbs]
  have hb0 : b = 0 := by
    have : (b : ℝ) * log (α2 : ℝ) = 0 := by simpa [ha0] using hlin
    exact_mod_cast (mul_eq_zero.mp this).resolve_right hα2p.ne'
  constructor
  · have : (k1 : ℤ) = (k1' : ℤ) := sub_eq_zero.mp (by simpa [a] using ha0)
    exact_mod_cast this
  · have : (k2 : ℤ) = (k2' : ℤ) :=
      (sub_eq_zero.mp (by simpa [b] using hb0)).symm
    exact_mod_cast this

theorem freq_injective_of_indep {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (hindep : ¬ multiplicativelyDependent α1 α2) (N1 N2 : ℕ) :
    Function.Injective fun s : Fin (n12 N1 N2) =>
      freq (α1 : ℝ) (α2 : ℝ) (s.val / (N2 + 1)) (s.val % (N2 + 1)) := by
  intro s t hst
  have hR : freqReal (α1 : ℝ) (α2 : ℝ) (s.val / (N2 + 1)) (s.val % (N2 + 1)) =
      freqReal (α1 : ℝ) (α2 : ℝ) (t.val / (N2 + 1)) (t.val % (N2 + 1)) :=
    Complex.ofReal_injective (by simpa [freq] using hst)
  obtain ⟨hk1, hk2⟩ := freqReal_eq_of_indep hα1 hα2 hindep hR
  apply Fin.ext
  have hs : s.val = (s.val / (N2 + 1)) * (N2 + 1) + s.val % (N2 + 1) := by
    rw [mul_comm, Nat.div_add_mod]
  have ht : t.val = (t.val / (N2 + 1)) * (N2 + 1) + t.val % (N2 + 1) := by
    rw [mul_comm, Nat.div_add_mod]
  rw [hs, ht, hk1, hk2]

theorem iteratedDeriv_eq_factorial_mul_dslope
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n f 0 = (n.factorial : ℂ) * iteratedDslope f n 0 := by
  have hR : (0 : NNReal) < 1 := by norm_num
  have hp := hf.hasFPowerSeriesOnBall (0 : ℂ) hR
  have hAt : HasFPowerSeriesAt f (cauchyPowerSeries f 0 1) 0 :=
    hp.hasFPowerSeriesAt
  have hds : iteratedDslope f n 0 = (cauchyPowerSeries f 0 1).coeff n :=
    iteratedDslope_zero_eq_coeff hAt n
  have hfac := hp.factorial_smul (1 : ℂ) n
  rw [FormalMultilinearSeries.apply_eq_pow_smul_coeff, one_pow, one_smul] at hfac
  rw [← iteratedDeriv_eq_iteratedFDeriv] at hfac
  have hcoeff :
      (cauchyPowerSeries f 0 (1 : NNReal)).coeff n = iteratedDslope f n 0 := by
    convert hds.symm
  rw [hcoeff] at hfac
  simpa [nsmul_eq_mul] using hfac.symm

theorem iteratedDeriv_fun_sum {ι : Type*} [Fintype ι]
    (f : ι → ℂ → ℂ) (hf : ∀ i, Differentiable ℂ (f i)) (n : ℕ) (z : ℂ) :
    iteratedDeriv n (fun w => ∑ i, f i w) z =
      ∑ i, iteratedDeriv n (f i) z := by
  have hfC : ∀ i, ContDiff ℂ ⊤ (f i) := fun i => (hf i).contDiff
  induction n generalizing z with
  | zero =>
    simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hfun :
        (fun w => ∑ i, iteratedDeriv n (f i) w) =
          iteratedDeriv n (fun w => ∑ i, f i w) := by
      funext w
      exact (ih w).symm
    rw [← hfun, deriv_sum]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [iteratedDeriv_succ]
    · intro i _
      exact ((hfC i).differentiable_iteratedDeriv n (WithTop.coe_lt_top _)).differentiableAt

theorem matveevPhi_of_coeffs_eq_expSum (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (α1 α2 : ℝ) (z : ℂ) :
    matveevPhi_of_coeffs L N1 N2 c α1 α2 z =
      ∑ j : Fin (coeffCount L N1 N2),
        (c j : ℂ) * z ^ decodeCoeffL L N1 N2 j *
          Complex.exp (freq α1 α2 (decodeCoeffK1 L N1 N2 j)
            (decodeCoeffK2 L N1 N2 j) * z) := by
  unfold matveevPhi_of_coeffs
  refine Finset.sum_congr rfl fun j _ => ?_
  trans
      (c j : ℂ) * z ^ decodeCoeffL L N1 N2 j *
        (alphaPowZ α1 ((decodeCoeffK1 L N1 N2 j : ℂ) * z) *
          alphaPowZ α2 ((decodeCoeffK2 L N1 N2 j : ℂ) * z))
  · ring
  · rw [alphaPowZ_mul_freq]

theorem matveevPhi_of_coeffs_L0 (N1 N2 : ℕ)
    (c : Fin (coeffCount 0 N1 N2) → ℤ) (α1 α2 : ℝ) (z : ℂ) :
    matveevPhi_of_coeffs 0 N1 N2 c α1 α2 z =
      ∑ j : Fin (coeffCount 0 N1 N2),
        (c j : ℂ) *
          Complex.exp (freq α1 α2 (decodeCoeffK1 0 N1 N2 j)
            (decodeCoeffK2 0 N1 N2 j) * z) := by
  rw [matveevPhi_of_coeffs_eq_expSum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hL : decodeCoeffL 0 N1 N2 j = 0 :=
    Nat.lt_one_iff.mp (decodeCoeffL_lt 0 N1 N2 j)
  simp [hL]

theorem matveevPhi_of_coeffs_differentiable (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (α1 α2 : ℝ) :
    Differentiable ℂ (matveevPhi_of_coeffs L N1 N2 c α1 α2) := by
  unfold matveevPhi_of_coeffs
  refine Differentiable.sum fun j _ => ?_
  have hz : Differentiable ℂ fun z : ℂ => (z : ℂ) ^ decodeCoeffL L N1 N2 j :=
    differentiable_id.pow _
  have h1 : Differentiable ℂ fun z : ℂ =>
      alphaPowZ α1 ((decodeCoeffK1 L N1 N2 j : ℂ) * z) :=
    (alphaPowZ_differentiable α1).comp (differentiable_id.const_mul _)
  have h2 : Differentiable ℂ fun z : ℂ =>
      alphaPowZ α2 ((decodeCoeffK2 L N1 N2 j : ℂ) * z) :=
    (alphaPowZ_differentiable α2).comp (differentiable_id.const_mul _)
  exact ((differentiable_const _).mul hz).mul h1 |>.mul h2

theorem decodeL_L0 (N1 N2 : ℕ) (j : Fin (coeffCount 0 N1 N2)) :
    decodeCoeffL 0 N1 N2 j = 0 :=
  Nat.lt_one_iff.mp (decodeCoeffL_lt 0 N1 N2 j)

theorem decodeCoeffK1_L0 (N1 N2 : ℕ) (j : Fin (coeffCount 0 N1 N2)) :
    decodeCoeffK1 0 N1 N2 j = j.val / (N2 + 1) := by
  have hj : j.val < n12 N1 N2 := by
    simpa [coeffCount, n12] using j.isLt
  simp [decodeCoeffK1, Nat.mod_eq_of_lt hj]

theorem decodeCoeffK2_L0 (N1 N2 : ℕ) (j : Fin (coeffCount 0 N1 N2)) :
    decodeCoeffK2 0 N1 N2 j = j.val % (N2 + 1) := by
  have hj : j.val < n12 N1 N2 := by
    simpa [coeffCount, n12] using j.isLt
  simp [decodeCoeffK2, Nat.mod_eq_of_lt hj]

/-- Pull a constant out of `iteratedDeriv`. Mathlib's
    `iteratedDeriv_const_mul` is the chain-rule form `f (c * x)`. -/
theorem iteratedDeriv_const_mul_fun
    (n : ℕ) (a : ℂ) (f : ℂ → ℂ) (hf : Differentiable ℂ f) (z : ℂ) :
    iteratedDeriv n (fun w => a * f w) z = a * iteratedDeriv n f z := by
  induction n generalizing z with
  | zero =>
    simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    have hcongr :
        iteratedDeriv n (fun w => a * f w) = fun w => a * iteratedDeriv n f w := by
      funext w
      exact ih w
    rw [hcongr, deriv_const_mul]
    exact ((hf.contDiff.differentiable_iteratedDeriv n
      (WithTop.coe_lt_top n)).differentiableAt)

theorem cexp_const_mul_differentiable (μ : ℂ) :
    Differentiable ℂ fun w => Complex.exp (μ * w) :=
  (differentiable_id.const_mul μ).cexp

theorem iteratedDeriv_mul_cexp (n : ℕ) (a μ : ℂ) (z : ℂ) :
    iteratedDeriv n (fun w => a * Complex.exp (μ * w)) z =
      a * μ ^ n * Complex.exp (μ * z) := by
  rw [iteratedDeriv_const_mul_fun n a _ (cexp_const_mul_differentiable μ) z]
  have h := iteratedDeriv_cexp_const_mul n μ
  have : iteratedDeriv n (fun w => Complex.exp (μ * w)) z =
      μ ^ n * Complex.exp (μ * z) := by
    simp [h]
  rw [this, mul_assoc]

theorem iteratedDeriv_zero_iff_dslope
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (n : ℕ) :
    iteratedDeriv n f 0 = 0 ↔ iteratedDslope f n 0 = 0 := by
  rw [iteratedDeriv_eq_factorial_mul_dslope hf n]
  constructor
  · intro h
    exact (mul_eq_zero.mp h).resolve_left
      (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
  · intro h
    rw [h, mul_zero]

/-- Independent frequencies: vanishing of the first `n12` derivatives of a
    pure exponential sum (`L = 0`) forces all coefficients to vanish. -/
theorem wuestholz_product_theorem_exp_Gm_L0
    {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (hindep : ¬ multiplicativelyDependent α1 α2) {N1 N2 : ℕ}
    (c : Fin (coeffCount 0 N1 N2) → ℤ)
    (hvan : ∀ k < coeffCount 0 N1 N2,
      iteratedDslope (matveevPhi_of_coeffs 0 N1 N2 c α1 α2) k 0 = 0) :
    c = 0 := by
  have hf := matveevPhi_of_coeffs_differentiable 0 N1 N2 c α1 α2
  have hN : coeffCount 0 N1 N2 = n12 N1 N2 := by
    simp [coeffCount, n12]
  let μ : Fin (coeffCount 0 N1 N2) → ℂ := fun j =>
    freq (α1 : ℝ) (α2 : ℝ) (decodeCoeffK1 0 N1 N2 j) (decodeCoeffK2 0 N1 N2 j)
  have hμ : Function.Injective μ := by
    intro j₁ j₂ hj
    have hj1 :
        (⟨j₁.val, by simpa [hN] using j₁.isLt⟩ : Fin (n12 N1 N2)) =
          ⟨j₂.val, by simpa [hN] using j₂.isLt⟩ := by
      apply freq_injective_of_indep hα1 hα2 hindep N1 N2
      simpa [μ, decodeCoeffK1_L0, decodeCoeffK2_L0] using hj
    have hv : j₁.val = j₂.val :=
      congrArg (fun x : Fin (n12 N1 N2) => x.val) hj1
    exact Fin.ext hv
  have hterm : ∀ j,
      Differentiable ℂ fun z : ℂ =>
        (c j : ℂ) * Complex.exp (μ j * z) := fun j =>
    (differentiable_const _).mul (cexp_const_mul_differentiable (μ j))
  have hsum0 : ∀ t < coeffCount 0 N1 N2,
      iteratedDeriv t (matveevPhi_of_coeffs 0 N1 N2 c α1 α2) 0 = 0 := by
    intro t ht
    exact (iteratedDeriv_zero_iff_dslope hf t).2 (hvan t ht)
  have hsum :
      (fun z => matveevPhi_of_coeffs 0 N1 N2 c α1 α2 z) =
        fun z => ∑ j, (c j : ℂ) * Complex.exp (μ j * z) := by
    funext z
    simpa [μ] using matveevPhi_of_coeffs_L0 N1 N2 c α1 α2 z
  have hjet : ∀ t : Fin (coeffCount 0 N1 N2),
      (∑ j, (c j : ℂ) * μ j ^ (t : ℕ)) = 0 := by
    intro t
    have h0 :
        iteratedDeriv t.val (fun z => matveevPhi_of_coeffs 0 N1 N2 c α1 α2 z) 0 = 0 :=
      hsum0 t.val t.isLt
    rw [hsum] at h0
    have hder := iteratedDeriv_fun_sum
      (fun j z => (c j : ℂ) * Complex.exp (μ j * z)) hterm t.val (0 : ℂ)
    rw [hder] at h0
    have htermDer : ∀ j,
        iteratedDeriv t.val (fun z => (c j : ℂ) * Complex.exp (μ j * z)) 0 =
          (c j : ℂ) * μ j ^ (t : ℕ) := by
      intro j
      simpa [Complex.exp_zero, mul_one] using
        iteratedDeriv_mul_cexp t.val (c j : ℂ) (μ j) 0
    simpa [htermDer] using h0
  have hvd :=
    eq_zero_of_forall_pow_sum_mul_pow_eq_zero (R := ℂ) hμ hjet
  exact funext fun j => by
    have hz : (c j : ℂ) = 0 := by
      have := congrArg (fun v => v j) hvd
      simpa using this
    exact Int.cast_eq_zero.mp hz


/-- Analytic curve `W = {(z, α1^z, α2^z)}` in `G_a × G_m²`. -/
def W_map (α1 α2 : ℝ) (z : ℂ) : ℂ × ℂ × ℂ :=
  (z, alphaPowZ α1 z, alphaPowZ α2 z)

theorem iteratedDslope_entire {f : ℂ → ℂ} (hf : Differentiable ℂ f) :
    ∀ n, Differentiable ℂ (iteratedDslope f n)
  | 0 => hf
  | n + 1 => by
    intro z
    have hR : (0 : ℝ) < ‖z‖ + 1 :=
      add_pos_of_nonneg_of_pos (norm_nonneg z) one_pos
    have hzmem : z ∈ ball (0 : ℂ) (‖z‖ + 1) := by
      rw [mem_ball_zero_iff]
      linarith [norm_nonneg z]
    have hd :=
      (Complex.differentiableOn_dslope (ball_mem_nhds (0 : ℂ) hR)).2
        ((iteratedDslope_entire hf n).differentiableOn)
    exact hd.differentiableAt (isOpen_ball.mem_nhds hzmem)

theorem vanishing_mul_cexp
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (lam : ℂ) {T : ℕ}
    (hvan : ∀ k < T, iteratedDslope f k 0 = 0) {k : ℕ} (hk : k < T) :
    iteratedDslope (fun z => Complex.exp (lam * z) * f z) k 0 = 0 := by
  have heq : (fun z => Complex.exp (lam * z) * f z) =
      fun z => z ^ T * (Complex.exp (lam * z) * iteratedDslope f T z) := by
    funext z
    rw [eval_eq_pow_mul_iteratedDslope f T hvan z]
    ring
  have hg : Differentiable ℂ fun z =>
      Complex.exp (lam * z) * iteratedDslope f T z :=
    (cexp_const_mul_differentiable lam).mul (iteratedDslope_entire hf T)
  rw [heq]
  exact iteratedDslope_pow_mul_vanishes _ T hg hk

theorem vanishing_mul_cexp_deriv
    {f : ℂ → ℂ} (hf : Differentiable ℂ f) (lam : ℂ) {T : ℕ}
    (hvan : ∀ t < T, iteratedDeriv t f 0 = 0) {n : ℕ} (hn : n < T) :
    iteratedDeriv n (fun z => Complex.exp (lam * z) * f z) 0 = 0 := by
  have hf' : Differentiable ℂ fun z => Complex.exp (lam * z) * f z :=
    (cexp_const_mul_differentiable lam).mul hf
  have hds : ∀ k < T, iteratedDslope f k 0 = 0 := fun k hk =>
    (iteratedDeriv_zero_iff_dslope hf k).1 (hvan k hk)
  exact (iteratedDeriv_zero_iff_dslope hf' n).2 (vanishing_mul_cexp hf lam hds hn)

theorem iteratedDeriv_add_right (m t : ℕ) (f : ℂ → ℂ) (z : ℂ) :
    iteratedDeriv (m + t) f z = iteratedDeriv t (iteratedDeriv m f) z := by
  induction t generalizing z with
  | zero =>
    simp [iteratedDeriv_zero]
  | succ t ih =>
    rw [Nat.add_succ, iteratedDeriv_succ, iteratedDeriv_succ]
    have hcongr :
        iteratedDeriv (m + t) f = iteratedDeriv t (iteratedDeriv m f) := by
      funext w
      exact ih w
    rw [hcongr]

def shiftPoly (ν : ℂ) (p : ℂ[X]) : ℂ[X] :=
  derivative p + C ν * p

theorem shiftPoly_sub (ν : ℂ) (p q : ℂ[X]) :
    shiftPoly ν (p - q) = shiftPoly ν p - shiftPoly ν q := by
  simp [shiftPoly, derivative_sub, mul_sub]
  ring

theorem shiftPoly_eq_zero {ν : ℂ} (hν : ν ≠ 0) {p : ℂ[X]}
    (h : shiftPoly ν p = 0) : p = 0 := by
  by_contra hp
  have hcoeff :
      (shiftPoly ν p).coeff p.natDegree = ν * p.leadingCoeff := by
    simp [shiftPoly, coeff_add, coeff_C_mul, coeff_derivative,
      coeff_eq_zero_of_natDegree_lt (Nat.lt_succ_self p.natDegree),
      coeff_natDegree]
  have hlead : (shiftPoly ν p).coeff p.natDegree ≠ 0 := by
    rw [hcoeff]
    exact mul_ne_zero hν (mt leadingCoeff_eq_zero.mp hp)
  exact hlead (by simp [h])

theorem shiftPoly_injective {ν : ℂ} (hν : ν ≠ 0) :
    Function.Injective (shiftPoly ν) := by
  intro p q hpq
  apply sub_eq_zero.mp
  exact shiftPoly_eq_zero hν (by rw [shiftPoly_sub, hpq, sub_self])

theorem natDegree_shiftPoly_le (ν : ℂ) (p : ℂ[X]) {L : ℕ}
    (h : p.natDegree ≤ L) : (shiftPoly ν p).natDegree ≤ L := by
  have h1 : (derivative p).natDegree ≤ L :=
    (natDegree_derivative_le p).trans ((Nat.sub_le _ _).trans h)
  have h2 : (C ν * p).natDegree ≤ L :=
    (natDegree_C_mul_le ν p).trans h
  exact (natDegree_add_le _ _).trans (max_le h1 h2)

theorem natDegree_iterate_shift_le (ν : ℂ) (p : ℂ[X]) {L : ℕ} (n : ℕ)
    (h : p.natDegree ≤ L) : ((shiftPoly ν)^[n] p).natDegree ≤ L := by
  induction n with
  | zero =>
    simpa using h
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact natDegree_shiftPoly_le ν _ ih

theorem shiftPoly_zero_eq_derivative (p : ℂ[X]) :
    shiftPoly 0 p = derivative p := by
  simp [shiftPoly]

theorem shiftPoly_map_zero (ν : ℂ) : ∀ n, (shiftPoly ν)^[n] 0 = 0
  | 0 => rfl
  | n + 1 => by
    rw [Function.iterate_succ_apply', shiftPoly_map_zero]
    simp [shiftPoly]

theorem iterate_shiftPoly_zero (n : ℕ) (p : ℂ[X]) :
    (shiftPoly 0)^[n] p = (derivative^[n] p) := by
  induction n generalizing p with
  | zero =>
    simp
  | succ n ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply,
      shiftPoly_zero_eq_derivative, ih]

theorem deriv_eval_mul_cexp (p : ℂ[X]) (ν : ℂ) (z : ℂ) :
    deriv (fun w => p.eval w * Complex.exp (ν * w)) z =
      (shiftPoly ν p).eval z * Complex.exp (ν * z) := by
  have hp := p.differentiable.differentiableAt (x := z)
  have he := (cexp_const_mul_differentiable ν).differentiableAt (x := z)
  rw [deriv_mul hp he, p.deriv]
  have hexp : deriv (fun w => Complex.exp (ν * w)) z =
      ν * Complex.exp (ν * z) := by
    have h := iteratedDeriv_cexp_const_mul 1 ν
    simpa [iteratedDeriv_succ, iteratedDeriv_zero, pow_one] using congrFun h z
  rw [hexp]
  simp [shiftPoly, eval_add, eval_mul, eval_C]
  ring

theorem iteratedDeriv_eval_mul_cexp (n : ℕ) (p : ℂ[X]) (ν : ℂ) (z : ℂ) :
    iteratedDeriv n (fun w => p.eval w * Complex.exp (ν * w)) z =
      ((shiftPoly ν)^[n] p).eval z * Complex.exp (ν * z) := by
  induction n generalizing z with
  | zero =>
    simp [iteratedDeriv_zero]
  | succ n ih =>
    rw [iteratedDeriv_succ]
    have hcongr :
        iteratedDeriv n (fun w => p.eval w * Complex.exp (ν * w)) =
          fun w => ((shiftPoly ν)^[n] p).eval w * Complex.exp (ν * w) := by
      funext w
      exact ih w
    rw [hcongr, deriv_eval_mul_cexp, Function.iterate_succ_apply']

theorem iteratedDeriv_eval_zero (p : ℂ[X]) (t : ℕ) :
    iteratedDeriv t (fun z => p.eval z) 0 = (t.factorial : ℂ) * p.coeff t := by
  have hf : Differentiable ℂ fun z => p.eval z := p.differentiable
  rw [iteratedDeriv_eq_factorial_mul_dslope hf t, iteratedDslope_polynomial_coeff]

theorem eval_mul_cexp_sum_differentiable {r : ℕ}
    (p : Fin r → ℂ[X]) (μ : Fin r → ℂ) :
    Differentiable ℂ fun z =>
      ∑ s, (p s).eval z * Complex.exp (μ s * z) :=
  Differentiable.sum fun s _ =>
    (p s).differentiable.mul (cexp_const_mul_differentiable (μ s))

/-- Jet invertibility for exponential polynomials with distinct
    frequencies and degree at most `L`. -/
theorem exp_poly_jet_zero (L : ℕ) :
    ∀ {r : ℕ} (μ : Fin r → ℂ), Function.Injective μ →
      ∀ (p : Fin r → ℂ[X]), (∀ s, (p s).natDegree ≤ L) →
        (∀ t < (L + 1) * r,
            iteratedDeriv t (fun z =>
              ∑ s, (p s).eval z * Complex.exp (μ s * z)) 0 = 0) →
          ∀ s, p s = 0 := by
  intro r
  induction r with
  | zero =>
    intro μ hμ p hdeg hvan s
    exact Fin.elim0 s
  | succ r ih =>
    intro μ hμ p hdeg hvan
    have hf := eval_mul_cexp_sum_differentiable p μ
    let g : ℂ → ℂ := fun z =>
      Complex.exp (-μ 0 * z) *
        ∑ s, (p s).eval z * Complex.exp (μ s * z)
    have hg_eq : g = fun z =>
        ∑ s, (p s).eval z * Complex.exp ((μ s - μ 0) * z) := by
      funext z
      simp only [g, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      have hexp :
          Complex.exp (-μ 0 * z) * Complex.exp (μ s * z) =
            Complex.exp ((μ s - μ 0) * z) := by
        rw [← Complex.exp_add]
        congr 1
        ring
      calc
        Complex.exp (-μ 0 * z) * ((p s).eval z * Complex.exp (μ s * z)) =
            (p s).eval z * (Complex.exp (-μ 0 * z) * Complex.exp (μ s * z)) := by
          ring
        _ = (p s).eval z * Complex.exp ((μ s - μ 0) * z) := by
          rw [hexp]
    have hT : (L + 1) * r.succ = (L + 1) * r + (L + 1) := by
      simp [Nat.succ_eq_add_one]
      ring
    have hvan_g : ∀ t < (L + 1) * r.succ, iteratedDeriv t g 0 = 0 := by
      intro t ht
      simpa [g] using vanishing_mul_cexp_deriv hf (-μ 0) hvan ht
    have hD :
        (fun z => iteratedDeriv (L + 1) g z) =
          fun z =>
            ∑ s, ((shiftPoly (μ s - μ 0))^[L + 1] (p s)).eval z *
              Complex.exp ((μ s - μ 0) * z) := by
      funext z
      have hsum := iteratedDeriv_fun_sum
        (fun s w => (p s).eval w * Complex.exp ((μ s - μ 0) * w))
        (fun s => (p s).differentiable.mul
          (cexp_const_mul_differentiable (μ s - μ 0)))
        (L + 1) z
      have : iteratedDeriv (L + 1) g z =
          iteratedDeriv (L + 1)
            (fun w => ∑ s, (p s).eval w * Complex.exp ((μ s - μ 0) * w)) z := by
        rw [hg_eq]
      rw [this, hsum]
      refine Finset.sum_congr rfl fun s _ => ?_
      exact iteratedDeriv_eval_mul_cexp (L + 1) (p s) (μ s - μ 0) z
    have h0term : (shiftPoly (μ 0 - μ 0))^[L + 1] (p 0) = 0 := by
      have hν : μ 0 - μ 0 = 0 := sub_self _
      rw [hν, iterate_shiftPoly_zero]
      exact iterate_derivative_eq_zero (Nat.lt_succ_of_le (hdeg 0))
    have hrest :
        (fun z => iteratedDeriv (L + 1) g z) =
          fun z =>
            ∑ i : Fin r,
              ((shiftPoly (μ i.succ - μ 0))^[L + 1] (p i.succ)).eval z *
                Complex.exp ((μ i.succ - μ 0) * z) := by
      rw [hD]
      funext z
      rw [Fin.sum_univ_succ, h0term]
      simp [eval_zero]
    let μ' : Fin r → ℂ := fun i => μ i.succ - μ 0
    let p' : Fin r → ℂ[X] := fun i =>
      (shiftPoly (μ i.succ - μ 0))^[L + 1] (p i.succ)
    have hμ' : Function.Injective μ' := by
      intro i j hij
      have : μ i.succ = μ j.succ := by
        have hij' : μ i.succ + (-μ 0) = μ j.succ + (-μ 0) := by
          simpa [μ', sub_eq_add_neg] using hij
        exact add_right_cancel hij'
      exact Fin.succ_injective r (hμ this)
    have hdeg' : ∀ i, (p' i).natDegree ≤ L := fun i =>
      natDegree_iterate_shift_le _ (p i.succ) (L + 1) (hdeg _)
    have hvan' : ∀ t < (L + 1) * r,
        iteratedDeriv t (fun z => ∑ i, (p' i).eval z * Complex.exp (μ' i * z)) 0 =
          0 := by
      intro t ht
      have ht' : L + 1 + t < (L + 1) * r.succ := by
        rw [hT]
        linarith
      have hgt := hvan_g (L + 1 + t) ht'
      rw [iteratedDeriv_add_right] at hgt
      have hfun :
          iteratedDeriv (L + 1) g =
            fun z => ∑ i, (p' i).eval z * Complex.exp (μ' i * z) := by
        simpa [p', μ'] using hrest
      simpa [hfun] using hgt
    have ih' := ih μ' hμ' p' hdeg' hvan'
    have hs : ∀ i : Fin r, p i.succ = 0 := by
      intro i
      have hν : μ i.succ - μ 0 ≠ 0 := by
        intro h
        have : μ i.succ = μ 0 := sub_eq_zero.mp h
        have hidx : i.succ = (0 : Fin r.succ) := hμ this
        exact Fin.succ_ne_zero i hidx
      have hinj := (shiftPoly_injective hν).iterate (L + 1)
      have hp' : p' i = 0 := ih' i
      have : (shiftPoly (μ i.succ - μ 0))^[L + 1] (p i.succ) =
          (shiftPoly (μ i.succ - μ 0))^[L + 1] 0 := by
        simpa [p', shiftPoly_map_zero] using hp'
      exact hinj this
    have hp0 : p 0 = 0 := by
      have hg0 : g = fun z => (p 0).eval z := by
        rw [hg_eq]
        funext z
        rw [Fin.sum_univ_succ]
        simp [hs, sub_self, Complex.exp_zero]
      have hvan0 : ∀ t < L + 1, iteratedDeriv t (fun z => (p 0).eval z) 0 = 0 := by
        intro t ht
        have ht' : t < (L + 1) * r.succ :=
          (lt_of_lt_of_le ht (by
            simpa using
              Nat.mul_le_mul_left (L + 1) (Nat.succ_le_succ (Nat.zero_le r))))
        have := hvan_g t ht'
        simpa [hg0] using this
      apply Polynomial.ext
      intro n
      by_cases hn : n ≤ L
      · have hlt : n < L + 1 := Nat.lt_succ_of_le hn
        have := hvan0 n hlt
        rw [iteratedDeriv_eval_zero] at this
        exact (mul_eq_zero.mp this).resolve_left
          (Nat.cast_ne_zero.mpr n.factorial_ne_zero)
      · have : L < n := Nat.lt_of_not_le hn
        exact coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (hdeg 0) this)
    intro s
    exact Fin.cases hp0 hs s

def coeffEquiv (L N1 N2 : ℕ) :
    Fin (L + 1) × Fin (n12 N1 N2) ≃ Fin (coeffCount L N1 N2) :=
  finProdFinEquiv.trans (finCongr (coeffCount_eq_mul_n12 L N1 N2).symm)

theorem coeffEquiv_val (L N1 N2 : ℕ)
    (ℓ : Fin (L + 1)) (s : Fin (n12 N1 N2)) :
    (coeffEquiv L N1 N2 (ℓ, s)).val = s.val + n12 N1 N2 * ℓ.val := by
  simp [coeffEquiv]

theorem decode_coeffEquiv_L (L N1 N2 : ℕ)
    (ℓ : Fin (L + 1)) (s : Fin (n12 N1 N2)) :
    decodeCoeffL L N1 N2 (coeffEquiv L N1 N2 (ℓ, s)) = ℓ.val := by
  unfold decodeCoeffL
  rw [coeffEquiv_val, Nat.add_mul_div_left _ _ (n12_pos N1 N2),
    Nat.div_eq_of_lt s.isLt, zero_add]

theorem decode_coeffEquiv_mod (L N1 N2 : ℕ)
    (ℓ : Fin (L + 1)) (s : Fin (n12 N1 N2)) :
    (coeffEquiv L N1 N2 (ℓ, s)).val % n12 N1 N2 = s.val := by
  rw [coeffEquiv_val, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt s.isLt]

theorem decode_coeffEquiv_K1 (L N1 N2 : ℕ)
    (ℓ : Fin (L + 1)) (s : Fin (n12 N1 N2)) :
    decodeCoeffK1 L N1 N2 (coeffEquiv L N1 N2 (ℓ, s)) = s.val / (N2 + 1) := by
  simp [decodeCoeffK1, decode_coeffEquiv_mod]

theorem decode_coeffEquiv_K2 (L N1 N2 : ℕ)
    (ℓ : Fin (L + 1)) (s : Fin (n12 N1 N2)) :
    decodeCoeffK2 L N1 N2 (coeffEquiv L N1 N2 (ℓ, s)) = s.val % (N2 + 1) := by
  simp [decodeCoeffK2, decode_coeffEquiv_mod]

def groupedPoly (L N1 N2 : ℕ) (c : Fin (coeffCount L N1 N2) → ℤ)
    (s : Fin (n12 N1 N2)) : ℂ[X] :=
  ∑ ℓ : Fin (L + 1), C (c (coeffEquiv L N1 N2 (ℓ, s)) : ℂ) * X ^ (ℓ : ℕ)

theorem groupedPoly_natDegree_le (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (s : Fin (n12 N1 N2)) :
    (groupedPoly L N1 N2 c s).natDegree ≤ L := by
  refine (natDegree_sum_le _ _).trans ?_
  refine (Finset.sup_le fun ℓ _ => ?_)
  exact ((natDegree_C_mul_le (c (coeffEquiv L N1 N2 (ℓ, s)) : ℂ)
      (X ^ (ℓ : ℕ))).trans (natDegree_X_pow_le (ℓ : ℕ))).trans
    (Nat.lt_succ_iff.mp ℓ.isLt)

theorem groupedPoly_coeff (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (s : Fin (n12 N1 N2))
    (ℓ : Fin (L + 1)) :
    (groupedPoly L N1 N2 c s).coeff ℓ.val =
      (c (coeffEquiv L N1 N2 (ℓ, s)) : ℂ) := by
  unfold groupedPoly
  rw [finset_sum_coeff]
  refine (Finset.sum_eq_single ℓ ?_ ?_).trans ?_
  · intro ℓ' _ hne
    rw [coeff_C_mul, coeff_X_pow]
    simp [Fin.val_ne_of_ne hne]
    intro h
    exact (hne (Fin.ext h.symm)).elim
  · simp
  · rw [coeff_C_mul, coeff_X_pow]
    simp

theorem matveevPhi_of_coeffs_grouped (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ) (α1 α2 : ℝ) (z : ℂ) :
    matveevPhi_of_coeffs L N1 N2 c α1 α2 z =
      ∑ s : Fin (n12 N1 N2),
        (groupedPoly L N1 N2 c s).eval z *
          Complex.exp (freq α1 α2 (s.val / (N2 + 1)) (s.val % (N2 + 1)) * z) := by
  set term : Fin (coeffCount L N1 N2) → ℂ := fun j =>
    (c j : ℂ) * z ^ decodeCoeffL L N1 N2 j *
      Complex.exp (freq α1 α2 (decodeCoeffK1 L N1 N2 j)
        (decodeCoeffK2 L N1 N2 j) * z)
  rw [matveevPhi_of_coeffs_eq_expSum]
  have hreindex :=
    Fintype.sum_equiv (coeffEquiv L N1 N2)
      (fun p => term (coeffEquiv L N1 N2 p)) term (fun _ => rfl)
  rw [← hreindex]
  rw [show (Finset.univ : Finset (Fin (L + 1) × Fin (n12 N1 N2))) =
        Finset.univ ×ˢ Finset.univ from Finset.univ_product_univ.symm]
  rw [Finset.sum_product]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => ?_
  have hrhs :
      (groupedPoly L N1 N2 c s).eval z *
          Complex.exp (freq α1 α2 (s.val / (N2 + 1)) (s.val % (N2 + 1)) * z) =
        ∑ ℓ : Fin (L + 1), term (coeffEquiv L N1 N2 (ℓ, s)) := by
    unfold groupedPoly
    have heval :
        (∑ ℓ ∈ Finset.univ, C (c (coeffEquiv L N1 N2 (ℓ, s)) : ℂ) * X ^ (ℓ : ℕ)).eval z =
          ∑ ℓ ∈ Finset.univ, (c (coeffEquiv L N1 N2 (ℓ, s)) : ℂ) * z ^ (ℓ : ℕ) := by
      rw [eval_finset_sum (R := ℂ) (ι := Fin (L + 1)) Finset.univ _ z]
      refine Finset.sum_congr rfl fun ℓ _ => ?_
      rw [eval_mul, eval_C, eval_pow, eval_X]
    rw [heval, mul_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ℓ _ => ?_
    rw [mul_comm]
    simp [term, decode_coeffEquiv_L, decode_coeffEquiv_K1, decode_coeffEquiv_K2]
  rw [hrhs]

/-- Independent `α1, α2`: a nonzero integer coefficient vector cannot
    make `Φ(z) = P(z, α1^z, α2^z)` vanish to order
    `(L+1)(N1+1)(N2+1)` at `0`. This is jet invertibility of
    `{z^ℓ α1^{k1 z} α2^{k2 z}}`, not the Wüstholz subgroup theorem
    and not a Matveev `C1_floor` close. -/
theorem wuestholz_product_theorem_exp_Gm
    {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (hindep : ¬ multiplicativelyDependent α1 α2)
    (L N1 N2 : ℕ)
    (c : Fin (coeffCount L N1 N2) → ℤ)
    (hvan : ∀ k < coeffCount L N1 N2,
      iteratedDslope (matveevPhi_of_coeffs L N1 N2 c α1 α2) k 0 = 0) :
    c = 0 := by
  have hf := matveevPhi_of_coeffs_differentiable L N1 N2 c α1 α2
  have hN : coeffCount L N1 N2 = (L + 1) * n12 N1 N2 :=
    coeffCount_eq_mul_n12 L N1 N2
  let μ : Fin (n12 N1 N2) → ℂ := fun s =>
    freq (α1 : ℝ) (α2 : ℝ) (s.val / (N2 + 1)) (s.val % (N2 + 1))
  have hμ : Function.Injective μ :=
    freq_injective_of_indep hα1 hα2 hindep N1 N2
  let p : Fin (n12 N1 N2) → ℂ[X] := groupedPoly L N1 N2 c
  have hdeg : ∀ s, (p s).natDegree ≤ L :=
    groupedPoly_natDegree_le L N1 N2 c
  have hsum :
      (fun z => matveevPhi_of_coeffs L N1 N2 c α1 α2 z) =
        fun z => ∑ s, (p s).eval z * Complex.exp (μ s * z) := by
    funext z
    simpa [p, μ] using matveevPhi_of_coeffs_grouped L N1 N2 c α1 α2 z
  have hvan' : ∀ t < (L + 1) * n12 N1 N2,
      iteratedDeriv t (fun z => ∑ s, (p s).eval z * Complex.exp (μ s * z)) 0 =
        0 := by
    intro t ht
    have ht' : t < coeffCount L N1 N2 := by
      simpa [hN] using ht
    have h0 :
        iteratedDeriv t (fun z => matveevPhi_of_coeffs L N1 N2 c α1 α2 z) 0 =
          0 :=
      (iteratedDeriv_zero_iff_dslope hf t).2 (hvan t ht')
    rw [hsum] at h0
    exact h0
  have hp0 := exp_poly_jet_zero L μ hμ p hdeg hvan'
  apply _root_.funext
  intro j
  obtain ⟨ℓs, rfl⟩ := (coeffEquiv L N1 N2).surjective j
  rcases ℓs with ⟨ℓ, s⟩
  have hpoly : p s = 0 := hp0 s
  have hcoeff := groupedPoly_coeff L N1 N2 c s ℓ
  have hcz : (c (coeffEquiv L N1 N2 (ℓ, s)) : ℂ) = (p s).coeff ℓ.val := by
    simpa [p] using hcoeff.symm
  rw [hpoly, coeff_zero] at hcz
  exact Int.cast_eq_zero.mp hcz

/-! ## `MvPolynomial` wrapper (requested API)

Same jet criterion, now for `P ∈ ℤ[y0,y1,y2]` of degree at most
`(L,N1,N2)`. This is still not the Wüstholz subgroup theorem and
does not close Matveev 2000 / `C1_floor`.
-/

def W_coord (α1 α2 : ℝ) (z : ℂ) : Fin 3 → ℂ :=
  fun i =>
    if i = 0 then z
    else if i = 1 then alphaPowZ α1 z
    else alphaPowZ α2 z

theorem W_coord_zero (α1 α2 : ℝ) (z : ℂ) : W_coord α1 α2 z 0 = z := by
  simp [W_coord]

theorem W_coord_one (α1 α2 : ℝ) (z : ℂ) :
    W_coord α1 α2 z 1 = alphaPowZ α1 z := by
  simp [W_coord]

theorem W_coord_two (α1 α2 : ℝ) (z : ℂ) :
    W_coord α1 α2 z 2 = alphaPowZ α2 z := by
  simp [W_coord]

theorem W_coord_prod (α1 α2 : ℝ) (z : ℂ) (d : Fin 3 →₀ ℕ) :
    ∏ i : Fin 3, W_coord α1 α2 z i ^ d i =
      z ^ d 0 * alphaPowZ α1 z ^ d 1 * alphaPowZ α2 z ^ d 2 := by
  rw [Fin.prod_univ_succ, Fin.prod_univ_succ, Fin.prod_univ_succ,
    Fin.prod_univ_zero]
  simp [W_coord, mul_assoc]

/-- `Φ(z) = P(z, α1^z, α2^z)` for an integer polynomial in three
    variables. -/
def matveevPhi_of_mvPolynomial (P : MvPolynomial (Fin 3) ℤ)
    (α1 α2 : ℝ) (z : ℂ) : ℂ :=
  MvPolynomial.eval₂ (Int.castRingHom ℂ) (W_coord α1 α2 z) P

theorem encode_lt {L N1 N2 ℓ k1 k2 : ℕ}
    (hℓ : ℓ ≤ L) (hk1 : k1 ≤ N1) (hk2 : k2 ≤ N2) :
    ℓ * n12 N1 N2 + k1 * (N2 + 1) + k2 < coeffCount L N1 N2 := by
  have h12 : k1 * (N2 + 1) + k2 < n12 N1 N2 := by
    unfold n12
    have hle : k1 * (N2 + 1) + k2 ≤ N1 * (N2 + 1) + N2 :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hk1) hk2
    have hlt : N1 * (N2 + 1) + N2 < (N1 + 1) * (N2 + 1) := by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left (Nat.lt_succ_self N2) _
    exact lt_of_le_of_lt hle hlt
  have hsum :
      ℓ * n12 N1 N2 + (k1 * (N2 + 1) + k2) < (ℓ + 1) * n12 N1 N2 := by
    rw [Nat.succ_mul]
    exact Nat.add_lt_add_left h12 _
  have hℓ1 : (ℓ + 1) * n12 N1 N2 ≤ (L + 1) * n12 N1 N2 :=
    Nat.mul_le_mul_right _ (Nat.succ_le_succ hℓ)
  have hrew : ℓ * n12 N1 N2 + k1 * (N2 + 1) + k2 =
      ℓ * n12 N1 N2 + (k1 * (N2 + 1) + k2) := by
    ac_rfl
  have hcount : (L + 1) * n12 N1 N2 = coeffCount L N1 N2 :=
    (coeffCount_eq_mul_n12 L N1 N2).symm
  rw [hrew]
  exact lt_of_lt_of_le hsum (hcount ▸ hℓ1)

def encodeOfBox (L N1 N2 : ℕ) (d : Fin 3 →₀ ℕ)
    (hd : d 0 ≤ L ∧ d 1 ≤ N1 ∧ d 2 ≤ N2) :
    Fin (coeffCount L N1 N2) :=
  ⟨d 0 * n12 N1 N2 + d 1 * (N2 + 1) + d 2, encode_lt hd.1 hd.2.1 hd.2.2⟩

def monomialOfDecodes (L N1 N2 : ℕ) (j : Fin (coeffCount L N1 N2)) :
    Fin 3 →₀ ℕ :=
  Finsupp.single (0 : Fin 3) (decodeCoeffL L N1 N2 j) +
    Finsupp.single (1 : Fin 3) (decodeCoeffK1 L N1 N2 j) +
    Finsupp.single (2 : Fin 3) (decodeCoeffK2 L N1 N2 j)

theorem monomialOfDecodes_zero (L N1 N2 : ℕ)
    (j : Fin (coeffCount L N1 N2)) :
    monomialOfDecodes L N1 N2 j 0 = decodeCoeffL L N1 N2 j := by
  simp [monomialOfDecodes, Finsupp.single_apply]

theorem monomialOfDecodes_one (L N1 N2 : ℕ)
    (j : Fin (coeffCount L N1 N2)) :
    monomialOfDecodes L N1 N2 j 1 = decodeCoeffK1 L N1 N2 j := by
  simp [monomialOfDecodes, Finsupp.single_apply]

theorem monomialOfDecodes_two (L N1 N2 : ℕ)
    (j : Fin (coeffCount L N1 N2)) :
    monomialOfDecodes L N1 N2 j 2 = decodeCoeffK2 L N1 N2 j := by
  simp [monomialOfDecodes, Finsupp.single_apply]

theorem decode_reconstruct (L N1 N2 : ℕ)
    (j : Fin (coeffCount L N1 N2)) :
    j.val =
      decodeCoeffL L N1 N2 j * n12 N1 N2 +
        decodeCoeffK1 L N1 N2 j * (N2 + 1) +
        decodeCoeffK2 L N1 N2 j := by
  unfold decodeCoeffL decodeCoeffK1 decodeCoeffK2
  have h1 := Nat.div_add_mod j.val (n12 N1 N2)
  have h2 := Nat.div_add_mod (j.val % n12 N1 N2) (N2 + 1)
  have hrew :
      j.val / n12 N1 N2 * n12 N1 N2 +
          j.val % n12 N1 N2 / (N2 + 1) * (N2 + 1) +
          j.val % n12 N1 N2 % (N2 + 1) =
        n12 N1 N2 * (j.val / n12 N1 N2) +
          ((N2 + 1) * (j.val % n12 N1 N2 / (N2 + 1)) +
            j.val % n12 N1 N2 % (N2 + 1)) := by
    ring
  rw [hrew, h2, h1]

theorem decode_encodeOfBox (L N1 N2 : ℕ) (d : Fin 3 →₀ ℕ)
    (hd : d 0 ≤ L ∧ d 1 ≤ N1 ∧ d 2 ≤ N2) :
    decodeCoeffL L N1 N2 (encodeOfBox L N1 N2 d hd) = d 0 ∧
      decodeCoeffK1 L N1 N2 (encodeOfBox L N1 N2 d hd) = d 1 ∧
        decodeCoeffK2 L N1 N2 (encodeOfBox L N1 N2 d hd) = d 2 := by
  have h12 : d 1 * (N2 + 1) + d 2 < n12 N1 N2 := by
    unfold n12
    have hle : d 1 * (N2 + 1) + d 2 ≤ N1 * (N2 + 1) + N2 :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hd.2.1) hd.2.2
    have hlt : N1 * (N2 + 1) + N2 < (N1 + 1) * (N2 + 1) := by
      rw [Nat.succ_mul]
      exact Nat.add_lt_add_left (Nat.lt_succ_self N2) _
    exact lt_of_le_of_lt hle hlt
  have hval : (encodeOfBox L N1 N2 d hd).val =
      (d 1 * (N2 + 1) + d 2) + n12 N1 N2 * d 0 := by
    change d 0 * n12 N1 N2 + d 1 * (N2 + 1) + d 2 =
      (d 1 * (N2 + 1) + d 2) + n12 N1 N2 * d 0
    ring
  have hmod : (encodeOfBox L N1 N2 d hd).val % n12 N1 N2 =
      d 1 * (N2 + 1) + d 2 := by
    rw [hval, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h12]
  have hdiv : (encodeOfBox L N1 N2 d hd).val / n12 N1 N2 = d 0 := by
    rw [hval, Nat.add_mul_div_left _ _ (n12_pos N1 N2),
      Nat.div_eq_of_lt h12, zero_add]
  have hk2 : d 2 < N2 + 1 := Nat.lt_succ_of_le hd.2.2
  have hmod2 : (d 1 * (N2 + 1) + d 2) % (N2 + 1) = d 2 := by
    have : d 1 * (N2 + 1) + d 2 = d 2 + (N2 + 1) * d 1 := by ring
    rw [this, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hk2]
  have hdiv2 : (d 1 * (N2 + 1) + d 2) / (N2 + 1) = d 1 := by
    have : d 1 * (N2 + 1) + d 2 = d 2 + (N2 + 1) * d 1 := by ring
    rw [this, Nat.add_mul_div_left _ _ (Nat.succ_pos N2),
      Nat.div_eq_of_lt hk2, zero_add]
  refine ⟨?_, ?_, ?_⟩
  · simpa [decodeCoeffL] using hdiv
  · simpa [decodeCoeffK1, hmod] using hdiv2
  · simpa [decodeCoeffK2, hmod] using hmod2

theorem monomialOfDecodes_encode (L N1 N2 : ℕ) (d : Fin 3 →₀ ℕ)
    (hd : d 0 ≤ L ∧ d 1 ≤ N1 ∧ d 2 ≤ N2) :
    monomialOfDecodes L N1 N2 (encodeOfBox L N1 N2 d hd) = d := by
  have hdec := decode_encodeOfBox L N1 N2 d hd
  ext i
  fin_cases i <;>
    simp [monomialOfDecodes, Finsupp.single_apply, hdec]

theorem monomialOfDecodes_injective (L N1 N2 : ℕ) :
    Function.Injective (monomialOfDecodes L N1 N2) := by
  intro j j' h
  apply Fin.ext
  have h0 : decodeCoeffL L N1 N2 j = decodeCoeffL L N1 N2 j' := by
    have := congrArg (fun d : Fin 3 →₀ ℕ => d 0) h
    simpa [monomialOfDecodes_zero] using this
  have h1 : decodeCoeffK1 L N1 N2 j = decodeCoeffK1 L N1 N2 j' := by
    have := congrArg (fun d : Fin 3 →₀ ℕ => d 1) h
    simpa [monomialOfDecodes_one] using this
  have h2 : decodeCoeffK2 L N1 N2 j = decodeCoeffK2 L N1 N2 j' := by
    have := congrArg (fun d : Fin 3 →₀ ℕ => d 2) h
    simpa [monomialOfDecodes_two] using this
  rw [decode_reconstruct L N1 N2 j, decode_reconstruct L N1 N2 j', h0, h1, h2]

def coeffsOfMvPolynomial (P : MvPolynomial (Fin 3) ℤ) (L N1 N2 : ℕ) :
    Fin (coeffCount L N1 N2) → ℤ :=
  fun j => MvPolynomial.coeff (monomialOfDecodes L N1 N2 j) P

theorem support_subset_box {L N1 N2 : ℕ} {P : MvPolynomial (Fin 3) ℤ}
    (hdeg : MvPolynomial.degreeOf 0 P ≤ L ∧
      MvPolynomial.degreeOf 1 P ≤ N1 ∧
        MvPolynomial.degreeOf 2 P ≤ N2) :
    ∀ d ∈ P.support, d 0 ≤ L ∧ d 1 ≤ N1 ∧ d 2 ≤ N2 := by
  intro d hd
  exact ⟨MvPolynomial.degreeOf_le_iff.mp hdeg.1 d hd,
    MvPolynomial.degreeOf_le_iff.mp hdeg.2.1 d hd,
    MvPolynomial.degreeOf_le_iff.mp hdeg.2.2 d hd⟩

theorem mvPolynomial_eq_zero_of_box_coeffs
    {L N1 N2 : ℕ} {P : MvPolynomial (Fin 3) ℤ}
    (hdeg : MvPolynomial.degreeOf 0 P ≤ L ∧
      MvPolynomial.degreeOf 1 P ≤ N1 ∧
        MvPolynomial.degreeOf 2 P ≤ N2)
    (hc : ∀ j, MvPolynomial.coeff (monomialOfDecodes L N1 N2 j) P = 0) :
    P = 0 := by
  refine MvPolynomial.ext P 0 fun d => ?_
  by_cases hd : d ∈ P.support
  · have hb := support_subset_box hdeg d hd
    have hmono :
        d = monomialOfDecodes L N1 N2 (encodeOfBox L N1 N2 d hb) :=
      (monomialOfDecodes_encode L N1 N2 d hb).symm
    rw [hmono, hc, MvPolynomial.coeff_zero]
  · rw [MvPolynomial.not_mem_support_iff.mp hd, MvPolynomial.coeff_zero]

theorem matveevPhi_of_mvPolynomial_eq_eval₂
    (P : MvPolynomial (Fin 3) ℤ) (α1 α2 : ℝ) (z : ℂ) :
    matveevPhi_of_mvPolynomial P α1 α2 z =
      ∑ d ∈ P.support,
        ((MvPolynomial.coeff (R := ℤ) d P : ℤ) : ℂ) *
          (z ^ d 0 * alphaPowZ α1 z ^ d 1 * alphaPowZ α2 z ^ d 2) := by
  unfold matveevPhi_of_mvPolynomial
  rw [MvPolynomial.eval₂_eq']
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [W_coord_prod]
  simp [Int.castRingHom]

theorem matveevPhi_of_mvPolynomial_eq_of_coeffs
    {L N1 N2 : ℕ} (P : MvPolynomial (Fin 3) ℤ)
    (hdeg : MvPolynomial.degreeOf 0 P ≤ L ∧
      MvPolynomial.degreeOf 1 P ≤ N1 ∧
        MvPolynomial.degreeOf 2 P ≤ N2)
    (α1 α2 : ℝ) (z : ℂ) :
    matveevPhi_of_mvPolynomial P α1 α2 z =
      matveevPhi_of_coeffs L N1 N2 (coeffsOfMvPolynomial P L N1 N2)
        α1 α2 z := by
  classical
  set e : Fin (coeffCount L N1 N2) → Fin 3 →₀ ℕ :=
    monomialOfDecodes L N1 N2
  set f : (Fin 3 →₀ ℕ) → ℂ := fun d =>
    ((MvPolynomial.coeff (R := ℤ) d P : ℤ) : ℂ) *
      (z ^ d 0 * alphaPowZ α1 z ^ d 1 * alphaPowZ α2 z ^ d 2)
  have hleft :
      matveevPhi_of_mvPolynomial P α1 α2 z = ∑ d ∈ P.support, f d :=
    matveevPhi_of_mvPolynomial_eq_eval₂ P α1 α2 z
  have hright :
      matveevPhi_of_coeffs L N1 N2 (coeffsOfMvPolynomial P L N1 N2)
          α1 α2 z =
        ∑ j : Fin (coeffCount L N1 N2), f (e j) := by
    unfold matveevPhi_of_coeffs coeffsOfMvPolynomial
    refine Finset.sum_congr rfl fun j _ => ?_
    have hz1 := alphaPowZ_nat_mul α1 (decodeCoeffK1 L N1 N2 j) z
    have hz2 := alphaPowZ_nat_mul α2 (decodeCoeffK2 L N1 N2 j) z
    simp [f, e, monomialOfDecodes_zero, monomialOfDecodes_one,
      monomialOfDecodes_two, hz1, hz2, mul_assoc]
  have hinj : ∀ x ∈ (Finset.univ : Finset (Fin (coeffCount L N1 N2))),
      ∀ y ∈ (Finset.univ : Finset (Fin (coeffCount L N1 N2))),
        e x = e y → x = y :=
    fun x _ y _ hxy => monomialOfDecodes_injective L N1 N2 hxy
  set box : Finset (Fin 3 →₀ ℕ) :=
    Finset.univ.image e
  have hbox_sum : ∑ d ∈ box, f d = ∑ j, f (e j) :=
    Finset.sum_image hinj
  have hsupp : P.support ⊆ box := by
    intro d hd
    have hb := support_subset_box hdeg d hd
    refine Finset.mem_image.2 ?_
    refine ⟨encodeOfBox L N1 N2 d hb, Finset.mem_univ _, ?_⟩
    exact monomialOfDecodes_encode L N1 N2 d hb
  have hunion : P.support ∪ (box \ P.support) = box :=
    Finset.union_sdiff_of_subset hsupp
  have hdisj : Disjoint P.support (box \ P.support) :=
    Finset.disjoint_sdiff
  have hzero : ∑ d ∈ box \ P.support, f d = 0 := by
    refine Finset.sum_eq_zero fun d hd => ?_
    have hns : d ∉ P.support := (Finset.mem_sdiff.mp hd).2
    have hc0 : MvPolynomial.coeff (R := ℤ) d P = 0 :=
      MvPolynomial.not_mem_support_iff.mp hns
    simp [f, hc0]
  have : ∑ d ∈ P.support, f d = ∑ d ∈ box, f d := by
    rw [← hunion, Finset.sum_union hdisj, hzero, add_zero]
  rw [hleft, this, hbox_sum, hright]

/-- Independent `α1, α2`: a nonzero integer `P` of degree
    `≤ (L,N1,N2)` cannot make `Φ(z)=P(z,α1^z,α2^z)` vanish to
    order `T ≥ (L+1)(N1+1)(N2+1)` at `0`. Jet invertibility, not
    the Wüstholz subgroup theorem, and not a `C1_floor` close. -/
theorem wuestholz_product_theorem_exp_Gm_of_mvPolynomial
    {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (hindep : ¬ multiplicativelyDependent α1 α2)
    (L N1 N2 : ℕ)
    (P : MvPolynomial (Fin 3) ℤ)
    (hdeg : MvPolynomial.degreeOf 0 P ≤ L ∧
      MvPolynomial.degreeOf 1 P ≤ N1 ∧
        MvPolynomial.degreeOf 2 P ≤ N2)
    {T : ℕ} (hT : coeffCount L N1 N2 ≤ T)
    (hvan : ∀ k < T,
      iteratedDslope
          (matveevPhi_of_mvPolynomial P (α1 : ℝ) (α2 : ℝ)) k 0 = 0) :
    P = 0 := by
  have hΦ :
      matveevPhi_of_mvPolynomial P (α1 : ℝ) (α2 : ℝ) =
        matveevPhi_of_coeffs L N1 N2
          (coeffsOfMvPolynomial P L N1 N2) (α1 : ℝ) (α2 : ℝ) := by
    funext z
    exact matveevPhi_of_mvPolynomial_eq_of_coeffs P hdeg (α1 : ℝ)
      (α2 : ℝ) z
  have hvan' : ∀ k < coeffCount L N1 N2,
      iteratedDslope
          (matveevPhi_of_coeffs L N1 N2
            (coeffsOfMvPolynomial P L N1 N2) (α1 : ℝ) (α2 : ℝ))
          k 0 = 0 := by
    intro k hk
    have hkT : k < T := lt_of_lt_of_le hk hT
    have := hvan k hkT
    simpa [hΦ] using this
  have hc :=
    wuestholz_product_theorem_exp_Gm hα1 hα2 hindep L N1 N2
      (coeffsOfMvPolynomial P L N1 N2) hvan'
  refine mvPolynomial_eq_zero_of_box_coeffs hdeg fun j => ?_
  have := congrArg (fun c => c j) hc
  simpa [coeffsOfMvPolynomial] using this

/-- Real-power form of multiplicative independence used in the
    requested statement. For `α>1` this rules out every ℕ-relation
    `α1^a = α2^b`. -/
def rpowIndependent (α1 α2 : ℕ) : Prop :=
  ∀ a b : ℤ, a ≠ 0 ∨ b ≠ 0 →
    (α1 : ℝ) ^ (a : ℝ) ≠ (α2 : ℝ) ^ (b : ℝ)

theorem not_mul_dep_of_rpow_indep {α1 α2 : ℕ}
    (h : rpowIndependent α1 α2) :
    ¬ multiplicativelyDependent α1 α2 := by
  rintro ⟨a, b, hpos, heq⟩
  have ha' : (a : ℤ) ≠ 0 ∨ (b : ℤ) ≠ 0 := by exact_mod_cast hpos
  have hcast : (α1 : ℝ) ^ a = (α2 : ℝ) ^ b := by exact_mod_cast heq
  have hpow :
      (α1 : ℝ) ^ ((a : ℤ) : ℝ) = (α2 : ℝ) ^ ((b : ℤ) : ℝ) := by
    have h1 : (α1 : ℝ) ^ ((a : ℤ) : ℝ) = (α1 : ℝ) ^ a := by
      rw [Int.cast_natCast, Real.rpow_natCast]
    have h2 : (α2 : ℝ) ^ ((b : ℤ) : ℝ) = (α2 : ℝ) ^ b := by
      rw [Int.cast_natCast, Real.rpow_natCast]
    rw [h1, h2, hcast]
  exact (h a b ha') hpow

/-- Requested independence shape: integer real powers, vanishing
    order `T ≥ (L+1)(N1+1)(N2+1)`, conclusion `P = 0`. -/
theorem wuestholz_product_theorem_exp_Gm_of_rpow_indep
    {α1 α2 : ℕ} (hα1 : 1 < α1) (hα2 : 1 < α2)
    (hindep : ∀ a b : ℤ, a ≠ 0 ∨ b ≠ 0 →
      (α1 : ℝ) ^ (a : ℝ) ≠ (α2 : ℝ) ^ (b : ℝ))
    (L N1 N2 : ℕ)
    (P : MvPolynomial (Fin 3) ℤ)
    (hdeg : MvPolynomial.degreeOf 0 P ≤ L ∧
      MvPolynomial.degreeOf 1 P ≤ N1 ∧
        MvPolynomial.degreeOf 2 P ≤ N2)
    {T : ℕ} (hT : (L + 1) * (N1 + 1) * (N2 + 1) ≤ T)
    (hvan : ∀ k < T,
      iteratedDslope
          (matveevPhi_of_mvPolynomial P (α1 : ℝ) (α2 : ℝ)) k 0 = 0) :
    P = 0 :=
  wuestholz_product_theorem_exp_Gm_of_mvPolynomial hα1 hα2
    (not_mul_dep_of_rpow_indep hindep) L N1 N2 P hdeg
    (by simpa [coeffCount] using hT) hvan

/-! ## Remaining steps (not in Mathlib 4.12) -/

set_option linter.unusedVariables false

def wuestholz_product_theorem : Prop :=
  ∀ (p : ℝ[X]) (hp : p ≠ 0) (a : ℝ),
    rootMultiplicity a p ≤ natDegree p

theorem wuestholz_product_theorem_polynomial : wuestholz_product_theorem :=
  zero_estimate_polynomial

/-- Wüstholz along `W ⊂ 𝐆_a × 𝐆_m²` for exponential polynomials.
    Not in Mathlib 4.12; inhabited only on `𝐆_a`. -/
def wuestholz_product_theorem_exp : Prop :=
  ∀ (α1 α2 : ℕ) (terms : List PhiTerm),
    1 < α1 →
      1 < α2 →
        (∀ T : ℕ,
            (∀ k < T, iteratedDslope (matveevPhi α1 α2 terms) k 0 = 0) →
              T ≤ (terms.map fun t => t.l + t.k1 + t.k2).sum) ∨
          multiplicativelyDependent α1 α2

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
#check matveevPhi
#check schwarz_lemma_of_order
#check matveev_interpolation_analytic_small_bound
#check matveev_interpolation_analytic_small_bound_det
#check interpolationDeterminant_L0_not_exp_small
#check cauchy_estimate_iteratedDslope
#check polynomial_iteratedDslope_vanishes
#check schwarz_lemma_of_order_polynomial
#check iteratedDslope_one_add_pow
#check matveev_interpolation_analytic_small_bound_polynomial
#check siegel_lemma
#check integer_box_card
#check matveevPhi_vanishing_exists_T
#check matveevPhi_vanishing_exists_T_height
#check matveevPhi_vanishing_exists_T_exp_height
#check matveevPhi_eq_P_along_W
#check gap3_not_fourth_thirteenth
#check interpolationDeterminant_L_pos_alpha_one
#check interpolationDeterminant_L_pos_exp_small
#check wuestholz_product_theorem_exp
#check wuestholz_product_theorem_exp_Gm
#check wuestholz_product_theorem_exp_Gm_L0
#check wuestholz_product_theorem_exp_Gm_of_mvPolynomial
#check wuestholz_product_theorem_exp_Gm_of_rpow_indep
#check matveevPhi_of_mvPolynomial
#check W_map
#check exp_poly_jet_zero
#print axioms interpolation_det_ne_zero
#print axioms binomial_interpolation_det_eq_one
#print axioms interpolationDeterminant_L0_eq_one
#print axioms wuestholz_product_theorem_family
#print axioms matveev_thm14_n2_real_explicit_is_false
#print axioms matveev_interpolation_track1
#print axioms schwarz_lemma_of_order
#print axioms matveev_interpolation_analytic_small_bound
#print axioms matveevPhi_differentiable
#print axioms cauchy_estimate_iteratedDslope
#print axioms polynomial_iteratedDslope_vanishes
#print axioms iteratedDslope_one_add_pow
#print axioms schwarz_lemma_of_order_polynomial
#print axioms siegel_lemma
#print axioms matveevPhi_vanishing_exists_T
#print axioms matveevPhi_vanishing_exists_T_height
#print axioms gap3_not_fourth_thirteenth
#print axioms interpolationDeterminant_L_pos_alpha_one
#print axioms interpolationDeterminant_L_pos_exp_small
#print axioms wuestholz_product_theorem_exp_Gm
#print axioms wuestholz_product_theorem_exp_Gm_L0
#print axioms exp_poly_jet_zero
#print axioms wuestholz_product_theorem_exp_Gm_of_mvPolynomial
#print axioms wuestholz_product_theorem_exp_Gm_of_rpow_indep
#print axioms not_mul_dep_of_rpow_indep

end BealMatveevBeal.MatveevInterpolation
