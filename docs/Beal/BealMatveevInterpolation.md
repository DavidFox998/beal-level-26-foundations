# MatveevInterpolation — genuine interpolation track (not bare-real Matveev)

Lean: [`MatveevInterpolation.lean`](../../MatveevInterpolation.lean)
(root module; `Beal/Matveev/MatveevInterpolation.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.MatveevInterpolation`.
Concept DOI `10.5281/zenodo.22379293`. C1_floor stays `143186215390` by `rfl`.

Mathlib 4.12 has no Matveev interpolation, no Wüstholz product theorem
for exponential polynomials, and no Bugeaud κ=1 refinement. This file
starts that work honestly. It does **not** import
`Beal/Matveev/MatveevThm14General` (that package owns the `Beal/` prefix
on `LEAN_PATH`).

## What is proved (0 sorry)

- `C1_floor = 143186215390`, `height_B0_nat = 104382751019310000000`,
  `B0_nat = 1000000` (`rfl` / `decide`).
- Rational height `h(a,b) = log max(a,b)` and Liouville
  `|a/b| ≥ exp(−h(a,b))` for positive integers `a,b`.
- Interpolation determinant `Δ(L,K,N1,N2,α1,α2)` as on Matveev 2000 p.5:
  columns `(ℓ,k)` with `0 ≤ ℓ ≤ L`, `0 ≤ k ≤ K`, entries
  `(k.choose i) α1^{ℓ N1} α2^{ℓ N2}`.
- Vandermonde specialisation `interpolation_det_ne_zero` and binomial
  specialisation `interpolationDeterminant_L0_eq_one` (`Δ = 1` when
  `L = N1 = N2 = 0`).
- Product theorem on `𝐆_a`: multiplicity of a nonzero polynomial is at
  most its degree; additivity on products and finite lists
  (`wuestholz_product_theorem_Ga`, `wuestholz_product_theorem_family`).
- Hadamard size `|Δ| ≤ n! X^n` with `X` from binomial / height bounds
  (`size_upper_bound_hadamard`). Analytic estimates `|log α| ≤ α − 1`
  for `α ≥ 1`.
- Matveev §3 auxiliary `Φ(z) = Σ c z^ℓ α1^{k1 z} α2^{k2 z}` is entire
  (`matveevPhi_differentiable`).
- Higher-order Schwarz: a zero of order `T` at `0` gives
  `|f|_r ≤ (r/R)^T |f|_R` (`schwarz_lemma_of_order`), via iterated
  `dslope` and Mathlib max-modulus. Jensen is not in Mathlib 4.12.
- Cauchy estimates: `|iteratedDslope f n 0| ≤ M / R^n`
  (`cauchy_estimate_iteratedDslope`); first-derivative form
  `|f'(0)| ≤ M/R`. Specialised to `Φ` as
  `matveevPhi_cauchy_estimate`.
- Polynomial vanishing: `T ≤ rootMultiplicity 0 p` implies the first
  `T` iterated dslopes of `p.eval` vanish
  (`polynomial_iteratedDslope_vanishes`). Schwarz and the analytic
  small bound are therefore inhabited on `𝐆_a`
  (`schwarz_lemma_of_order_polynomial`,
  `matveev_interpolation_analytic_small_bound_polynomial`).
- Binomial matrix entries are those Taylor coefficients:
  `C(j,i) = iteratedDslope (1+z)^j i 0`
  (`iteratedDslope_one_add_pow`).
- Siegel / pigeonhole: an underdetermined integer system
  `M c = 0` with more unknowns than equations has a nonzero
  integer solution of controlled height (`siegel_lemma`,
  Mathlib `Int.Matrix.exists_ne_zero_int_vec_norm_le`;
  `integer_box_card` records the box count).
- `matveevPhi_vanishing_exists_T`: integer coefficients with
  Siegel height such that the G_a specialisation (`α1=α2=1`)
  of `Φ` vanishes to order `siegel_T = N/2` at `0`. Height
  forms: `‖c‖ ≤ N` and `‖c‖ ≤ exp N`. Exact exponential-jet
  vanishing is not an integer linear system (derivatives
  carry `log α`).
- `Φ(z) = P(z, α1^z, α2^z)` along the curve
  `W = {(z, α1^z, α2^z)}` (`matveevPhi_eq_P_along_W`).
- Gap-3 is not the relation `A^4 = (B+3)^13`
  (`gap3_not_fourth_thirteenth`). Remaining multiplicative
  relations are Baker / LLL (`baker_bound_gap3`).
- `L≥1` and `α1=α2=1` forces `Δ=0` (duplicate columns), so
  `|Δ| ≤ exp(−c L K)` holds degenerately
  (`interpolationDeterminant_L_pos_exp_small`). The `L=0`
  binomial has `Δ=1`.
- Frequencies `k1 log α1 + k2 log α2` are distinct if `α1,α2`
  are multiplicatively independent (`freq_injective_of_indep`).
- Jet invertibility on `W`:
  `wuestholz_product_theorem_exp_Gm` / `exp_poly_jet_zero`.
  If `α1,α2` are multiplicatively independent, a nonzero integer
  coefficient vector of degree at most `(L,N1,N2)` cannot make
  `Φ(z)=P(z,α1^z,α2^z)` vanish to order `(L+1)(N1+1)(N2+1)` at
  `0`. The `MvPolynomial` wrapper
  `wuestholz_product_theorem_exp_Gm_of_mvPolynomial` (and the
  real-power independence form
  `wuestholz_product_theorem_exp_Gm_of_rpow_indep`) is the same
  criterion for `P ∈ ℤ[y0,y1,y2]` of degree `≤ (L,N1,N2)`:
  vanishing of `Φ(z)=P(z,α1^z,α2^z)` to order
  `T ≥ (L+1)(N1+1)(N2+1)` forces `P = 0`. Gap-3 rules out the
  single relation `A^4=(B+3)^13`; remaining relations are Baker
  (`baker_bound_gap3`). The disjunction
  `wuestholz_product_theorem_exp_of_full_order` packages
  `P = 0 ∨ multiplicativelyDependent` at the jet-dimension
  threshold. `A^4 ≠ C^13` is not independence (`4` and `2`);
  a dependent pair admits nonzero `P` with `Φ ≡ 0`
  (`dependent_pair_allows_identically_zero_Phi`). On `𝐆_a`,
  Siegel still produces nonzero `P` with order `N/2 < N`.
  The intermediate-order statement `T ≥ c L K` uniformly in
  `N1,N2` stays `wuestholz_subgroup_theorem` (`def Prop`).
  This does **not** close Matveev 2000 / `C1_floor`. Track 1
  stays the elementary `1/max` bound.
- Conditional analytic smallness
  `matveev_interpolation_analytic_small_bound`: if the order is `T`
  and `T log 2 ≥ c L K + log M`, then `|f| ≤ exp(−c L K)` on
  `|z| ≤ R/2`. With displayed `T = L K` and `c = log 2`, this
  absorbs once `M ≤ 1` (`analytic_T_absorbs_unit_bound`).
  Determinant form
  `matveev_interpolation_analytic_small_bound_det` for Schwarz-small
  entries. Unconditional `|Δ| ≤ exp(−c L K)` is false
  (`interpolationDeterminant_L0_not_exp_small`).
- Integer-determinant Liouville `|det| ≥ exp(−h(|det|,1))`.
- Interpolation contradiction schema: a *small* upper bound
  `|Δ| ≤ exp(−c1 L K)` plus Liouville
  `|Δ| ≥ exp(−c2 L K − D h(β))` with `c2 L K + D h(β) < c1 L K`
  is impossible.
- Bugeaud κ=1 displayed floor `bugeaud_kappa_one_C0 = C1_floor` by `rfl`.
- Track 1: `matveev_interpolation_track1` is the integer-gap bound
  `matveev_thm14_n2_explicit_of_nat` (integers `A,C > 1`, `A⁴ ≠ C¹³`).
- `matveev_thm14_n2_real_explicit_is_false`: the bare-real ∀-reals
  claim is false (a real `A` can hug `C^{13/4}`).

Axioms: `[propext, Classical.choice, Quot.sound]` only.

## What stays a def Prop

- `matveev_thm14_n2_real_explicit` — bare-real claim; **false**.
- `wuestholz_product_theorem` — inhabited only as the polynomial
  special case (`wuestholz_product_theorem_polynomial`). Mathlib 4.12
  has no Wüstholz theorem for exponential polynomials.
- `wuestholz_product_theorem_exp` — the Wüstholz *subgroup*
  theorem for `P` along `W ⊂ 𝐆_a × 𝐆_m²`. Not in Mathlib 4.12.
  The inhabited theorem is the jet criterion
  `wuestholz_product_theorem_exp_Gm` /
  `wuestholz_product_theorem_exp_Gm_of_mvPolynomial` /
  `wuestholz_product_theorem_exp_of_full_order`, not this
  `def Prop`. `wuestholz_subgroup_theorem` is the
  intermediate-`T` statement and also stays a `def Prop`.
- `size_upper_bound` — unconditional `|Δ| ≤ exp(−c n²)` on a generic
  interpolation matrix. False for `L=0` (`Δ=1`). The *conditional*
  Schwarz bound is a theorem; the G_a jet of `Φ` vanishes after
  Siegel. The inhabited Gm statement is jet invertibility
  (`wuestholz_product_theorem_exp_Gm`). The subgroup theorem
  `wuestholz_product_theorem_exp` stays a `def Prop`.

Unrestricted `matveev_theorem_1_4_gap3_target` and
`baker_bound_gap3` stay `def Prop`. No minted
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional` tag.
