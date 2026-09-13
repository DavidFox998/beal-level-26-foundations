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
- Conditional analytic smallness
  `matveev_interpolation_analytic_small_bound`: if the order is `T`
  and `T log 2 ≥ c L K + log M`, then `|f| ≤ exp(−c L K)` on
  `|z| ≤ R/2`. Determinant form
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
- `size_upper_bound` — unconditional `|Δ| ≤ exp(−c n²)` on a generic
  interpolation matrix. False for `L=0` (`Δ=1`). The *conditional*
  Schwarz bound is a theorem; vanishing of Matveev's exponential
  `Φ` still needs Wüstholz (not in Mathlib 4.12).

Unrestricted `matveev_theorem_1_4_gap3_target` and
`baker_bound_gap3` stay `def Prop`. No minted
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional` tag.
