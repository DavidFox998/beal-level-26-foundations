# WuestholzSubgroup — intermediate-`T` no-go (not a uniform `c`)

Lean: [`WuestholzSubgroup.lean`](../../WuestholzSubgroup.lean)
(root module; `Beal/Matveev/WuestholzSubgroup.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.WuestholzSubgroup`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `cfd4794` (`v24-v24x-final-LLL-nogo`). Mathlib 4.12
has no Philippon zero estimate. The uniform Wüstholz statement

  `∃ c > 0, ∀ N1,N2,  T ≥ c L K  →  P = 0 ∨ dependence`

is **not** a theorem of jet invertibility.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `AlgebraicSubgroup` / `degSubgroup` / `candidateSubgroups`:
  integer model of `y1=1`, `y2=1`, `z=0` (graphs remain the
  extra constructor of `ProperSubgroupCandidate`).
- `W_tangent`: Lie direction `(1, log A, log(B+3))`.
- `vanishesToOrder`: jet of `Φ(z)=P(z,α1^z,α2^z)` at `0`.
- `coeffCount_one_ten_ten`: `(1+1)(10+1)(10+1) = 242`.
- `no_uniform_c_easy_half`: `(1/2)·1·1 < 242` (`46bdeea`).
- `no_uniform_c_one_div_two_forty_two` / `_thousand`:
  `c = 1/242` and `c = 1/1000` still lose to that jet.
- `no_uniform_c_linear_in_N`: even `K ∼ N1+N2` has no uniform
  `c` (the jet is quadratic in the `G_m` degrees).
- `easy_half_W_not_in_candidate`: independence keeps `W` out of
  every proper candidate.
- `wuestholz_subgroup_theorem_of_jet_dim`: if the jet dimension
  is already `≤ c L K ≤ T`, full-order invertibility gives
  `P = 0 ∨ dependence`. Not uniform in `N1,N2`.
- `siegel_T_lt_jet_dim`: Siegel on `𝐆_a` vanishes only to
  order `N/2`.

## What stays a def Prop

- `wuestholz_subgroup_theorem` — uniform `T ≥ c L K`.
- `wuestholz_product_theorem_exp` — exponential product along
  `W` below full jet order.
- Level 26 `baker_bound_gap3` / `bugeaud_LLL_reduction_proof`.

Not a minted v25 tag. Successor packaging of the inhabited
full-order product theorem lives in
[`BealWuestholzProduct.md`](BealWuestholzProduct.md).
