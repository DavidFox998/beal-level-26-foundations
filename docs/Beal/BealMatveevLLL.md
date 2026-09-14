# MatveevLLL — elementary continued-fraction lemmas (not Baker B0)

Lean: [`MatveevLLL.lean`](../../MatveevLLL.lean)
(root module; `Beal/Matveev/MatveevLLL.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.MatveevLLL`.
Concept DOI `10.5281/zenodo.22379293`. C1_floor stays `143186215390`.

## What is proved (0 sorry)

On a gap-3 solution $A^4+B^4=(B+3)^{13}$ with $B>0$:

- `B0_nat = 1000000` (`rfl` to Level 26 `baker_B0`).
- Displayed Bugeaud scaling `LLL_C_nat = 10^30` and basis
  `e1 = (1, 0)`, `e2 = (floor(C log A), floor(C log(B+3)))` as
  definitions only. Mathlib 4.12 has no LLL theorem that turns
  this lattice into `B ≤ 10^6`.
- `|log(B+3)/log A − 4/13| = |Λ|/(13 log A) ≤ (B^4/A^4)/(13 log A)`.
- `B^4/A^4 < 1/((B+3)^9 − 1)`.
- The error is `< 1/(2 · 13^2)`, so Legendre's theorem gives
  `four_thirteenths_is_convergent`: `4/13` is a convergent of the
  log ratio. This is **expected** (`A^4 ≈ (B+3)^{13}`), not a
  contradiction.
- `integer_gap_lt_ratio`: `1/(B+3)^{13} < B^4/A^4`. The integer-gap
  theorem `matveev_thm14_n2_explicit_of_nat` is at most this gap,
  so it never contradicts `|Λ| ≤ B^4/A^4` and never forces `B ≤ 10^6`.
- `abs_Lambda_tight_sandwich`: `B^4/(B+3)^{13} ≤ |Λ| ≤ B^4/A^4`
  via `log(1+u) ≥ u/(1+u)`. Same order (ratio of sides is
  `(B+3)^{13}/A^4 = 1 + B^4/A^4`). Still no cutoff.
- `A_pow_gt_B_pow_five` / `ratio_lt_inv_B` / `abs_Lambda_le_inv_B`:
  `A^4 > B^5` so `|Λ| < 1/B`. The elementary gap
  `1/(B+3)^{13}` is still `< 1/B`
  (`elementary_inv_max_compatible_with_inv_B`), so this is not a
  Baker–Davenport cutoff.
- `abs_Lambda_lt_inv_max_log_coeff`: on every positive-`B`
  solution, `|Λ| < 1/max(4 log A, 13 log(B+3))`. That proposed
  “elementary” lower bound is false and cannot be combined with
  `|Λ| < 1/B` to inhabit `baker_bound_gap3`.
- `track1_exp_lt_ratio`: the packaged Track 1
  `exp(−C1 log A log C B0_term)` is `< B^4/A^4`.
- `LLL_e2_linear_form_approx`: the displayed `C=10^{30}` floor
  form approximates `C Λ` with error `< 17`. Mathlib 4.12 has no
  LLL shortest-vector theorem.
- Rank-3 lattice (columns `b₁ = (1,0,⌊C log A⌋)`,
  `b₂ = (0,1,⌊C log(B+3)⌋)`, `b₃ = (0,0,C)`):
  `LLL_basis_det` (`det = C`), `LLL_v_mem` (`v = 4 b₁ − 13 b₂ ∈ L`),
  `LLL_v_norm_lt_thirty_two` / `LLL_lambda1_lt_thirty_two`
  (`‖v‖ < 32` and `λ₁ < 32` on a solution with `B > 10⁶`,
  using `B⁴/A⁴ < 1/((B+3)⁹−1)` so `C|Λ| < 1`; `|Λ| < 1/B`
  only gives `C|Λ| < 10^{24}`). Minkowski does not raise `|Λ|`.
- Gram–Schmidt coefficients, size-reduction / Lovász predicates,
  and the potential `lllPotential` are defined. The displayed
  basis is **not** claimed LLL-reduced.
- `lll_lovasz_size_half` / `lll_reduced_gs_half`: reduced +
  orthogonal GS ⇒ `‖bᵢ*‖² ≥ (1/2) ‖bᵢ₋₁*‖²`.
- `lllPotential_swap12_factor_lt`: a failed Lovász swap scales
  `D` by a factor `< 3/4`. `LLL_b1_normSq_int`: displayed
  `‖b₁‖²` is an integer. `abs_sub_lllNearestInt`: size-reduction.
- `lll_svt_bound_of_reduced`: an LLL-reduced Z-basis satisfies
  `‖b₁‖ ≤ 2 λ₁`.
- `baker_davenport_gs_lower`: if `r ≤ |v₃|` and `17 < r` then
  `|Λ| ≥ (r − 17)/C`. On `B > 10⁶` one has `|v₃| < 18`, so this
  does not beat `|Λ| < 1/B`.
- `lll_algorithm_terminates`: the displayed lattice has an
  LLL-reduced generating triple. Size-reduction is finite;
  each Lovász-failing swap drops the integer potential
  `D = d₁ d₂ d₃` by a factor `< 3/4`, so only finitely many
  swaps occur. This does **not** give `B ≤ 10⁶`: a reduced
  first vector is short (`‖b₁‖ ≤ 2 λ₁ < 64`).
- `lll_svt_bound`: a reduced *generating* first vector
  satisfies `‖b₁‖ ≤ 2 λ₁`. Not “every lattice vector is
  short”.
- `lll_det_bound`: a reduced generating first vector
  satisfies `‖b₁‖ ≤ √2 · C^{1/3}` (`≈ 2.8e10` for
  `C = 10^{30}`). An *upper* bound, far larger than
  `‖v‖ < 32`. Not a `B ≤ 10⁶` cutoff.

Axioms: `[propext, Classical.choice, Quot.sound]` only.

## What stays a def Prop

- *(removed)* the old universal `lll_svt_bound` /
  `lll_det_bound` “every lattice vector” forms were false
  and are replaced by the displayed theorems above.
- `baker_bound_gap3_from_ratio` — “solution and `|Λ| ≤ B^4/A^4` ⇒ `B ≤ B0_nat`”.
- `bugeaud_LLL_reduction_proof` — same Prop; **not** a theorem.
- `baker_davenport_reduction` — same Prop; Mathlib 4.12 has no
  Baker–Davenport / Bugeaud LLL theorem.
- Level 26 `baker_bound_gap3` — `∀ B > 10^6, ¬∃ A`.

`baker_bound_gap3_of_from_ratio` shows that inhabiting the
implication form inhabits Level 26 `baker_bound_gap3` (the proved
`|Λ| ≤ B^4/A^4` is already available). That is the v25 close, and
it is still open.

Unrestricted `matveev_theorem_1_4_gap3_target` stays a `def Prop`.
No `matveev_gap3_lower_unrestricted` theorem. No minted
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional` tag.
