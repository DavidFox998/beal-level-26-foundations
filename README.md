# foundations-level-26 — Beal Level 26 Matveev-Baker Foundations

[![Matveev-Beal CI](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml/badge.svg)](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml)

This repo is foundations-level-26, the Matveev proof for beal-conjecture f7bbdc5. Current HEAD: 0 sorry. `matveev_gap3_lower` is the **B≤10^6 integer-gap** close (`|Λ| > exp(-height_B0 log height_B0)` on gap-3 solutions with `B ≤ 10^6`) via `matveev_thm14_n2_explicit_of_nat` and `matveev_product_bound_of_B_le_B0`. `MatveevLLL.lean` proves the elementary CF lemmas (`4/13` is a convergent of the log ratio; integer gap `<` `B⁴/A⁴`) and keeps `bugeaud_LLL_reduction_proof` / `baker_bound_gap3` as uninhabited `def Prop` — being a convergent does not force `B ≤ 10⁶`. C1_floor=143186215390. Not Matveev interpolation, not unrestricted `matveev_inequality_real_target` (product false for huge B), not `hLLL`. Not v25. lake build BealMatveevBeal green. NOT waiting on Mathlib.

Monorepo beal-conjecture stays beal-conjecture, this repo is foundations-level-26 Matveev-Beal complement.

GitHub slug remains `beal-level-26-foundations` (not renamed: concept DOI
[10.5281/zenodo.22379293](https://doi.org/10.5281/zenodo.22379293) stays
attached). Display title:
**Beal Level 26 Foundations — Matveev 2000 Thm1.4 n=2 + Bugeaud LLL → Baker B0=10^6**.

This URL formerly hosted the Level 26 kernel through
`v24.4.0-Beal-44-13-Level-26-v24x-Final-Summary` (`db7a556`,
DOI [10.5281/zenodo.22732209](https://doi.org/10.5281/zenodo.22732209)).
That closing tree lives at
[`DavidFox998/beal-conjecture`](https://github.com/DavidFox998/beal-conjecture)
`Level26/BealLevel26Foundations` (`f7bbdc5` / `e823a52` wiring, 0 sorry).
See `README_MOVED.md`.

This repository owns the **Matveev–Beal** formalization: inhabit
`matveev_inequality_real_target` / `|Λ| > exp(C_exp_bound)` toward
unconditional `B ≤ B0 = 10^6`. That is v25 only when `baker_bound_gap3`
greens via `baker_conditional_gap3_full` with no `hBaker`. Mathlib 4.12
has no Matveev 2000 Thm 1.4.

```
Beal/Matveev/MatveevThm14General.lean
MatveevThm14Proof.lean
MatveevLLL.lean
```

**0 `sorry`.** `matveev_gap3_lower` is the B≤10^6 integer-gap theorem
(`matveev_gap3_lower_B_le_B0_target`), not the unrestricted Level26
`matveev_inequality_real_target`. The integer gap lives in
`MatveevThm14Proof.lean` (`matveev_thm14_n2_explicit_of_nat`).

On a gap-3 solution, `B < A` and `A ≈ (B+3)^{13/4}`. The old
`A < B+3` bound is false. Usable: `log A < (13/4) log(B+3)`.

- `gap3_A_bounds` — `0 < A`, `1 < A`, `1 < B+3`, `A^4 < (B+3)^13`,
  `log A < (13/4) log(B+3)` (proved)
- `matveev_theorem_1_4_general` — Matveev 2000 Thm 1.4 n=2 on
  `α1 = A`, `α2 = B+3`, `b1=4`, `b2=-13`, `D=1`, `B=13`
  (uninhabited `def Prop`; not in Mathlib 4.12; we own Matveev)
- `matveev_product_bound_gap3` — unrestricted product on every
  solution (uninhabited `def Prop`: LHS is `O((log(B+3))³)`, RHS constant)
- `matveev_product_bound_of_B_le_B0` / `matveev_product_bound_of_B3_le_height`
  — the product that *is* a theorem, when `B ≤ 10^6` via `log 13 < 3`
- `matveev_thm14_n2_explicit_of_nat` — integer gap
  `|4 log A − 13 log C| > exp(−C1·log A·log C·B0)` for integers
  `A,C > 1` with `A⁴ ≠ C¹³` (proved; not interpolation)
- `matveev_gap3_lower_of_integer_gap_of_B_le_B0` — integer gap +
  `B ≤ 10^6` product ⇒ `|Λ| > exp(C_exp_bound)` (proved; no `hGen`)
- `matveev_gap3_lower_of_general_of_B_le_B0` — `hGen` + `B ≤ 10^6`
  ⇒ `|Λ| > exp(C_exp_bound)` (proved; does not inhabit `hGen`)
- `matveev_gap3_conditional_B_of_general` — `hGen` ⇒
  `B^4(1+δ) > δ(B+3)^13` with Matveev `δ`. Does **not** give
  `B ≤ 10^6` (that is LLL / `baker_bound_gap3`)
- `matveev_gap3_lower_of` — general + unrestricted product ⇒
  unrestricted target (proved; does not inhabit the hypotheses)
- `matveev_gap3_lower` — B≤10^6 integer-gap close (proved).
  Unrestricted `matveev_theorem_1_4_gap3_target` stays a `def Prop`
- `four_thirteenths_is_convergent` — on a solution,
  `|log(B+3)/log A − 4/13| < 1/(2·13²)`, so `4/13` is a
  convergent (proved; expected, not a Baker cutoff)
- `integer_gap_lt_ratio` — `1/(B+3)¹³ < B⁴/A⁴` on a solution
  (proved; integer-gap Matveev never contradicts the upper bound)
- `abs_Lambda_tight_sandwich` — `B⁴/(B+3)¹³ ≤ |Λ| ≤ B⁴/A⁴`
  (proved; same order, no Baker cutoff)
- `bugeaud_LLL_reduction_proof` / `baker_bound_gap3_from_ratio`
  — implication “ratio upper bound ⇒ `B ≤ 10⁶`” (uninhabited
  `def Prop`; inhabiting it would inhabit Level 26
  `baker_bound_gap3`)

`baker_conditional_gap3_full` takes `baker_bound_gap3`, not the
Matveev target. After the lower bound, the remaining implication
`matveev_inequality_real_target → baker_bound_gap3` is still an
uninhabited `def Prop` (LLL / Bugeaud `hLLL`). Mathlib 4.12 has
no LLL reduction theorem. The CF lemmas do not close v25.

```bash
lake update
lake exe cache get   # optional, uses the mathlib oleans cache
lake build
```

Lake requires the monorepo subdirectory
`Level26/BealLevel26Foundations` (not the whole `beal_conjecture`
default `Beal` lib). Import wrappers live under
`BealConjecture.Level26.BealLevel26Foundations.*`.
Axioms on the real pack: `[propext, Classical.choice, Quot.sound]`.

## Citation for the relocated v24.4.0 closing

```bibtex
@software{beal_level26_v24_4_0,
  title = {Beal Level 26 Foundations v24.4.0: v24.x Final Summary},
  author = {Fox, David},
  year = {2026},
  doi = {10.5281/zenodo.22732209},
  url = {https://doi.org/10.5281/zenodo.22732209},
  note = {Concept DOI 10.5281/zenodo.22379293, GitHub tag
    v24.4.0-Beal-44-13-Level-26-v24x-Final-Summary on db7a556,
    now at beal-conjecture/Level26/BealLevel26Foundations}
}
```
