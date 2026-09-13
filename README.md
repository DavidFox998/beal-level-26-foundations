# foundations-level-26 — Beal Level 26 Matveev-Baker Foundations

This repo is foundations-level-26, the Matveev proof for beal-conjecture f7bbdc5. Current 4bd15bd one sorry matveev_gap3_lower at 716 representing hGen Matveev 2000 Thm1.4 n=2 explicit C1_floor=143186215390 + hLLL Bugeaud LLL reduction to B0=10^6, gap3_A_bounds B<A logA<13/4 log(B+3) proved, matveev_product_bound_of_B_le_B0 proved via log13<3, matveev_gap3_lower_of_general_of_B_le_B0 v25-sufficient, lake build green with warning, NOT waiting on Mathlib, we own Matveev.

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
```

Honest skeleton, **one `sorry`**: `matveev_gap3_lower` at line 716, which is
definitionally `matveev_inequality_real_target` from the relocated
Level26 kernel (represents `hGen`).

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
- `matveev_gap3_lower_of_general_of_B_le_B0` — `hGen` + `B ≤ 10^6`
  ⇒ `|Λ| > exp(C_exp_bound)` (proved; v25-sufficient; does not inhabit `hGen`)
- `matveev_gap3_conditional_B_of_general` — `hGen` ⇒
  `B^4(1+δ) > δ(B+3)^13` with Matveev `δ`. Does **not** give
  `B ≤ 10^6` (that is LLL / `baker_bound_gap3`)
- `matveev_gap3_lower_of` — general + unrestricted product ⇒ target
  (proved; does not inhabit the hypotheses)
- `matveev_gap3_lower` — the v25 goal (`sorry` at 716)

`baker_conditional_gap3_full` takes `baker_bound_gap3`, not the
Matveev target. After the lower bound, the remaining implication
`matveev_inequality_real_target → baker_bound_gap3` is still an
uninhabited `def Prop` (LLL / Bugeaud `hLLL`).

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
