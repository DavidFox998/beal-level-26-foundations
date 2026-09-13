# Matveev–Beal lower bound

This GitHub URL formerly hosted **Beal Level 26 Foundations** through
`v24.4.0-Beal-44-13-Level-26-v24x-Final-Summary` (`db7a556`,
DOI [10.5281/zenodo.22732209](https://doi.org/10.5281/zenodo.22732209),
concept [10.5281/zenodo.22379293](https://doi.org/10.5281/zenodo.22379293)).

That closing tree is relocated to
[`DavidFox998/beal-conjecture`](https://github.com/DavidFox998/beal-conjecture)
at `Level26/BealLevel26Foundations`. See `README_MOVED.md`.

This repository is the **Matveev–Beal** formalization: inhabit
`matveev_inequality_real_target` / `|Λ| > exp(C_exp_bound)` toward
unconditional `B ≤ B0 = 10^6`. That is v25 only when `baker_bound_gap3`
greens via `baker_conditional_gap3_full` with no `hBaker`.

```
Beal/Matveev/MatveevThm14General.lean
```

Honest skeleton, **one `sorry`**: `matveev_gap3_lower`, which is
definitionally `matveev_inequality_real_target` from the relocated
Level26 kernel.

- `matveev_theorem_1_4_general` — Matveev 2000 Thm 1.4 shape with
  `height_B0 = C1_floor * 30^6` (uninhabited `def Prop`)
- `matveev_theorem_1_4_gap3_target` — gap-3 instance
- `matveev_gap3_lower` — the v25 goal (`sorry`)

`baker_conditional_gap3_full` takes `baker_bound_gap3`, not the
Matveev target. After the lower bound, the remaining implication
`matveev_inequality_real_target → baker_bound_gap3` is still an
uninhabited `def Prop` (LLL / Bugeaud).

```bash
lake update
lake exe cache get   # optional, uses the mathlib oleans cache
lake build
```

Lake requires the monorepo subdirectory
`Level26/BealLevel26Foundations` (not the whole `beal_conjecture`
default `Beal` lib). Import wrappers live under
`BealConjecture.Level26.BealLevel26Foundations.*`.

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
