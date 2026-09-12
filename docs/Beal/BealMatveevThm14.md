# BealMatveevThm14 — v24.0.0 Matveev 2000 Thm 1.4 formalization start

**Tag.** `v24.0.0-Beal-44-13-Level-26-Matveev-Thm-1-4-Formalization-Start`.
**Source.** `lean/BealLevel26Foundations/Beal/FullProof/BealMatveevThm14.lean`.
**Namespace.** `BealLevel26Foundations.BealMatveevThm14`.
**Parent.** v23 `c44f161` / `v23.0.0-Beal-44-13-Level-26-Matveev-C-Exp-Bound-Compare` / DOI `10.5281/zenodo.22730338`.
**Concept.** `10.5281/zenodo.22379293`.

This is the first v24 file. It starts a real in-kernel formalization of the Matveev 2000 Theorem 1.4 lower bound

\[
|\Lambda| \;>\; \exp\bigl(-C_{1,\mathrm{floor}}\cdot 30^{n+3}\cdot\log\mathrm{height}_{B_0}\bigr)
\]

on a gap-3 Beal solution. It does **not** inhabit that inequality, and it does **not** inhabit `baker_bound_gap3`. We stay in the v24 series (`v24.0.1`, `v24.1.0`, …) until the Real inequality is a theorem. v25 is reserved for the first version where `baker_bound_gap3` is inhabited and `baker_conditional_gap3_full` drops `hBaker`.

## Imports (no Ribet / Frey modularity)

```
import BealLevel26Foundations.BealMatveevConstants
import BealLevel26Foundations.BealMatveevInequality
import BealLevel26Foundations.BealBugeaudLLLFormal
import BealLevel26Foundations.BealMatveevInequalityReal
import BealLevel26Foundations.BealBakerBoundGap3
```

Does **not** import `BealRibetMazur`, `Modularity.FreyModularity_13`, or `BealFreyB14`. The 24-module none-chain stays intact.

## Reused constants (v19–v23)

| Source | Object | Kernel status |
|---|---|---|
| v19 `8fe96fd` | `matveev_C1_floor = 143186215390` | `decide`, no axioms |
| v19 | `matveev_thirty_pow = 729000000` (`30^6`) | `decide`, no axioms |
| v19 | `matveev_thirty_pow ≠ 72900000` (typo) | `decide`, no axioms |
| v19 | `matveev_height_B0 = 104382751019310000000` | `decide`, no axioms |
| v19 | `matveev_c4_scale = 16` | `decide`, no axioms |
| v20 `768ed7f` | `bugeaud_K = 10^{20}` | `decide`, no axioms |
| v20 | `bugeaud_LLL_basis_holds` | `decide`, no axioms |
| v21 `3079d82` | `matveev_log_form_int 0 / 14 ≠ 0` | `decide`, no axioms |
| v21 | Tate witness `63982 = 2 * 31991` | `decide`, no axioms |
| v22 `1db061a` | `matveev_C_exp_bound : Real` | reused as-is |
| v23 `c44f161` | `matveev_height_B0_gt_onee12` | `decide`, no axioms |
| v23 | `matveev_C_exp_bound < -10^{12}` | pack axioms |

v23 compare used `729000000`. The user prompt also mentioned `72900000`. Both numerals are recorded as `decide` theorems so the typo cannot silently replace `30^6`.

## New lemmas

```lean
theorem matveev_height_log_pos :
    0 < Real.log (matveev_height_B0 : Real)
```

From `1 < height_B0` (via `height_B0_gt_onee12` and `1 < 10^{12}`) plus `Real.log_pos`. Pack `[propext, Classical.choice, Quot.sound]`.

```lean
theorem matveev_exp_bound_neg : matveev_C_exp_bound < 0
```

Restates v23 `matveev_C_exp_bound_neg`. Same pack.

## Named target (uninhabited)

```lean
def matveev_inequality_real_target : Prop :=
  ∀ (A B : Nat),
    0 < B →
      Nat.pow A 4 + Nat.pow B 4 = Nat.pow (B + 3) 13 →
        |matveev_log_form A B| > Real.exp matveev_C_exp_bound
```

This is the Matveev 2000 Theorem 1.4 statement we are formalizing, specialized to a gap-3 Beal solution. Mathlib 4.12 has no Matveev theorem, so the name is a `def Prop` with no inhabitant and no `sorry`.

The target is **not** `∀ A B, |Λ| > exp(-C)`. That universal statement is false for arbitrary positive integers: the logs can be arbitrarily close. The bound is only claimed on an actual gap-3 solution, which is where Matveev applies.

## What this does **not** prove

- It does **not** prove `|Λ| > Real.exp matveev_C_exp_bound`.
- It does **not** inhabit `baker_bound_gap3`.
- It does **not** drop `hBaker` from `baker_conditional_gap3_full`.
- It does **not** claim a Beal theorem.

v23 already showed `Λ ≠ 0` on a solution and `C_exp_bound < -10^{12}`. Those facts are necessary but not sufficient: on a solution `|Λ| = log(1+(B/A)^4)` can be arbitrarily small for huge `B`. The missing piece is Matveev's uniform lower bound.

## Honesty lock

`git diff v23.0.0-Beal-44-13-Level-26-Matveev-C-Exp-Bound-Compare` is empty on:

- Tate (`BealFreyTateConductor.lean`)
- Baker (`BealGap3BakerUpperBound.lean`)
- modular-elim (`BealModularElimination.lean`)
- v15 B0 (`BealBakerB0Certificate.lean`)
- v17 LLL (`BealBakerB0ReductionCertificate.lean`)
- v19 constants (`BealMatveevConstants.lean`)
- v20 Bugeaud (`BealBugeaudLLLFormal.lean`)
- v21 inequality (`BealMatveevInequality.lean`)
- v22 Real skeleton (`BealMatveevInequalityReal.lean`)
- v23 compare (`BealBakerBoundGap3.lean`)

v14 J0 `[[1,0,1,-5,-8],[1,-1,1,-3,3]]` mwrank `{0,12}` M3 `[[1,1],[0,2]]` unchanged, holds, no axioms. J0 formal unchanged since v11 `3089bec`.

## Versioning

We stay in v24 until `matveev_inequality_real_target` is a theorem and `baker_bound_gap3` is inhabited:

- `v24.0.1`, `v24.1.0`, `v24.2.0`, … — iterative Real / Matveev work
- `v25` — only when `baker_bound_gap3` greens via `baker_conditional_gap3_full` with no `hBaker`
