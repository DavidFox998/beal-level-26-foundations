# BealMatveevThm14 — v24.0.0 Matveev 2000 Thm 1.4 formalization start

**Tag.** `v24.2.0-Beal-44-13-Level-26-Matveev-Log-Form-Bound`.
**Source.** `lean/BealLevel26Foundations/Beal/FullProof/BealMatveevThm14.lean`.
**Namespace.** `BealLevel26Foundations.BealMatveevThm14`.
**Parent.** v24.1.1 `21df092` / `v24.1.1-Beal-44-13-Level-26-Matveev-C-Exp-Rewrite` / DOI `10.5281/zenodo.22730846`.
**Concept.** `10.5281/zenodo.22379293`.

## v24.2.0 — logarithmic form upper bound on gap-3 solutions

```lean
theorem matveev_gap3_B_pos_of_solution :
    A^4 + B^4 = (B+3)^13 → 0 < B
theorem matveev_gap3_A_pos :
    A^4 + B^4 = (B+3)^13 → 0 < A
theorem matveev_gap3_log_form_upper_bound :
    A^4 + B^4 = (B+3)^13 → 0 < B →
      matveev_log_form A B < 0 ∧
        |matveev_log_form A B| = -matveev_log_form A B
theorem matveev_exp_lower_lt_one_and_pos :
    0 < matveev_target_exp_lower ∧ matveev_target_exp_lower < 1
```

On a gap-3 solution $A^4 + B^4 = (B+3)^{13}$:
- $B > 0$ is proven by eliminating $B = 0$ via `baker_le_B0_gap3` ($0 \le 10^6$).
- $A > 0$ follows from $0 < B$ and $B < A$ via `eq_implies_A_gt_B`.
- The logarithmic linear form $\Lambda = 4 \log A - 13 \log (B+3)$ is strictly negative, so $|\Lambda| = -\Lambda = -(4 \log A - 13 \log (B+3))$.
- The target lower bound $\exp(C_{\mathrm{exp\_bound}})$ is strictly in $(0, 1)$.
- Links the upper bound side to the lower bound target. `matveev_inequality_real_target` and `baker_bound_gap3` stay uninhabited def Props.

## v24.1.1 — rewriting C_exp_bound via height_B0

```lean
theorem matveev_C_exp_bound_eq_neg_height_mul_log :
    matveev_C_exp_bound = -(((height_B0 : Real) * Real.log (height_B0 : Real)))
theorem matveev_C_exp_bound_eq_neg_height_log :
    matveev_C_exp_bound = -(height_B0 : Real) * Real.log (height_B0 : Real)
theorem matveev_target_exp_lower_eq :
    matveev_target_exp_lower = Real.exp (-((height_B0 : Real) * Real.log (height_B0 : Real)))
theorem matveev_height_B0_mul_log_pos :
    0 < (height_B0 : Real) * Real.log (height_B0 : Real)
theorem matveev_C_exp_bound_neg_of_mul_log_pos :
    matveev_C_exp_bound < 0 ↔ 0 < (height_B0 : Real) * Real.log (height_B0 : Real)
```

Rewrites the displayed exponent `matveev_C_exp_bound` using the product identity `matveev_height_product_link` (`height_B0 = C1_floor * thirty_pow`).
`matveev_inequality_real_target` and `baker_bound_gap3` stay uninhabited def Props.

## v24.1.0 — height product identity

```lean
theorem matveev_C1_floor_mul_thirty_pow_div10 :
    C1_floor * 72900000 = 10438275101931000000
theorem matveev_C1_floor_mul_thirty_pow :
    C1_floor * 729000000 = 104382751019310000000
theorem matveev_C1_floor_mul_thirty_pow_div10_times_ten :
    C1_floor * 72900000 * 10 = height_B0
theorem matveev_C1_floor_mul_thirty_pow_div10_ne_height :
    C1_floor * 72900000 ≠ height_B0
theorem matveev_height_product_link :
    height_B0 = C1_floor * thirty_pow
```

`thirty_pow = 729000000 = 30^6`. The 7-digit typo `72900000` is `30^6 / 10`. The correct product **is** `height_B0`. The typo product is `height_B0 / 10`. This is **not** `|Λ| > exp(-C)`.

`matveev_inequality_real_target` and `baker_bound_gap3` stay uninhabited.

## v24.0.2 — exp of the displayed bound

```lean
theorem matveev_exp_bound_lt_zero : matveev_C_exp_bound < 0
theorem matveev_exp_of_bound_pos_lt_one :
    Real.exp matveev_C_exp_bound < 1
theorem matveev_exp_of_bound_pos :
    0 < Real.exp matveev_C_exp_bound
theorem matveev_C_exp_bound_le_neg_onee12 :
    matveev_C_exp_bound ≤ -((ten_pow_12 : Nat) : Real)
noncomputable def matveev_target_exp_lower : Real :=
  Real.exp matveev_C_exp_bound
```

`0 < matveev_target_exp_lower < 1`. This names the Matveev lower-bound shape. It does **not** prove `|Λ| > matveev_target_exp_lower`. Mathlib 4.12 has no Matveev 2000 Thm 1.4.

`matveev_inequality_real_target` and `baker_bound_gap3` stay uninhabited.

## v24.0.1 — height and log monotone

Keeps the v24.0.0 lemmas and adds:

```lean
theorem matveev_C1_floor_pos : matveev_C1_floor > 0
theorem matveev_thirty_pow_pos : matveev_thirty_pow > 0
theorem matveev_thirty_pow_eq_typo_times_ten :
    matveev_thirty_pow = 72900000 * 10
```

`decide`, no axioms. `thirty_pow = 729000000 = 30^6`. The 7-digit numeral `72900000` is `30^6 / 10`, not `30^6`.

```lean
theorem matveev_height_B0_gt_two :
    (2 : Real) < (matveev_height_B0 : Real)
```

From `height_B0 > 10^12`. Pack axioms from Real coercion.

```lean
theorem matveev_log_height_monotone :
    ∀ h1 h2 : Real, 0 < h1 → h1 < h2 → Real.log h1 < Real.log h2
```

`Real.log_lt_log`. Pack axioms.

```lean
theorem matveev_C_exp_bound_lt_zero_of_pos_log :
    matveev_C_exp_bound < 0 ↔
      0 < Real.log (matveev_height_B0 : Real)
```

Because `C1_floor > 0` and `thirty_pow > 0`, the product in `-C1_floor * thirty_pow * log height_B0` is negative iff the log is positive. Pack axioms.

`matveev_inequality_real_target` and `baker_bound_gap3` stay uninhabited.

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

`git diff v24.1.1-Beal-44-13-Level-26-Matveev-C-Exp-Rewrite` is empty on:

- Tate (`BealFreyTateConductor.lean`)
- Baker (`BealGap3BakerUpperBound.lean`)
- modular-elim (`BealLevel26ModularElimination.lean`)
- v15 B0 (`BealBakerB0Certificate.lean`)
- v17 LLL (`BealBakerB0ReductionCertificate.lean`)
- v19 constants (`BealMatveevConstants.lean`)
- v20 Bugeaud (`BealBugeaudLLLFormal.lean`)
- v21 inequality (`BealMatveevInequality.lean`)
- v22 Real skeleton (`BealMatveevInequalityReal.lean`)
- v23 compare (`BealBakerBoundGap3.lean`)

v14 J0 `[[1,0,1,-5,-8],[1,-1,1,-3,3]]` mwrank `{0,12}` M3 `[[1,1],[0,2]]` unchanged, holds, no axioms. J0 formal unchanged since v11 `3089bec`.
