# BealBakerBoundGap3 — v23 exponent compare + Real nonzero on a solution

Lean: [`lean/BealLevel26Foundations/Beal/FullProof/BealBakerBoundGap3.lean`](../../lean/BealLevel26Foundations/Beal/FullProof/BealBakerBoundGap3.lean)

## What is kernel-real here

- `matveev_height_B0_gt_onee12` : `10^12 < height_B0` by `decide`, no axioms.
- `matveev_C_exp_bound_decide_reuse` : `C1_floor = 143186215390 ∧ thirty_pow = 729000000` by `decide`, no axioms.
- `matveev_C_exp_bound_eq_neg_mul` : displayed exponent equals `-height_B0 * log(height_B0)`.
- `matveev_log_height_B0_gt_one` : `1 < log(height_B0)` via `Real.exp_one_lt_d9` and `height_B0 > 3`.
- `matveev_C_exp_bound_lt_neg_onee12` : `C_exp_bound < -10^12`.
- `matveev_log_form_ne_zero_of_gap3` : on a solution `A^4 + B^4 = (B+3)^13` with `B > 0`, the Real form `4 log A - 13 log(B+3)` is strictly negative, hence nonzero.

Real theorems print `[propext, Classical.choice, Quot.sound]` only.

## What is still not kernel-real

- `|Λ| > exp(matveev_C_exp_bound)` stays an uninhabited unrestricted `def Prop` (`matveev_inequality_real_lower_remaining`). The foundations complement proves the B≤10^6 integer-gap form as `BealMatveevBeal.matveev_gap3_lower`.
- `baker_bound_gap3` stays an uninhabited `def Prop` (`baker_bound_gap3_remaining`). The foundations `MatveevLLL.lean` CF lemmas (`4/13` convergent; integer gap `<` ratio) do not inhabit it. `MatveevBugeaud.lean` proves the displayed lattice cannot inhabit it. `MatveevThreeLogs.lean` proves `baker_bound_gap3_nogo_logs`: any `C1 ≥ 1` has `exp(−C1 log A log(B+3)) < B⁴/A⁴` on a solution with `B ≥ B0`, so the log method cannot inhabit it either. `BealKraus.lean` proves `baker_bound_gap3_kraus_nogo`: the displayed Frey curve does not Fermat-lower primes in `A` at `p=13` (`13 ∤ 8`). `BealKrausZsig.lean` proves `baker_bound_gap3_gaussian_nogo`: even after `N(A²+iB²)=(B+3)¹³`, a Matveev-style bound on the Gaussian argument form needs `C1 < 2` and `C1_floor` / `242` / `2` all lose to `B⁴/C¹³` on `B ≥ B0`. `BealCatalanZsig.lean` proves `baker_bound_gap3_mihailescu_zsigmondy_nogo`: gap-3 is not Catalan shape, `3 ∤ B` gives `gcd(A,B)=1` so Zsigmondy primes in `B` do not force `13 ∣ v_p(A)`, and the same `C1 < 2` cutoff still fails.
- `baker_conditional_gap3_full` still takes `hBaker : baker_bound_gap3`.
- Mathlib 4.12 has no Matveev 2000 Theorem 1.4 and no Bugeaud/LLL reduction.
- `C_exp_bound < -10^12` is a fact about the displayed exponent, not a uniform lower bound on `|Λ|`.
- `Λ ≠ 0` on a solution does not imply `|Λ| > exp(-C)` for all large `B`.

Does not use sorry. No `axiom`. No `native_decide`.
Does not import `RibetMazur`, `FreyModularity_13`, or `BealFreyB14`.
Does not inhabit `ExistsNewformLevel2` or `¬ PositiveBealTriple`.

## Honesty lock

`git diff v22.0.0-Beal-44-13-Level-26-Matveev-Inequality-Real` is 0 on
Tate / Baker / modular-elim / v15 B0 / v17 LLL / v19 constants / v20 Bugeaud LLL / v21 inequality / v22 Real skeleton.

v14 `J0 = [[1,0,1,-5,-8],[1,-1,1,-3,3]]`, mwrank `{0,12}`, formal `M3 = [[1,1],[0,2]]` unchanged.

## Remaining for v24

Inhabit `baker_bound_gap3` only after a real in-kernel Matveev 2000 Thm 1.4
lower bound `|Λ| > exp(-C1_floor · 30^{n+3} · log height_B0)` plus a real
Bugeaud/LLL reduction from `B0_raw` to `10^6`. Until then
`baker_conditional_gap3_full` stays conditional on that Prop.
