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
- `baker_bound_gap3` stays an uninhabited **named theorem** (`baker_bound_gap3_remaining`). The kernel Prop is inhabited axiom-relatively as `BealTrueV25.baker_bound_gap3_true` via `axiom darmon_merel_4413_axiom`; that extra axiom is not Mathlib 4.12 and does not mint `v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`. The foundations `MatveevLLL.lean` CF lemmas (`4/13` convergent; integer gap `<` ratio) do not inhabit it. `MatveevBugeaud.lean` proves the displayed lattice cannot inhabit it. `MatveevThreeLogs.lean` proves `baker_bound_gap3_nogo_logs`: any `C1 ≥ 1` has `exp(−C1 log A log(B+3)) < B⁴/A⁴` on a solution with `B ≥ B0`, so the log method cannot inhabit it either. `BealKraus.lean` proves `baker_bound_gap3_kraus_nogo`: the displayed Frey curve does not Fermat-lower primes in `A` at `p=13` (`13 ∤ 8`). `BealKrausZsig.lean` proves `baker_bound_gap3_gaussian_nogo`: even after `N(A²+iB²)=(B+3)¹³`, a Matveev-style bound on the Gaussian argument form needs `C1 < 2` and `C1_floor` / `242` / `2` all lose to `B⁴/C¹³` on `B ≥ B0`. `BealCatalanZsig.lean` proves `baker_bound_gap3_mihailescu_zsigmondy_nogo`: gap-3 is not Catalan shape, `3 ∤ B` gives `gcd(A,B)=1` so Zsigmondy primes in `B` do not force `13 ∣ v_p(A)`, and the same `C1 < 2` cutoff still fails. `BealDarmonMerel.lean` proves `baker_bound_gap3_darmon_merel_nogo`: `3 ∣ B` forces `3 ∣ A` so Darmon–Merel coprime hypothesis fails; `13 ∣ 26` / `13 ∤ 8` so an unlowered prime in `A` makes the residual estimate not divide 32. `BealDarmonMerel44p.lean` proves `baker_bound_gap3_darmon_merel_44p_nogo`: displayed residual ≠ 32 on `B > 0`; `A = a¹³` and `B = b¹³` is Fermat exponent 13. `BealFLT13.lean` proves `baker_bound_gap3_flt13_darmon_merel_nogo`: no solutions when `3 ∣ B` (3-adic descent); every solution is coprime, which is Darmon–Merel's remaining case. `BealGenuineV25.lean` proves `baker_bound_gap3_darmon_merel_4413_3adic_nogo`: Darmon–Merel `(4,4,13)` would close `baker_bound_gap3` vacuously, but that statement is not in Mathlib 4.12, and a `B ≥ B0` solution would refute it. Tagged `v24-v24x-final-genuine-v25-nogo` at `2b4ee3b`. See [`BealTrueV25.md`](BealTrueV25.md) and [`BealUnconditionalV25.md`](BealUnconditionalV25.md). `BealUnconditionalV25.lean` proves `baker_bound_gap3_unconditional_nogo`: `hGen` and `hLLL` cannot cut `B ≤ 10⁶` (every `C1 ≥ 1` loses to `B⁴/A⁴`; no Baker–Davenport witness above `17+C/B0`). Darmon–Merel, Ribet-to-32, and FLT stay `def Prop` as theorems.
- `baker_conditional_gap3_full` still takes `hBaker : baker_bound_gap3`.
- Mathlib 4.12 has no Matveev 2000 Theorem 1.4 and no Bugeaud/LLL reduction.
- `C_exp_bound < -10^12` is a fact about the displayed exponent, not a uniform lower bound on `|Λ|`.
- `Λ ≠ 0` on a solution does not imply `|Λ| > exp(-C)` for all large `B`.

Does not use sorry. No `native_decide`.
The only extra axiom in this repository is
`BealTrueV25.darmon_merel_4413_axiom`, used solely by
`baker_bound_gap3_true` / `no_gap3_of_axiom` /
`baker_bound_gap3_le_B0`. Kernel-real theorems in this file
print `[propext, Classical.choice, Quot.sound]` only.
Does not import `RibetMazur`, `FreyModularity_13`, or `BealFreyB14`.
Does not inhabit `ExistsNewformLevel2` or `¬ PositiveBealTriple`.

## Honesty lock

`git diff v22.0.0-Beal-44-13-Level-26-Matveev-Inequality-Real` is 0 on
Tate / Baker / modular-elim / v15 B0 / v17 LLL / v19 constants / v20 Bugeaud LLL / v21 inequality / v22 Real skeleton.

v14 `J0 = [[1,0,1,-5,-8],[1,-1,1,-3,3]]`, mwrank `{0,12}`, formal `M3 = [[1,1],[0,2]]` unchanged.

## Remaining for an unconditional v25 mint

Inhabit `hGen` and `hLLL` 0-sorry in Mathlib 4.12 (a real
in-kernel Matveev 2000 Thm 1.4 lower bound plus a real
Bugeaud/LLL reduction from `B0_raw` to `10^6`). Until then
`baker_conditional_gap3_full` stays conditional on that Prop,
and the named tag
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`
is not minted. `baker_bound_gap3_true` is the axiom-relative
vacuous close, not that mint. `baker_bound_gap3_unconditional_nogo`
records that the displayed `hGen` / `hLLL` methods fail on
`B ≥ B0`.
