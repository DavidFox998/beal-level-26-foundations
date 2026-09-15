# Effective level-lowering / p-adic linear forms (not a v25 mint)

Lean: [`EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.lean`](../../EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.lean)
(root module; `Beal/Matveev/EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.lean`
is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `v24-v24x-final-gapK-generic-nogo`. Re-exports the
honest `BealGapK` infrastructure. This does **not** inhabit
`baker_bound_B0_1e6`, does **not** replace
`darmon_merel_4413_axiom`, and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

None of Bugeaud–Laurent 1996, Kraus 1997, Oesterlé, Ribet
level-lowering, Kummer's regular-prime FLT, or a p-adic LLL
witness is in Mathlib 4.12. Real-log Matveev / LLL already lose
every `C1 ≥ 1` on gap solutions with `B ≥ B0`. A displayed
p-adic lower bound that would beat `B⁴/A⁴` is the same missing
inhabitant.

The estimate `C ≤ 73` for `B ≤ 10⁶` assumes `A ≤ 10⁶` as well
and is circular as an unconditional Baker close. Under
`A ≤ B0` and `B ≤ B0` one does get `C < 100`, because
`C¹³ ≤ 2 · B0⁴ = 2 · 10²⁴ < 10²⁶ = 100¹³`. Positive `k` does
**not** force `B ≤ 72`: `C = B+k` grows with `B`. On any gap
solution with `B ≥ B0` and `k ≥ 1` one has `100 ≤ C` and
`¬ C ≤ 73`.

`BealGap1`–`BealGap15` and `BealGapK` stay in the tree.
0 sorry. No new axiom.

Do **not** inhabit `hGen_padic` / `hLLL_padic` /
`baker_bound_B0_1e6` / `beal_conjecture_4413` /
`darmon_merel_4413_no_coprime_unconditional` /
`fermat_last_theorem_thirteen_unconditional` /
`ribet_level_lowering_to_32_unconditional`.

## What is proved (0 sorry)

- GapK wrappers: odd-`k` parity (`B` even, `A` odd), even-`k`
  forces `A` even only, `gcd(B,B+k)=gcd(B,k)∣k`,
  `p∣k` and `p∣B` force `p∣A`, `v_p(k)=1` descents for
  `p=3,5,7,11,13`, residue kills with the displayed
  congruence hypotheses, remaining coprime is axiom-relative
  Darmon–Merel.
- `C_lt_hundred_of_A_B_le_B0` — conditional on `A,B ≤ B0`.
- `C_ge_hundred_of_B_ge_B0` / `not_C_le_seventy_three_of_B_ge_B0`
  — on `B ≥ B0` and `k ≥ 1`, `C` is already `≥ 1000001`.
- Logs / LLL still lose every `C1 ≥ 1` (including `C1_floor`)
  on gap solutions with `B ≥ B0`.
- `baker_bound_B0_1e6` / `hGen_padic` / `hLLL_padic` /
  `baker_bound_gapK_unconditional_wins` / `beal_conjecture_4413`
  stay `def Prop`.

`#print axioms baker_bound_B0_1e6_unconditional_nogo` is
`[propext, Classical.choice, Quot.sound]` only.
