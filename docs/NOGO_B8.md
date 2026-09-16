# LLL `|Λ| ≥ B⁻⁸` nogo

## Phase lift nogo e5a95f5: |Λ|≥B⁻⁸ uninhabited, LLL target ≡ no_sol_ge_B0

Archived from branch `phase-lll-lift-b8` at `e5a95f5`.
This file is documentation only. It does **not** mint v25.
No further lattice `C` scaling.

### Foundation (this `main`)

- `main` at the time of this note’s parent: `6247c63`
- annotated tag `v24.1-foundation-B1000-Lambda-B9-6247c63` → `6247c63`
- closed computational slice: `B < 1000` (ten foldl shards of 100)
- on a solution with `B ≥ 100`: `|Λ| ≤ 2/B⁹` (`f12ad03`)
- `|Λ| ≥ B⁻⁸` stays `def Prop`

### Rank-3 shape nogo tag (unchanged)

- annotated tag `v24-v24x-final-rank3-shape-nogo` → `c1d173e`
- not moved; not retargeted at `e5a95f5`

### What `e5a95f5` proved

Root module `LLLTargetB8_C1_lower_bound.lean` on Lake target
`BealMatveevBealV25B0Search` (not the default glob):

- `two_div_pow_nine_lt_one_div_pow_eight`: `B ≥ 3` ⇒ `2/B⁹ < 1/B⁸`
- `C1_le_8_impossible` / `C1_le_8_impossible_of_sol`: on a gap-3
  solution with `B ≥ B0 = 10⁶`, no `C1' ≤ 8` is a lower bound for `|Λ|`
- `LLL_reduces_C1_to_lt_nine_iff_no_sol_ge_B0`: given `|Λ| ≤ 2/B⁹`,

  `LLL_reduces_C1_to_lt_nine` ↔ no gap-3 solution with `B ≥ B0`

  So the LLL `C1' ≤ 8` target is not an independent lattice lemma.
  It holds if and only if the large-`B` branch is already empty
  (vacuous `∀` on an empty set of solutions).

`C1_lower_bound_false` and `LLL_cannot_reach_B8`
(`¬ LLL_reduces_C1_to_lt_nine`) stay `def Prop`. Inhabiting the
negation would need a witness solution with `B ≥ B0`.

Typical Bugeaud–Laurent `C1'` is `30`–`50`, still `> 8`.
`C1' ≥ 9` does not beat `|Λ| ≤ 2/B⁹`.

Phase-lift lattices (`L` `λ₁=1`, `L'` `C=10⁴⁸` `λ₁=C`,
`L3` `C₃=10³⁰` `λ₁=1` not `C₃^{1/3}`) do not produce `|Λ| ≥ B⁻⁸`.
Stop scaling `C`.

### Pins

| name | SHA |
|---|---|
| foundation / parent of this note | `6247c63` |
| rank-3 shape nogo tag | `c1d173e` |
| phase-lift C1' nogo | `e5a95f5` on `phase-lll-lift-b8` |

v25 is not minted. Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390`. `B0_nat = 1000000`.
