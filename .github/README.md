[![Matveev-Beal CI](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml/badge.svg)](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml)
[![Concept DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)

# .github/

GitHub Actions for
[DavidFox998/beal-level-26-foundations](https://github.com/DavidFox998/beal-level-26-foundations)
(display title: foundations-level-26 Matveev–Beal). The GitHub slug is
unchanged so concept DOI `10.5281/zenodo.22379293` stays attached.
Monorepo `beal-conjecture` stays `beal-conjecture`.

[`workflows/main.yml`](workflows/main.yml) runs on pushes and pull
requests to **`main`**, and on `workflow_dispatch`:

1. `lake exe cache get`
2. `lake build BealMatveevBeal` — default target; 0 `sorry`
3. `lake build BealMatveevBealV25Rank3` — separate Rank-3 B0/C
   cutoff nogo target; not in the default glob
4. `lake build BealMatveevBealV25B0Search` — separate `B<1000`
   foldl shards of 100 plus `LLLTargetB8` (`C=10⁴⁸` `L'` and
   3-dim `L3` with `C₃=10³⁰`, `λ₁=1`; `|Λ|≥B⁻⁸` stays `def Prop`)
   and `Gap3B0Million` (10k-shard foldl wiring; `allShardsTrue_eq_true`
   stays `def Prop`; shards are not `native_decide`'d);
   full `B ≤ B0` stays `def Prop`
5. `bash scripts/verify-matveev-beal.sh` — AMS / Math. Comp. referee
   surface: 0 `sorry`, `matveev_gap3_lower` is the B≤10^6 integer-gap
   close, `C1_floor=143186215390`, `B0_nat=1000000`, `gap3_A_bounds` and
   `matveev_product_bound_of_B_le_B0` present, concept DOI and slug
   on `CITATION.cff`

It does **not** run `lake build BealLevel26FoundationsScaffold` or
`BealLevel26FoundationsReal` (those targets left with the relocated
v24.4.0 kernel in `beal-conjecture`). It does **not** run
`scripts/verify-scaffold.sh` (historical X0(26) checklist).

A green run is a Lean 4.12 / Mathlib 4.12 build of the B≤10^6
integer-gap Matveev lower bound plus the elementary CF lemmas in
`MatveevLLL.lean`. It is not a minted `v25.0.0` tag, not
interpolation, and not an unconditional `∀ B ¬∃ A` (`hLLL` /
`bugeaud_LLL_reduction_proof` stay `def Prop`).
