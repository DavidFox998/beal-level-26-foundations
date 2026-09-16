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
   stays `def Prop`; shards are not `native_decide`'d) plus
   `LLLTargetB8_C1_lower_bound` (`C1'≤8` impossible on a solution;
   `LLL_cannot_reach_B8` stays `def Prop`) plus
   `DarmonMerelFrey4413` (displayed Frey `(4,4,13)`;
   `level_32_no_newform` stays `def Prop`) plus
   `Level32Table` (LMFDB `32a1` q-exp by `𝔽_p` counts;
   `l=3,5` match, `p=29` mismatches good reduction;
   `level_32_no_newform_for_Frey_gap3` stays `def Prop`) plus
   `Level928Table` (`29 ∣ ABC` split, displayed residual `928`;
   `level_928_no_match_bad_29` stays `def Prop`) plus
   `Ribet29C_Lowering` (`v₂₉(Δ)=26 v₂₉(C)`; `a₇=−4` on residue
   `(2,3)`; `ribet_29C_lowers_to_32` stays `def Prop`);
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
