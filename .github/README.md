[![Latest Mint](https://zenodo.org/badge/DOI/10.5281/zenodo.22450737.svg)](https://doi.org/10.5281/zenodo.22450737)
[![Hook 22379293](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)

### v4.27.0 X0(26)(Q) Cusps P-mem Locked — DOI 22450737

| Name | What |
|---|---|
| X0_26_Q / X0_26_cusps | = [1,2,13,26] rfl P.mem mem_1 mem_2 mem_13 mem_26 not_mem_3 |
| hInList_X0_26 / hNotIn_X0_26 | P.mem lemmas for hGeomForbid_typed_true |
| beal_forall_eq_exponent13_bridge | none = beal_forall_from_ribet = Contradiction.beal_exponent13_from_ribet BRIDGE none hGeomForbid_typed_true (hNotIn hInList) |
| beal13_forall_bridge_triple | none ⟨exponent13,forall,bridge⟩ — formerly final_* |

Hook `22379293` `IsVersionOf` `22272382` is metadata only. Mint `10.5281/zenodo.22450737` findable (index ~19 of the parallel parent). Original-concept latest remains v4.0.9 `10.5281/zenodo.22322627`.

PARI lock: 26a1 Δ `-17576` 26b1 Δ `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260` image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.

# .github/

GitHub Actions for
[DavidFox998/beal-level-26-foundations](https://github.com/DavidFox998/beal-level-26-foundations).

[`workflows/main.yml`](workflows/main.yml) runs on pushes and pull
requests to **`main`**:

1. `lake build BealLevel26Foundations`
2. `lake build BealLevel26FoundationsScaffold`
3. `lake build BealLevel26FoundationsReal`
4. `bash scripts/verify-scaffold.sh`

A green CI run is a Lean 4.12 / Mathlib 4.12 build plus the scaffold
script. It is not a DOI and not an unconditional `BealTheorem`.
Current Foundations tag `v4.2.0-full-chain` does not change this
workflow.
