[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22452680.svg)](https://doi.org/10.5281/zenodo.22452680)
[![Hook 22379293](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)

### v4.28.0 X0(26)(Q) Cusps P-mem Locked — DOI 22452680

| Name | What |
|---|---|
| X0_26_Q | [1,2,13,26] rfl P.mem mem_1 mem_2 mem_13 mem_26 not_mem_3 hInList hNotIn for hGeomForbid |
| beal_forall_eq_exponent13_bridge | none = beal_forall_from_ribet = Contradiction.beal_exponent13_from_ribet BRIDGE none hGeomForbid_typed_true (hNotIn hInList) |
| beal13_forall_bridge_triple | none ⟨exponent13,forall,bridge⟩ |

DOI `22452680` findable records prior mint `22450737` hook `22379293` `IsVersionOf` `22272382` honest original latest `22322627`.

PARI lock: 26a1 Δ `-17576` 26b1 Δ `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260` image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.

# docs/Final/

Iter / Forall / typed-bridge docs. Lean sources live in
[`lean/BealLevel26Foundations/Final/`](../../lean/BealLevel26Foundations/Final/README.md).
Package table: [`../BealExponent13_Iter_Package.md`](../BealExponent13_Iter_Package.md).
Forall reduction sketch (v4.31.0, p=13 working prime):
[`BealExponent13_Forall.md`](BealExponent13_Forall.md).
v4.35.0: `#check is13CaseForcesGcdGt1Sketch_inhabited` is the typed
close (`BealTheorem_Exponent13_Typed`, none).
`Is13CaseForcesGcdGt1Sketch` stays uninhabited. Still not `∀ A B C`.
v4.40.0: `FreyCurve13_of_BealCounterexampleBases` is the working-prime
Weierstrass `freyCurve ↑A ↑B 13 13`.  Not a noncuspidal `X₀(26)`
point. `ExistsNoncuspidal_26_of_Is13CaseSketch` stays uninhabited.
