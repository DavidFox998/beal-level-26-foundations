# v25 forward Matveev and level-26 interface

Lean module:
[`Forward.lean`](Forward.lean), registered as
`BealMatveevBealV25B0Search.Forward`.

This module retrofits the v25 search line after the v30.1.7 final interface.
It records the dependency order without changing the proof status of any
search or construction boundary:

1. `MatveevBoundData` carries
   `C1_floor = 143186215390` and `B0_nat = 1000000`.
2. `Level26SearchData` carries the forward numerical surface
   `Δ = 16A⁸B⁸(A⁴+B⁴)²`,
   `v₂₉(Δ) = 26v₂₉(B+3)`,
   `13 ∣ v₂₉(Δ)`,
   `928/29 = 32`, and `32·29 = 928`.
3. `MatveevLevel26ForwardData.searchBelow1000` carries the closed
   `B < 1000` elimination proposition. The existing theorem
   `gap3_B_lt_1000_no_sol` is its proved source.
4. `MatveevLevel26ForwardData.fullB0Search` separately carries
   `gap3_B_le_B0_no_solution`, the exhaustive `B ≤ 10⁶` boundary.

`B0_search_forward`, `beal_matveev_level26_forward`, and
`v25_numerical_surface_forward` only project fields in that order. Numerical
equalities are never used backwards to construct Matveev, Tate, Mazur, Ribet,
modularity, or exhaustive-search evidence.

The principal projection theorems contain no `sorry`, `sorryAx`, axiom
declaration, `native_decide`, `Lean.ofReduceBool`, or `:= True`. The existing
`gap3_B_lt_1000_no_sol` theorem remains unchanged and retains its historical
finite-computation dependency.

Build:

```bash
lake build BealMatveevBealV25B0Search.Forward
```

Do not run `lake update`. This module does not vendor another repository.

## Exact external scan through one million

[`Full10e6.lean`](Full10e6.lean) records the explicit typed interface.
[`check_gap3_full10e6.py`](../scripts/check_gap3_full10e6.py) checks every
integer `0 ≤ B ≤ 1,000,000` using exact fourth roots and stores 10,000-value
SHA-256 checkpoints in
[`gap3_full10e6_checkpoints.json`](../certs/gap3_full10e6_checkpoints.json).
The verifier replays the range with an independent binary-search fourth root.
There are no candidate solutions in this range. This is **external
computational evidence**, not a Lean kernel proof. In particular, a hash of
these checkpoints cannot inhabit `gap3_B_le_B0_no_solution`.
`Full10e6KernelCert` remains an explicit field. No unconditional Beal result
or v25.0.2 inhabited-search release is claimed.

`MaskSound.lean` checks ten modular masks using ordinary kernel reduction
(`by decide`) and proves that any actual solution passes every mask.
`Chunked10e6.lean` connects a checked 500-value interval to the no-solution
statement and checks one sample interval. The 2,000 intervals covering
`B < 10⁶` have **not** all been checked and combined. These modules therefore
do not inhabit `Full10e6KernelCert`; the external digest is not a proof input.