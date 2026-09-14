# Beal/

Lake library sources for the Matveev–Beal complement
(`BealMatveevBeal`). The default target globs
`Beal.Matveev` plus root modules `MatveevThm14Proof`,
`MatveevLLL`, `MatveevInterpolation`, `MatveevBugeaud`,
`WuestholzSubgroup`, `WuestholzProduct`, `MatveevThreeLogs`,
`BealKraus`, `BealKrausZsig`, `BealCatalanZsig`, `BealDarmonMerel`,
`BealDarmonMerel44p`, `BealFLT13`, `BealGenuineV25`,
`BealTrueV25`, `BealUnconditionalV25`, and `BealGap1`.

`Beal.lean` re-exports `Beal.Matveev.MatveevThm14General`.
Substantial proofs live in **root** modules; files under
`Beal/Matveev/` are LEAN_PATH stubs. See `Beal/Matveev/README.md`.

Concept DOI `10.5281/zenodo.22379293`. `C1_floor = 143186215390`.
`B0_nat = 1000000`. **0 sorry.** `BealTrueV25` inhabits
`baker_bound_gap3_true` relative to `axiom darmon_merel_4413_axiom`.
`BealUnconditionalV25` proves `hGen` + `hLLL` cannot close
`B ≤ 10⁶` in Mathlib 4.12. `BealGap1` proves the gap-1 analogue
(`baker_bound_gap1` stays `def Prop`; `(1,0)` is a solution).
That is not the minted unconditional v25 tag.
