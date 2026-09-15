# Beal/

Lake library sources for the Matveev–Beal complement
(`BealMatveevBeal`). The default target globs
`Beal.Matveev` plus root modules `MatveevThm14Proof`,
`MatveevLLL`, `MatveevInterpolation`, `MatveevBugeaud`,
`WuestholzSubgroup`, `WuestholzProduct`, `MatveevThreeLogs`,
`BealKraus`, `BealKrausZsig`, `BealCatalanZsig`, `BealDarmonMerel`,
`BealDarmonMerel44p`, `BealFLT13`, `BealGenuineV25`,
`BealTrueV25`, `BealUnconditionalV25`, `BealGap1`, `BealGap2`,
`BealGap4`, `BealGap5`, `BealGap6`, `BealGap7`, `BealGap8`,
and `BealGap9`.

`Beal.lean` re-exports `Beal.Matveev.MatveevThm14General`.
Substantial proofs live in **root** modules; files under
`Beal/Matveev/` are LEAN_PATH stubs. See `Beal/Matveev/README.md`.

Concept DOI `10.5281/zenodo.22379293`. `C1_floor = 143186215390`.
`B0_nat = 1000000`. **0 sorry.** `BealTrueV25` inhabits
`baker_bound_gap3_true` relative to `axiom darmon_merel_4413_axiom`.
`BealUnconditionalV25` proves `hGen` + `hLLL` cannot close
`B ≤ 10⁶` in Mathlib 4.12. `BealGap1` proves the gap-1 analogue
(`baker_bound_gap1` stays `def Prop`; `(1,0)` is a solution).
`BealGap2` proves the gap-2 analogue (`baker_bound_gap2` stays
`def Prop`; `B` odd, `A` even; `3 ∣ B` impossible; no `(1,0)`).
`BealGap4` proves the gap-4 analogue (`baker_bound_gap4` stays
`def Prop`; `B` odd, `A` even; `3 ∣ B` compatible; `5 ∣ B`
impossible; no `(1,0)`).
`BealGap5` proves the gap-5 analogue (`baker_bound_gap5` stays
`def Prop`; `B` even, `A` odd; `3 ∣ B` impossible; `5 ∣ B`
impossible by 5-descent; no `(1,0)`).
`BealGap6` proves the gap-6 analogue (`baker_bound_gap6` stays
`def Prop`; `B` odd, `A` even; even `B` dies as `6` or `14`
mod 16; `3 ∣ B` impossible by 3-descent; `5 ∣ B` compatible;
no `(1,0)`).
`BealGap7` proves the gap-7 analogue (`baker_bound_gap7` stays
`def Prop`; `B` even, `A` odd; `3 ∣ B` compatible; `5 ∣ B`
impossible (`C ≡ 2`); `7 ∣ B` impossible by 7-descent;
no `(1,0)`).
`BealGap8` proves the gap-8 analogue (`baker_bound_gap8` stays
`def Prop`; `B` odd, `A` even; even `B` dies after nine `/2`
as residue `8`; `3 ∣ B` impossible (`C ≡ 2`); `5 ∣ B`
impossible (`C ≡ 3`); `7 ∣ B` compatible; no `(1,0)`).
`BealGap9` proves the gap-9 analogue (`baker_bound_gap9` stays
`def Prop`; `B` even, `A` odd; `3 ∣ B` impossible by
3-descent; `5 ∣ B` impossible (`C ≡ 4`); `7 ∣ B`
compatible (`A⁴ ≡ 2`); no `(1,0)`).
That is not the minted unconditional v25 tag.
