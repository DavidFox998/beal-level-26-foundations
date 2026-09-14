# docs/Beal/

Notes for the Matveev–Beal Lean modules in this repository.
Each file names the root Lean module, the locked numerals
`C1_floor = 143186215390` and `B0_nat = 1000000`, and what
stays an uninhabited `def Prop`.

Current Matveev–Beal track:

- [`BealMatveevThm14.md`](BealMatveevThm14.md) — integer-gap `B≤B0`
- [`BealMatveevLLL.md`](BealMatveevLLL.md) — CF lemmas, lattice, SVT
- [`BealMatveevBugeaud.md`](BealMatveevBugeaud.md) — displayed and uniform-`C` LLL no-go
- [`BealMatveevInterpolation.md`](BealMatveevInterpolation.md) — Δ, Schwarz, jet invertibility
- [`BealWuestholzSubgroup.md`](BealWuestholzSubgroup.md) — no uniform `c`
- [`BealWuestholzProduct.md`](BealWuestholzProduct.md) — full-order product packaging
- [`BealMatveevThreeLogs.md`](BealMatveevThreeLogs.md) — log-method `C1`-vs-ratio no-go
- [`BealKraus.md`](BealKraus.md) — displayed Frey / Kraus valuation no-go
- [`BealKrausZsig.md`](BealKrausZsig.md) — Gaussian / Thue argument-form no-go
- [`BealCatalanZsig.md`](BealCatalanZsig.md) — Catalan / Zsigmondy no-go
- [`BealDarmonMerel.md`](BealDarmonMerel.md) — Darmon–Merel / Ribet residual-level no-go
- [`BealDarmonMerel44p.md`](BealDarmonMerel44p.md) — Darmon–Merel signature (4,4,p) / Ribet-to-32 no-go
- [`BealFLT13.md`](BealFLT13.md) — FLT 13 / Darmon–Merel 44p / 3-adic descent no-go
- [`BealGenuineV25.md`](BealGenuineV25.md) — Darmon–Merel (4,4,13) + 3-adic vacuous-close no-go (`v24-v24x-final-genuine-v25-nogo` at `2b4ee3b`)
- [`BealTrueV25.md`](BealTrueV25.md) — axiom-relative `baker_bound_gap3_true` (Darmon–Merel axiom; not the minted v25 tag)
- [`BealUnconditionalV25.md`](BealUnconditionalV25.md) — `hGen` + `hLLL` no-go; unconditional mint still waits
- [`BealGap1.md`](BealGap1.md) — gap-1 `A⁴+B⁴=(B+1)¹³` no-go (`v24-v24x-final-gap1-nogo`); coprime from the start; `3∣B` compatible
- [`BealGap2.md`](BealGap2.md) — gap-2 `A⁴+B⁴=(B+2)¹³` no-go (`v24-v24x-final-gap2-nogo`); `B` odd `A` even; `3∣B` impossible like `f1cb039`
- [`BealGap4.md`](BealGap4.md) — gap-4 `A⁴+B⁴=(B+4)¹³` no-go (`v24-v24x-final-gap4-nogo`); `B` odd `A` even; `3∣B` compatible like gap-1; `5∣B` impossible
- [`BealGap5.md`](BealGap5.md) — gap-5 `A⁴+B⁴=(B+5)¹³` no-go (`v24-v24x-final-gap5-nogo`); `B` even `A` odd; `3∣B` impossible like `f1cb039`; `5∣B` impossible by 5-descent
- [`BealGap6.md`](BealGap6.md) — gap-6 `A⁴+B⁴=(B+6)¹³` no-go (`v24-v24x-final-gap6-nogo`); `B` odd `A` even; even `B` dies as `6` or `14` mod 16; `3∣B` impossible by 3-descent (`C₁=B₁+2`); `5∣B` compatible
- [`BealBakerBoundGap3.md`](BealBakerBoundGap3.md) — kernel `baker_bound_gap3` stays a `def Prop`; Mathlib-only close remains open

Older Frey / Zsigmondy / modular-elimination notes in this
folder are historical kernel documentation. They do not inhabit
`baker_bound_gap3`. Concept DOI `10.5281/zenodo.22379293`.
