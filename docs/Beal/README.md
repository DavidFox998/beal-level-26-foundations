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
- [`BealGap7.md`](BealGap7.md) — gap-7 `A⁴+B⁴=(B+7)¹³` no-go (`v24-v24x-final-gap7-nogo`); `B` even `A` odd; `3∣B` compatible; `5∣B` impossible (`C≡2`); `7∣B` impossible by 7-descent
- [`BealGap8.md`](BealGap8.md) — gap-8 `A⁴+B⁴=(B+8)¹³` no-go (`v24-v24x-final-gap8-nogo`); `B` odd `A` even; even `B` dies after nine `/2` residue `8`; `3∣B` impossible (`C≡2`); `5∣B` impossible (`C≡3`); `7∣B` compatible
- [`BealGap9.md`](BealGap9.md) — gap-9 `A⁴+B⁴=(B+9)¹³` no-go (`v24-v24x-final-gap9-nogo`); `B` even `A` odd; `3∣B` impossible by 3-descent (`C₁=B₁+3`); `5∣B` impossible (`C≡4`); `7∣B` compatible (`A⁴≡2`)
- [`BealGap10.md`](BealGap10.md) — gap-10 `A⁴+B⁴=(B+10)¹³` no-go (`v24-v24x-final-gap10-nogo`); `A` even; even `B` last-step leftover `B₃≡2∨4`; `3∣B` compatible; `5∣B` impossible by 5-descent (`C₁=B₁+2`); `7∣B` impossible (`C≡3`)
- [`BealGap11.md`](BealGap11.md) — gap-11 `A⁴+B⁴=(B+11)¹³` no-go (`v24-v24x-final-gap11-nogo`); `B` even `A` odd; `3∣B` impossible (`C≡2`); `11∣B` impossible by 11-descent (`C₁=B₁+1`); `5∣B` compatible (`A⁴≡1`); `7∣B` compatible (`A⁴≡4`)
- [`BealGap12.md`](BealGap12.md) — gap-12 `A⁴+B⁴=(B+12)¹³` no-go (`v24-v24x-final-gap12-nogo`); `B` odd `A` even; even `B` dies after six `/2` residue `12`; `3∣B` impossible by 3-descent (`C₁=B₁+4`); `5∣B` impossible (`C≡2`); `7∣B` impossible (`C≡5`)
- [`BealGap13.md`](BealGap13.md) — gap-13 `A⁴+B⁴=(B+13)¹³` no-go (`v24-v24x-final-gap13-nogo`); `B` even `A` odd; `3∣B` compatible (`A⁴≡1`); `5∣B` impossible (`C≡3`); `7∣B` impossible (`C≡6`); `11∣B` impossible (`C¹³≡8`); `13∣B` impossible by 13-descent (`C₁=B₁+1`)
- [`BealGap14.md`](BealGap14.md) — gap-14 `A⁴+B⁴=(B+14)¹³` no-go (`v24-v24x-final-gap14-nogo`); `B` odd `A` even; even `B` dies after three `/2` last `2(4B₃+7)¹³` residue `6` or `14`; `3∣B` impossible (`C≡2`); `5∣B` impossible (`C≡4`); `7∣B` impossible by 7-descent (`C₁=B₁+2`)
- [`BealBakerBoundGap3.md`](BealBakerBoundGap3.md) — kernel `baker_bound_gap3` stays a `def Prop`; Mathlib-only close remains open

Older Frey / Zsigmondy / modular-elimination notes in this
folder are historical kernel documentation. They do not inhabit
`baker_bound_gap3`. Concept DOI `10.5281/zenodo.22379293`.
