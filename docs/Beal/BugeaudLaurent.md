# Bugeaud–Laurent / p-adic LLL import plan (not a v25 mint)

Lean: [`BugeaudLaurent.lean`](../../BugeaudLaurent.lean)
(root module; `Beal/Matveev/BugeaudLaurent.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BugeaudLaurent`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `v24-v24x-final-effective-padic-nogo`. This file
records **what Mathlib 4.12 has** and **what would be needed**
to inhabit `baker_bound_B0_1e6`. It does **not** fork Mathlib,
does **not** open a Mathlib PR, does **not** change
`lean-toolchain`, and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

## What Mathlib 4.12 has

- `ℚ_[p]`, `padicNorm`, `padicValNat`
- `WeierstrassCurve` / `EllipticCurve`
- abstract `ModularForm` spaces
- `Real.log` (archimedean)

## What Mathlib 4.12 does not have

- Iwasawa p-adic logarithm `log_p : ℚ_[p] → ℚ_[p]`
- Bugeaud–Laurent 1996 explicit linear forms in two p-adic logs
- LLL over `ℤ_p` (no LLL module at all)
- Tate's algorithm / Néron conductor
- Ribet level-lowering, Mazur 13-torsion on this Frey curve,
  `dim S₂(32) = 1` / newform `32a1`

That is why `baker_bound_B0_1e6`, `hGen_padic`, and
`hLLL_padic` stay uninhabited `def Prop`.

## What is proved (0 sorry)

- On odd `k`, GapK parity gives `B` even and `A` odd, hence
  `C = B+k` odd. Then `v₂(A⁴+B⁴) = v₂(C¹³) = 0`: the 2-adic
  valuation of the equation is compatible and does **not**
  replace p-adic logs.
- `v₂(B⁴) ≥ 4` when `B` is even and positive.
- Real logs lose every `C1 ≥ 1` on `B ≥ B0`, including
  `C1_floor` **and** the placeholder numeral `1000`.
- `C < 100` only under `A,B ≤ B0`; on `B ≥ B0` one has
  `C ≥ 1000001`.
- `bugeaud_laurent_1996_two_logs` / `p_adic_LLL_reduction` /
  `S2_32_dimension_one` / `baker_bound_B0_1e6` stay `def Prop`.

`#print axioms bugeaud_laurent_unconditional_nogo` is
`[propext, Classical.choice, Quot.sound]` only.
