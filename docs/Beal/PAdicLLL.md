# p-adic LLL / `A ∈ [B, B+10]` no-go (not a v25 mint)

Lean: [`PAdicLLL.lean`](../../PAdicLLL.lean)
(root module; `Beal/Matveev/PAdicLLL.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.PAdicLLL`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `v24-v24x-final-bugeaud-laurent-nogo`. This file
records that Mathlib 4.12 already has `PadicInt` / `ℤ_[p]`, but
**not** LLL over `ℤ_p`. It does **not** fork Mathlib, does **not**
open a Mathlib PR, does **not** change `lean-toolchain`, and does
**not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.
Floor lattice `b1=(1,0)` has Euclidean length `1 < B0`
(`lll_euclidean_lower_bound_fails`); `LLL_reduces_bound_to_B0_theorem`
stays `def Prop`.

## What Mathlib 4.12 has

- `PadicInt p` / `ℤ_[p]` = `{x : ℚ_[p] // ‖x‖ ≤ 1}`
- `ℚ_[p]`, `padicNorm`, `padicValNat`
- `Real.log` (archimedean)

## What Mathlib 4.12 does not have

- LLL over `ℤ_p` (no LLL module at all)
- Iwasawa p-adic logarithm `log_p : ℚ_[p] → ℚ_[p]`
- Bugeaud–Laurent 1996 explicit linear forms in two p-adic logs
- Tate / Ribet / Mazur 13-torsion / `dim S₂(32) = 1`

That is why `p_adic_LLL_reduction`, `hLLL_padic`,
`baker_bound_B0_1e6`, and `LLL_reduces_bound_to_B0` stay
uninhabited `def Prop`. Defining `p_adic_LLL_reduced := True`
would inhabit `∀ L, ∃ L', reduced L'` and is forbidden.

## What is proved (0 sorry)

- `Z_p` is an alias of Mathlib `PadicInt`; `‖x‖ ≤ 1` on that
  subtype. This is **not** an LLL lattice.
- For `B ≥ 2`, `2(B+10)⁴ < (B+1)¹³` via `n ≥ 3 ⇒ n+9 ≤ 4n` and
  `512 < n⁹`.
- On a gap-`k` solution with `k ≥ 1` and `B ≥ 2`,
  `¬ A ≤ B+10`. Combined with GapK `B < A`, the window
  `[B, B+10]` contains no solutions. The proposed
  `check_gap3_range` / 977 `native_decide` shards with
  `A ∈ [B, B+10]` are therefore false, and
  `matveev_gap3_lower` is left as the existing integer-gap
  close.
- The toy comparison `4 ≤ 1000` (`four_le_C1_padic_placeholder`)
  does **not** bound `B`.
- Wrapped Bugeaud–Laurent nogo: real logs lose every `C1 ≥ 1`
  including the placeholder `1000`; 2-adic valuation of the
  equation is compatible on odd `k`.

`#print axioms p_adic_LLL_unconditional_nogo` is
`[propext, Classical.choice, Quot.sound]` only.

## Floor lattice `b1=(1,0)` (still not a B0 cutoff)

The draft v25 lattice `b1=(1,0)`, `b2=(⌊C_LLL α⌋, C_LLL)` with
`C_LLL = C1_floor²` and `α(B) = log(B+3)` has floor error
`< 1`, which kills the integer kernel `u a + v C1 = 0`. It does
**not** kill the lattice vector `(1,0)`: that combination has
Euclidean length `1 < B0`. So the draft
`lll_lower_bound` (`‖u b1 + v b2‖ ≥ B0` for all nonzero
`(u,v)`) is false. `C1_floor / 2 > B0` is a numeral, not `λ₁`.
LLL/Minkowski *upper*-bound a short vector.

`nat_int_form_has_kernel` records the naive form always
vanishes at `(C1, -a)`. `lll_euclidean_lower_bound_fails` and
`floor_lattice_nogo` are theorems. `LLL_reduces_bound_to_B0_theorem`
and `beal_gap3_4_4_13_unconditional_v25_draft` stay `def Prop`.
`#print axioms lll_euclidean_lower_bound_fails` is
`[propext, Classical.choice, Quot.sound]` (`Real.log` / `Real.sqrt`).

Successor integer-form nogo: [`PAdicLLL_ZeroAxiom.md`](PAdicLLL_ZeroAxiom.md).
v25 is not minted.
