# v9.2.0 Tate Steps 6-7 at 2 for Frey Y² = X(X−A⁴)(X+B⁴)

`lean/BealLevel26Foundations/Beal/FullProof/BealFreyTateConductor.lean`

Mathlib 4.12 has `WeierstrassCurve.Δ` and no
Tate / Kodaira / conductor `N(E)` API.
v9.1.0 encoded Tate 1975 Step 2 as a
function of valuations (Silverman AEC IV.9).
This slice adds Steps 6-7 at 2.

Inhabited extra (axioms `[propext, Quot.sound, Classical.choice]`):

- `c₆ = -32 * (B⁴−A⁴) * (2(B⁴−A⁴)²+9 A⁴ B⁴)`
- `v₂(c₆) ≥ 6` when `A ≠ B` (the factor 32
  and an even tail from A,B parity)
- `conductorExponentTate67` / `conductorExponentTate2`
  (Step 6-7 table, upper bound `≤ 5`)
- `tate_2adic_exponent_le5`: `v₂(c₄) ≥ 4`
  and the table give exponent `≤ 5`
- `tate_odd_exponent_le_one` (keeps odd `q`
  exponent exactly 1, hence `≤ 1`)
- `tate_conductor_bound_rhs = 2⁵ * rad(AB(B+3)) * 13`
- packed `2^{f₂} * oddRad` divides that RHS

Inhabited from v9.1.0:

- `c₄ = 16 * (A⁸ + A⁴B⁴ + B⁸)` on
  `freyCurve ↑A ↑B 4 4`
- `v₂(c₄) ≥ 4` when `A` or `B` is nonzero,
  so Step 2 does **not** finish at 2
- Odd `q | A*B*(B+3)` with pairwise
  coprime bases and `A,B > 0`:
  `v_q(c₄)=0`, `v_q(Δ)>0`,
  `conductorExponentTate = 1`
- `tate_rhs = 2⁵ * rad(AB(B+3)) * 13`
  and `rad(ABC) | tate_rhs`

Uninhabited:

- `frey_tate_conductor`: exists a Tate
  conductor `N` with
  `N | 2⁵ * rad(AB(B+3)) * 13`.
  Mathlib has no `N(E)`.  The packed
  valuation bound is not `N(E)`.
  Do not inhabit with `N = |Δ|`
  (false: `A⁸` does not divide
  `rad(ABC)`) or `N = 1` (trivial).

Keeps `baker_bound_gap3` Prop, the
three Zsig Props, `conductor_86` Prop,
`B14_honest` Prop.  Survivor
`63982 = 2 * 31991` still shows
`N` does not divide `2⁵ * 3 * 13`.
Not BCDT.
