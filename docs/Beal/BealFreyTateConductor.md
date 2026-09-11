# v9.1.0 Tate Step 2 for Frey Y² = X(X−A⁴)(X+B⁴)

`lean/BealLevel26Foundations/Beal/FullProof/BealFreyTateConductor.lean`

Mathlib 4.12 has `WeierstrassCurve.Δ` and no
Tate / Kodaira / conductor `N(E)` API.
This file encodes Tate 1975 Step 2 as a
function of valuations (Silverman AEC IV.9).

Inhabited (axioms `[propext, Quot.sound, Classical.choice]`):

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
  Step 2 does not give the 2-adic
  exponent.  Do not inhabit with
  `N = |Δ|` (false: `A⁸` does not
  divide `rad(ABC)`) or `N = 1`
  (trivial).

Keeps `baker_bound_gap3` Prop, the
three Zsig Props, `conductor_86` Prop,
`B14_honest` Prop.  Survivor
`63982 = 2 * 31991` still shows
`N` does not divide `2⁵ * 3 * 13`.
Not BCDT.
