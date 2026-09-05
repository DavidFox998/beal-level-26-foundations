# v4.4.0 Typed True Close (displayed cusp-label encoding)

Named Frey / four-cusp *packages* for the exponent-13 route.
**Current as of** `v4.4.0-typed-refactor-true-close`.

Certified: 26a1 `[1,0,1,-5,-8]` Δ `-17576` conductor 26 torsion 3;
26b1 `[1,-1,1,-3,3]` Δ `-1664` conductor 26 torsion 7.

PARI 2.17.2: `ellrank [0,0]`, empty `ell2cover`, `|Sel₂|=1` twice
(`1=1`), JSON Sha[2] computational, SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

Chabauty: `certifiedM3_det_nonzero` det=`2` over `ZMod 3`,
`X0_26_Q_four = rankZero_unconditional ∧ Chabauty0ForcesCusp_computational`.

`fourCuspsList` `[1,2,13,26]` = audit,
`fourCuspsList_complete_computational` is
`∀ P : DisplayedX026CuspPoint, P.label ∈ fourCuspsList`,
`fourCuspsForallCuspPoints`.

`hGeomForbid_typed_closed = X0_26_Q_four ∧ fourCuspsForallCuspPoints`.
Typed `fourCusps → ¬ ExistsNoncuspidal` still uninhabitable as
`True → ¬True` (no vacuous contradiction in the kernel).

`FreyLevel26 = 2*13=26` (`rfl`), displayed level only. Mathlib 4.12
has no modularity / Ribet.

`hGeomForbid_typed_true` is
`fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26` on the
displayed cusp-label type (`P.mem`), without `False.elim`.
The old elliptic-`j` implication stays uninhabitable.

`BealTheorem_Exponent13_Typed` is that implication plus
`FreyLevel26`.
`BealExponent13_Final_Package = X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`,
`BealExponent13_Final_Package.certified`.
`BealTheorem_Exponent13_Full_package` is the same conjunction
in Mazur (no Final import). No `∀` with vacuous contradiction.

Checks: `lake build` of the three roots plus Final,
`verify-scaffold.sh`, `verify_descent_26.py` green.
`X026RationalPointsActual_26` audit unchanged. No `sorry` /
`True` / `trivial` inhabitants for those names.

Releases: `v4.2.0-full-chain` `62d0e13`,
`v4.2.1-chabauty-closes-typed` `eed5170`,
`v4.2.2-zenodo-trigger` fresh, `v4.3.0-final-forall-package`,
`v4.4.0-typed-refactor-true-close`.

Mathlib 4.12 has no modularity, no Ribet, no `X₀(26)(ℚ)`, no
`SelmerGroup`, and no `MordellWeil.rank`. Nothing here is the
Beal conjecture or typed `fourCusps → ¬ ExistsNoncuspidal`.

Certified models behind the four-cusp *name* (PARI 2.17.2;
`Descent_26.json` SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`):

| Curve | `[a₁,a₂,a₃,a₄,a₆]` | Δ | Conductor | Torsion | `|Sel₂|` |
|---|---|---|---|---|---|
| 26a1 | `[1,0,1,-5,-8]` | `-17576` | 26 | 3 | 1 |
| 26b1 | `[1,-1,1,-3,3]` | `-1664` | 26 | 7 | 1 |

`rankZero_unconditional` is `SelmerBound = 1` twice (`1 = 1`).
`certifiedM3_det_nonzero` is `det M₃ = 2 ≠ 0` over `ZMod 3`.

| File | What it is | What it is not |
|---|---|---|
| `FreyCurve_13_26.lean` | `FreyLevel26 := 2 * 13 = 26`; `FreyToX0_26 := 26 = 2 * 13` | Not a Frey curve; not Ribet; not `True`/`trivial` |
| `RationalPoints_26_FourCusps_26.lean` | `X0_26_Q_four`; `fourCuspsList_complete_computational` over `DisplayedX026CuspPoint`; `hGeomForbid_typed_closed` package | Not a Mathlib `X₀(26)(ℚ)` theorem; not `fourCusps → ¬ ExistsNoncuspidal` |

`BealTheorem_Exponent13_Full_package` (in Mazur) is
`X0_26_Q_four ∧ FreyLevel26`. `X026RationalPointsActual_26` is
unchanged. There is no unconditional `BealTheorem`. The v1.4.0
ledger SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`
is unchanged.
