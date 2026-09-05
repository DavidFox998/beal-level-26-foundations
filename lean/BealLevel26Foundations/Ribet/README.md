# lean/BealLevel26Foundations/Ribet/

Typed `LevelLowering_26` certificate data from `v3.0.0-ribet`, the
v4.0.5 displayed Ribet-existence package, the v4.0.6 split
between existence and the four-cusp list, and the v4.0.7-j
finite `j`-invariant `hIdentify`.
**Current as of** `v4.0.15-lmfdb-certs-no-doi`
(includes `v4.0.14-coleman-integral-no-doi`, `v4.0.13-formal-immersion-proof-no-doi`, `v4.0.12-scheme-stub-no-doi`, `v4.0.11-residue-disks-no-doi`, `v4.0.10-chabauty0-no-doi`, `v4.0.9-fourCusps-forall`, `v4.0.8-geom-forbid`, `v4.0.7-hIdentify-j`, `v4.0.7-hIdentify`, `v4.0.6-rank-zero-fixed`,
`v4.0.5-nofrey-point`).

| File | What it is | What it is not |
|---|---|---|
| `LevelLowering_26.lean` | Indexed `(ℓ, N, p, M)` certificate; `vₚ(26 p) = 1` from `p ∤ 26` | Not a Ribet, modularity, or Galois-representation theorem |
| `RibetLoweringActual_26.lean` | Displayed Frey model with `loweredLevel = 26` and `Δ ≠ 0`; `ofBealFreyLowering` inhabits `ExistsFreyWitness` | Not a Mathlib Ribet theorem; not a modular-curve point |
| `NoFreyPointActual_26.lean` | Four-cusp *list* `[1,2,13,26]` from `X0_26_RationalPoints26.of_qExpansion` | Not Ribet existence; not `¬` elliptic-`j` `ExistsNoncuspidal`; not a modular-curve rational-point theorem |
| `HIdentifyActual_26.lean` | `hIdentify` / `HIdentify26.of_qExpansion` packs a Frey `j` as `ellipticJ` | Not a Mathlib `X₀(26)` point; not `BealTheorem` |

[`LevelLowering_26.lean`](LevelLowering_26.lean) is a **structure**, not
an opaque `Prop`. It is indexed by residual prime `ℓ`, source/target
levels, and the exact-divide step `M * p = N` with `vₚ(N) = 1`. It
proves `vₚ(26 p) = 1` from `p ∤ 26` and the factorization `26 = 2 * 13`.

`RibetTheoremBoundary26` is explicit. This folder does not construct a
residual Galois representation, a Hecke algebra, or a realizing
newform, and it does not replace the parent
`LevelLowering_26` supplier. Typed `hIdentify` is the finite
`j`-packing. v4.0.8 records typed `hGeomForbid` as uninhabitable
in [`../Mazur/HGeomForbidActual_26.lean`](../Mazur/HGeomForbidActual_26.lean).
v4.0.9 retypes four cusps as a forall over cusp-labeled points;
typed `hGeomForbid` stays uninhabitable. v4.0.10-chabauty0-no-doi
keeps this `j`-packing and does not inhabit a residual
representation as a vacuous proposition.
The remaining geometric gate is a Mathlib noncuspidal `X₀(26)` point.
