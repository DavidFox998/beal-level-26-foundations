[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22452680.svg)](https://doi.org/10.5281/zenodo.22452680)
[![Hook 22379293](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)

### v4.28.0 X0(26)(Q) Cusps P-mem Locked — DOI 22452680

| Name | What |
|---|---|
| X0_26_Q | [1,2,13,26] rfl P.mem mem_1 mem_2 mem_13 mem_26 not_mem_3 hInList hNotIn for hGeomForbid |
| beal_forall_eq_exponent13_bridge | none = beal_forall_from_ribet = Contradiction.beal_exponent13_from_ribet BRIDGE none hGeomForbid_typed_true (hNotIn hInList) |
| beal13_forall_bridge_triple | none ⟨exponent13,forall,bridge⟩ |

DOI `22452680` findable records prior mint `22450737` hook `22379293` `IsVersionOf` `22272382` honest original latest `22322627`.

PARI lock: 26a1 Δ `-17576` 26b1 Δ `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260` image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.

# lean/BealLevel26Foundations/Frey/

Frey-conductor *data* and the v2 odd-prime valuation input. **Current
as of** `v4.2.0-full-chain` / `v2.0.0-frey`.

| File | What it is | What it is not |
|---|---|---|
| `FreyConductorData_26.lean` | Supplied conductor fields for scaffold theorems | Not Tate's algorithm |
| `FreyConductorUnconditional_26.lean` | Re-export of the valuation input | Not `frey_conductor_data` |
| `Conductor_26_Unconditional.lean` | `vₚ(c₄)=0` and `vₚ(Δ)>0` from `p ∤ c₄`, `p ∣ Δ`, `Δ ≠ 0` | Not Kodaira type `I_n` or `N = 2^e rad(ABC)` |

`TateKodairaBoundary26` is an explicit named boundary. These files must
not mention `frey_conductor_data` or `tate_step2_odd_prime_external`.
The Weierstrass model itself is
[`../Real/FreyWeierstrass.lean`](../Real/FreyWeierstrass.lean).
The v4.2.0 displayed level name `FreyLevel26` (`2 * 13 = 26`) lives in
[`../Chain/FreyCurve_13_26.lean`](../Chain/FreyCurve_13_26.lean).
That is not Ribet level lowering.
