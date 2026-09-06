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

# v4.27.0 X₀(26) Four Cusps — `P.mem` Lock

Displayed stand-in in
`lean/BealLevel26Foundations/Chain/X0_26_Point.lean`.
This is **not** a Mathlib `X₀(26)(ℚ)` theorem. The carrier is
`X0_26_Point_Raw`. `X0_26_Q` is a `Set` of those points;
`X0_26_cusps` is the label list `[1,2,13,26]`.

| Name | What it is |
|---|---|
| `X0_26_cusps` | `[1,2,13,26]` — four displayed cusp labels |
| `X0_26_Q` | `{P \| P.label ∈ fourCuspsList}` — no `True` disjunct |
| `X0_26_Q_eq_cusps` | `X0_26_Q = {P \| P.label ∈ X0_26_cusps}` (`rfl`) |
| `X0_26_Q_eq_fourCuspsList` | same set, named on `fourCuspsList` (`rfl`) |
| `mem_1` / `mem_2` / `mem_13` / `mem_26` | `1,2,13,26 ∈ X0_26_cusps` (`decide`) |
| `not_mem_3` | `3 ∉ X0_26_cusps` (`decide`) |
| `hInList_X0_26` | `∀ x ∈ X0_26_Q, x.label ∈ [1,2,13,26]` |
| `hNotIn_X0_26` | `∀ x ∉ X0_26_Q, x.label ∉ [1,2,13,26]` |
| `hInList_label` / `hNotIn_label` | label form used by `hGeomForbid_typed_true` |
| `displayed_mem_cusps` | `P.mem` : `P.label ∈ X0_26_cusps` |
| `ExistsNoncuspidal_26` | empty by `P.mem` versus `P.label ∉ fourCuspsList` |

`hGeomForbid_typed_true` in Mazur uses `displayed_mem_cusps`,
`hInList_label`, and `hNotIn_label` (`hNotIn hInList`). That
close is axiom-free. Still not `∀ A B C : ℕ`.

PARI lock: 26a1 Δ `-17576`, 26b1 Δ `-1664`, `|Sel2|=1`,
det `M3=2`, SHA
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`,
image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.
Mint `10.5281/zenodo.22450737` findable on parallel parent
`22379293`. Honest: hook did not retarget `22272382`.
