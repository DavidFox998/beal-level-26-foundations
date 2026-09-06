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
Mint `10.5281/zenodo.22448176` findable on parallel parent
`22379293`. Honest: hook did not retarget `22272382`.
