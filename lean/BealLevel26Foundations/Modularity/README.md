# v4.8.0 Iter modularity scaffold

Explicit Wiles--Taylor / Ribet *names*. **Current as of**
`v4.8.0-iter-modularity-scaffold`.

These files are computational-assumption placeholders. They are
not Mathlib modularity and not a Lean Ribet theorem.

| File | What it is | What it is not |
|---|---|---|
| `FreyModularity_13.lean` | `FreyCurve13` displayed triple; empty `Modularity` inductive; `axiom frey_modular_13`; `frey_conductor_26 = 26`; `freyLevel26_computational` is `2 * 13 = 26` | Not Wiles--Taylor; not a Frey Weierstrass model |
| `RibetLevelLowering_26.lean` | `axiom ribet_level_lowering_26`; `ribet_secured_by_certs` lists PARI `\|Sel₂\|=1` twice, `det M₃=2`, SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260` | Not Ribet; not a modular-curve point |

The only axioms in the tree are `frey_modular_13` and
`ribet_level_lowering_26`, each marked
`COMPUTATIONAL ASSUMPTION`. Mazur imports both plus
`Chain/X0_26_Point.lean` (`X0_26_Point_Raw`,
`DisplayedX026CuspPoint` with `P.mem`, `X0_26_Q` the
four-label set with no `True`).

`hGeomForbid_typed_true` stays axiom-free (`hNotIn hInList`).
`ExistsNoncuspidal_26` is empty by type. Old
`#check hGeomForbid_typed_is_uninhabitable` stays live.

Certs: 26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]`
Δ `-1664`. Not `∀ ℕ` and no `False.elim`.
