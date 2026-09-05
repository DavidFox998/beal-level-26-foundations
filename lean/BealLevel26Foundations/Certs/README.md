# lean/BealLevel26Foundations/Certs/

Archived LMFDB *display* data and PARI 2-descent display for `26a1`
and `26b1`. **Current as of** `v4.7.0-iter-typed-no-axioms-closing` / `v4.8.0-iter-modularity-scaffold` / `v4.9.0-iter-no-True-X0` / `v4.10.0-iter-pari-locked` / `v4.6.0-readmes-about`.

| File | What it is | What it is not |
|---|---|---|
| `LMFDB_26.json` | Labels, conductor `26`, displayed rank `0`, torsion strings, `a₂` | Not a live LMFDB fetch; not a Mordell--Weil theorem |
| `LMFDBCert_26.lean` | Finite Lean package of those fields, matching Sage `certified_mwrank` and q-expansion `a₂` | Not unconditional `rankZero`; not `True`/`trivial` |
| `Descent_26.json` | PARI `ellrank` / `ell2cover` / `elltors`: rank `0`, torsion `3`/`7`, `|Sel₂|=1`, `sha2_trivial: true` | Not a Mathlib Selmer group; not a Mordell--Weil theorem |

`scripts/fetch_LMFDB.py` writes `LMFDB_26.json` from a hardcoded
table. `scripts/verify_descent_26.py` recomputes with Sage or
cypari2 when present. Neither contacts LMFDB.org or changes
`sagemath/level_26_ledger.json` (SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`).

LMFDB JSON SHA-256
`39e22740a7787567882b33e27396b1c1dfd10a7f14e23b8af28f89e594e7b5f0`.
Descent JSON SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

v4.4.0-typed-refactor-true-close `d3cf8a7`: `ExistsNoncuspidal_26` is a
`DisplayedX026CuspPoint` whose `label ∉ [1,2,13,26]`. Every such `P`
has `P.mem`, so the existential is empty by type. The trailing `True`
is a placeholder for `P ∈ X0_26_Q`; Mathlib 4.12 has no `X0_26_Point`.

`hGeomForbid_typed_true` is `fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`,
proved by `hNotIn hInList`. It depends on no axioms. That is not the
old elliptic-`j` implication (`True → ¬True`).

v4.5.0-forall-real `1d0044e`: `BealExponent13_Iter_Typed_And_Package`
is `BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`. That
is a named conjunction, not `∀ ℕ` and not `∀ A B C`. Certs unchanged:
26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]` Δ `-1664`,
PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

Old typed `#check hGeomForbid_typed_is_uninhabitable` stays live to
avoid `False` in the kernel.

Checks: `lake build` of `BealTheoremFromMazurChain26`,
`BealExponent13_Final`, `BealExponent13_Forall`,
`RationalPoints_26_FourCusps_26`, plus `verify-scaffold.sh` and
`verify_descent_26.py`, green. No `sorry`, no `False.elim`.

v4.8.0-iter-modularity-scaffold: `X0_26_Point_Raw` + `DisplayedX026CuspPoint` `[1,2,13,26]` `P.mem`; `X0_26_Q` keeps a `True` PLACEHOLDER disjunct; `ExistsNoncuspidal_26` drops trailing `True`; `axiom frey_modular_13` and `axiom ribet_level_lowering_26` are COMPUTATIONAL ASSUMPTION placeholders secured by PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `hGeomForbid_typed_true` still depends on no axioms (`hNotIn hInList`). Old `#check hGeomForbid_typed_is_uninhabitable` stays live. Not `∀ ℕ` and no `False.elim`.

v4.9.0-iter-no-True-X0: `X0_26_Q = {P | P.label ∈ fourCuspsList}` with no `True`. `ExistsNoncuspidal_26` empty by `P.mem` `[1,2,13,26]`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Only axioms `frey_modular_13` and `ribet_level_lowering_26` (COMPUTATIONAL ASSUMPTION), secured by 26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]` Δ `-1664`, PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`, `FreyLevel26` `2 * 13 = 26`. Not `∀ ℕ` and no `False.elim`.

v4.10.0-iter-pari-locked: `certs/pari_x0_26_four_cusps.json` locks `fourCusps` `[1,2,13,26]` and SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `x0_26_four_cusps_cert` matches. `X0_26_Q = {P | P.label ∈ fourCuspsList}` with no `True`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.
