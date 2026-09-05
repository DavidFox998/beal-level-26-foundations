# Next steps (not a close)

We do not use the word final until `∀ A B C : ℕ` is in the
kernel without `False.elim`.

Prior: v4.8.0-iter-modularity-scaffold named the two
computational-assumption axioms. v4.9.0-iter-no-True-X0
set `X0_26_Q` to the four-label set with no True.

## v4.10.0 Iter PARI locked

`X0_26_Q = {P | P.label ∈ fourCuspsList}` — no True.
`x0_26_four_cusps_cert = [1,2,13,26]` matches
`certs/pari_x0_26_four_cusps.json`.
`verify-scaffold.sh` cats that JSON and checks SHA +
`fourCuspsList`. `verify_descent_26.py` still checks
SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

`ExistsNoncuspidal_26` empty by `P.mem`.
`hGeomForbid_typed_true` no axioms (`hNotIn hInList`).
Only axioms: `frey_modular_13` and `ribet_level_lowering_26`,
both COMPUTATIONAL ASSUMPTION, secured by 26a1
`[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]` Δ `-1664`,
PARI `|Sel₂|=1` twice, `det M₃=2`, `FreyLevel26` `2 * 13 = 26`.

Zenodo GitHub hook is ON.  Waiting for a version mint beyond
`10.5281/zenodo.22322627` (`v4.0.9`).  Do not invent a DOI.

## v4.12.0 Iter verify plus

`verify-scaffold.sh` locks
`docs/images/2-descent-level-26-26a1-26b1.webp`,
README `PARI 2-Descent Certificates — X0(26) Four Cusps`,
and `certs/pari_x0_26_four_cusps.json` keys `26a1` /
`26b1` / `SHA`. Facebook upload name gone. Certs unchanged:
26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]` Δ
`-1664`, `|Sel₂|=1` twice, `det M₃=2`, SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

## v4.11.0 (not started)

`BealExponent13_Contradiction` would be
`(A^13+B^13=C^13 coprime) → ExistsNoncuspidal_26` as a
placeholder, then `False` via `hGeomForbid_typed_true`.
Still computational: the carrier is `X0_26_Point_Raw`, not
a Mathlib modular-curve point, and the two axioms remain
assumptions. Do not inhabit `∀ A B C : ℕ` by `False.elim`.
