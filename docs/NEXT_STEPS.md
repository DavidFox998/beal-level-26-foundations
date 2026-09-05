# Next steps (not a close)

We do not use the word final until `∀ A B C : ℕ` is in the
kernel without `False.elim`.

## v4.8.0 Iter modularity scaffold

Typed true close `d3cf8a7` plus forall-real `1d0044e` plus
v4.6.0 ingest plus v4.7.0 Iter rename.  Current names:

* `BealExponent13_Iter_Package` =
  `X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`
* `BealExponent13_Iter_Typed_And_Package` =
  `BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`

`hGeomForbid_typed_true` depends on no axioms via `hNotIn hInList`
on `DisplayedX026CuspPoint` `[1,2,13,26]` (`P.mem`).
`ExistsNoncuspidal_26` is empty by type (no trailing `True`).
Old `#check hGeomForbid_typed_is_uninhabitable` stays live.

New explicit layer:

* `X0_26_Q` on `X0_26_Point_Raw` still has a `True`
  PLACEHOLDER disjunct (Mathlib 4.12 has no modular-curve
  `ℚ`-points; replace later by PARI + Chabauty cert)
* `axiom frey_modular_13` — COMPUTATIONAL ASSUMPTION,
  Wiles/Taylor not in Mathlib, secured by LMFDB 26a1/26b1
* `axiom ribet_level_lowering_26` — PLACEHOLDER AXIOM,
  secured by PARI `|Sel₂|=1` + `det M₃=2`
* Mazur chain uses those two axioms plus
  `freyLevel26_computational` plus axiom-free
  `hGeomForbid_typed_true`

Zenodo GitHub hook is ON (account-holder toggle).  Waiting for a
version mint beyond `10.5281/zenodo.22322627` (`v4.0.9`).  Do not
invent a DOI.

Certs unchanged: 26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1
`[1,-1,1,-3,3]` Δ `-1664`, PARI `|Sel₂|=1` twice, `det M₃=2`,
SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`,
`FreyLevel26` `2 * 13 = 26`.

## v4.9.0 (not started)

`BealExponent13_Contradiction` would be the implication
`(A^13+B^13=C^13 coprime) → ExistsNoncuspidal_26` as a
placeholder, then `False` via `hGeomForbid_typed_true`.  That
would still be computational: `P ∈ X0_26_Q` is the `True`
disjunct on the displayed set.  Mathlib 4.12 has no scheme
`X0_26_Point` and no Ribet (the two axioms remain assumptions).
Do not inhabit `∀ A B C : ℕ` by `False.elim`.
