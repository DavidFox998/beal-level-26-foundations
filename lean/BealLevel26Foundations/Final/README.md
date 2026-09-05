# v4.6.0 READMEs / About (typed no axioms)

**Current as of** `v4.6.0-readmes-about`.

This folder names the exponent-13 conjunction. It is not
`∀ A B C, ¬ A^13 + B^13 = C^13`.

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
`BealTheorem_Exponent13_Forall_Computational` is
`BealTheorem_Exponent13_Typed ∧ BealExponent13_Final_Package`
(not `∀ A B C`).
`BealExponent13_Final_Package = X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`,
`BealExponent13_Final_Package.certified`.
`BealTheorem_Exponent13_Full_package` is the same conjunction
in Mazur (Final imports Mazur). No `∀` with vacuous contradiction.

v4.4.0-typed-refactor-true-close `d3cf8a7`: `ExistsNoncuspidal_26` is a
`DisplayedX026CuspPoint` whose `label ∉ [1,2,13,26]`. Every such `P`
has `P.mem`, so the existential is empty by type. The trailing `True`
is a placeholder for `P ∈ X0_26_Q`; Mathlib 4.12 has no `X0_26_Point`.

`hGeomForbid_typed_true` is `fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`,
proved by `hNotIn hInList`. It depends on no axioms. That is not the
old elliptic-`j` implication (`True → ¬True`).

v4.5.0-forall-real `1d0044e`: `BealTheorem_Exponent13_Forall_Computational`
is `BealTheorem_Exponent13_Typed ∧ BealExponent13_Final_Package`. That
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

Releases: `v4.2.0-full-chain` `62d0e13`,
`v4.2.1-chabauty-closes-typed` `eed5170`,
`v4.2.2-zenodo-trigger` fresh, `v4.3.0-final-forall-package`,
`v4.4.0-typed-refactor-true-close` `d3cf8a7`, `v4.5.0-forall-real`
`1d0044e`, `v4.6.0-readmes-about`.
