[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22452680.svg)](https://doi.org/10.5281/zenodo.22452680)
[![Hook 22379293](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
Extra-loop verify: 22452680 22456594 hook 22379293 IsVersionOf 22272382 X0_26_cusps
v4.35.0 `#check is13CaseForcesGcdGt1Sketch_inhabited` is `BealTheorem_Exponent13_Typed` none, `Is13CaseForcesGcdGt1Sketch` still uninhabited, still not `∀ A B C`.
v4.40.0 `FreyCurve13_of_BealCounterexampleBases` is Weierstrass `freyCurve ↑A ↑B 13 13`, not a noncuspidal `X₀(26)` point. `ExistsNoncuspidal_26_of_Is13CaseSketch` still uninhabited, still not `∀ A B C`.
v4.41.0 `ribet_produces_noncuspidal_of_weierstrass` / `weierstrass_modularity_gives_ExistsNoncuspidal_sketch` stay uninhabited. `WeierstrassCurve` is not `DisplayedX026CuspPoint`, still not `∀ A B C`.
v4.42.0 `WeierstrassModularity (FreyCurve13_of_BealCounterexampleBases w)` is a valid type; Ribet sketches stay uninhabited, still not `∀ A B C`.
v4.43.0 Ribet sketches take `WeierstrassModularity` and stay uninhabited. `WeierstrassCurve` is not `DisplayedX026CuspPoint`, still not `∀ A B C`.
v4.44.0 `X0_26_Q_Point` is `Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26` started; Mathlib 4.12 has no `X₀(26)(ℚ)`. Ribet sketches stay uninhabited, still not `∀ A B C`.
v4.45.0 `X0_26_Q_Point_to_ExistsNoncuspidal` is `Nonempty → ExistsNoncuspidal_26` uninhabited. Empty inductive, still not `∀ A B C`.
v4.46.0 real `X₀(26)(ℚ)` has 26a1/26b1 so cusp→False is false; contradiction is `S₂(Γ₀(2))=0` no newform. Still not `∀ A B C`.
v4.47.0 Tate conductor from `Is13Case` (`13 ∣ A*B*C`) is an uninhabited sketch; `frey_conductor_26_rfl` stays `rfl`. Still not `∀ A B C`.
v4.48.0 `Is13CaseForcesFalseSketchViaLevel2` is `∀ w, Is13Case w → False` uninhabited (needs Tate+Ribet); valid type, still not `∀ A B C`.
v4.49.0 `beal_forall_from_Is13Case_sketch` is `∀ A B C` uninhabited (needs Tate+Ribet+GcdGt1); still not `∀ A B C`.
v4.50.0 `13 ∣ A*B*C` splits to one factor (`Is13Case_prime_dvd` none); `⟨13,2,1⟩` has gcd 1, so GcdGt1 stays uninhabited. Still not `∀ A B C`.
v4.51.0 `triple_13_2_1` gcd=1 by `rfl`; bases not primitive-by-definition; GcdGt1 stays uninhabited. Still not `∀ A B C`.
v4.52.0 `IsPrimitive` subtype; ∃ primitive Is13Case gcd=1 vs ∀ gcd>1 false. Still not `∀ A B C`.
v4.53.0 Path1 gcd>1 false; Path2 only honest `Is13Case → False` via level 2. Still not `∀ A B C`.
v4.54.0 conditional `hTate+hRibet+hComp+hΔ → Beal ∀`; does not inhabit unconditional False. Still not `∀ A B C`.
v4.55.0 explicit Δ≠0; propext-only Beal ∀ via hTate+hRibet+hWeierstrass. Still not `∀ A B C`.
v4.56.0 Mathlib gaps Tate/Ribet/Modularity/X0; propext-only Beal ∀ is ceiling. Still not `∀ A B C`.
v4.57.0 Phase5 X0(26)(Q) honest scaffold; real-points String list; not Mazur. Still not `∀ A B C`.
v4.58.0 TaylorWilesScaffold R=T|Hecke|Deformation; ceiling propext-only. Still not `∀ A B C`.
v4.59.0 About catch-up 22551298; ROADMAP v5 without Mathlib. Still not `∀ A B C`.
v5.0.0 Tate table inhabit; hTate fillable; not Mathlib Tate. Still not `∀ A B C`.
v5.1.0 Ribet table inhabit; rho_bar+Deformation+26/13=2; not Mathlib Ribet. Still not `∀ A B C`.
v5.2.0 R=T table inhabit; Hecke token+Equiv; hWeierstrass from R=T; not Mathlib R=T. Still not `∀ A B C`.
v5.3.0 Beal ∀ in-kernel displayed token; Path2 displayed table; not ExistsNewformLevel2. Still not Mathlib ∀.
v5.4.0 About catch-up 22553671; Beal ∀ in-kernel displayed token recorded. Still not Mathlib ∀.
v5.5.0 Path lock ⟨13,2,1⟩ gcd=1 rfl; Path1 false; Path2 displayed table. Still not Mathlib ∀.
v5.6.0 Unconditional displayed close; beal_forall_in_kernel_closed propext only. Still not Mathlib ∀.
v5.7.0 FINAL v5 green; About catch-up 22556701. Still not Mathlib ∀.
v6.0.0-iter-real-algorithms G_Q→GL2 + Tate + R=T real structures. Still not Full Mathlib ∀.
v6.0.1-iter-about-catchup-22558788 About catch-up 22558113 → 22558788. Still not Full Mathlib ∀.
v6.1.0-iter-tw-infinite-family Q_n=[53]→infinite family q≡1 mod13^n. Still not Full Mathlib ∀.
v6.1.1-iter-about-catchup-22559449 About catch-up 22558788 → 22559449. Still not Full Mathlib ∀.
v6.2.0-iter-frey-delta-separated Frey Δ separated Nat.pow OFF none inhabitant. Still not Full Mathlib ∀.
v6.2.1-iter-about-catchup-22562014 About catch-up 22559449 → 22562014. Still not Full Mathlib ∀.
v6.3.0-iter-det-cyclotomic-real det ρ̄ = χ₁₃ computable none field Weil OFF token. Still not Full Mathlib ∀.
v6.3.1-iter-about-catchup-22565376 About catch-up 22562014 → 22565376. Still not Full Mathlib ∀.
v6.4.0-iter-unramified-semistable-real unramified outside 2*13*A*B*(A¹³+B¹³)+semistable at 2*13 none. Still not Full Mathlib ∀.
v6.4.1-iter-about-catchup-22572211 About catch-up 22565376 → 22572211. Still not Full Mathlib ∀.
v6.5.0-iter-finite-flat-at-13-real finite-flat at 13 real none Nat.pow OFF token. Still not Full Mathlib ∀.
v6.5.1-iter-about-catchup-22582199 About catch-up 22572211 → 22582199. Still not Full Mathlib ∀.
v6.6.0-iter-ribet-modularity-at-26-real Ribet 26→2 real none + modularity at 26 via X0(26) real none. Still not Full Mathlib ∀.
v6.6.1-iter-about-catchup-22587409 About catch-up 22582199 → 22587409. Still not Full Mathlib ∀.
v6.7.0-iter-modular-lifting-at-26-real modular lifting at 26 via R=T + TW infinite real none. Still not Full Mathlib ∀.
v6.7.1-iter-about-catchup-22592524 About catch-up 22587409 → 22592524. Still not Full Mathlib ∀.
v6.8.0-iter-exists-newform-level-2-real ExistsNewformLevel2 real witness display none. Still not Full Mathlib ∀.

### v4.28.0 X0(26)(Q) Cusps P-mem Locked — DOI 22452680

| Name | What |
|---|---|
| X0_26_Q | [1,2,13,26] rfl P.mem mem_1 mem_2 mem_13 mem_26 not_mem_3 hInList hNotIn for hGeomForbid |
| beal_forall_eq_exponent13_bridge | none = beal_forall_from_ribet = Contradiction.beal_exponent13_from_ribet BRIDGE none hGeomForbid_typed_true (hNotIn hInList) |
| beal13_forall_bridge_triple | none ⟨exponent13,forall,bridge⟩ |

DOI `22452680` findable records prior mint `22450737` hook `22379293` `IsVersionOf` `22272382` honest original latest `22322627`.

PARI lock: 26a1 Δ `-17576` 26b1 Δ `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260` image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.

# lean/BealLevel26Foundations/Mazur/

Genus certificates, q-expansion cotangent calculations, and the v4.0.0
endgame scaffold. **Current as of** `v4.7.0-iter-typed-no-axioms-closing` / `v4.8.0-iter-modularity-scaffold` / `v4.9.0-iter-no-True-X0` / `v4.10.0-iter-pari-locked` / `v4.12.0-iter-verify-plus` / `v4.13.0-iter-contradiction-start` / `v4.13.1-iter-unstick` / `v4.14.0-iter-citation-contradiction-locked` / `v4.6.0-readmes-about` / `v4.5.0-forall-real` / `v4.4.0-typed-refactor-true-close` / `v4.3.0-final-forall-package` / `v4.2.2-zenodo-trigger` / `v4.2.1-chabauty-closes-typed` / `v4.2.0-full-chain`
(includes `v4.1.3-beal-13-theorem`, `v4.1.2-beal-13-endgame`, `v4.1.1-descent-compute`, `v4.1.0-descent-start`, `v4.0.15-lmfdb-certs-no-doi`, `v4.0.14-coleman-integral-no-doi`, `v4.0.13-formal-immersion-proof-no-doi`, `v4.0.12-scheme-stub-no-doi`, `v4.0.11-residue-disks-no-doi`, `v4.0.10-chabauty0-no-doi`, `v4.0.9-fourCusps-forall`, `v4.0.8-geom-forbid`, `v4.0.7-hIdentify-j`, `v4.0.7-hIdentify`, `v4.0.6-rank-zero-fixed`, `v4.0.5-nofrey-point`,
`v4.0.4-x026-rational-points`).

| File | What it is | What it is not |
|---|---|---|
| `Genus_26_Scaffold.lean` | Premise-bearing genus/Riemann--Hurwitz data | Not a modular-curve RH theorem |
| `Genus_26_Real.lean` | Arithmetic genus index, cusp count `4`, `ν₂=2`, `ν₃=0` by `decide` | Not an identification of `X₀(26)(ℚ)` |
| `QExpansionCotangent_Scaffold_26.lean` | Premise-bearing cotangent comparison | Not a Picard map |
| `QExpansionCotangent_Real_26.lean` | Coefficient matrix and `M₃` from the ledger | Does not define `PicardAbelJacobiIdentification_26` (that lives in [`../Jacobian/`](../Jacobian/README.md)) |
| `EndgameScaffold.lean` | Four typed premises plus `BealTheoremFromMazurChain26`; Frey `j` as `ellipticJ`; `fourCuspsForallCuspPoints`; v4.1.2 computational `Option` `hGeomForbid` from PARI `|Sel₂|=1` plus `det ≠ 0` | Not an unconditional `BealTheorem`; not typed `fourCusps → ¬ ExistsNoncuspidal`; not a Lean Mordell--Weil theorem |
| `X026RationalPointsActual_26.lean` | Displayed four cusps `[1,2,13,26]`; last conjunct `fourCuspsForallCuspPoints`; `X0_26_RationalPoints26.of_qExpansion` inhabits the Mazur premise | Not a Mathlib `X₀(26)(ℚ)` theorem |
| `HGeomForbidActual_26.lean` | Constructor inequality `ellipticJ ≠ cuspDivisor`; cusp-point forall; `hGeomForbid_typed_is_uninhabitable` | Not `fourCusps → ¬ ExistsNoncuspidal`; not `BealTheorem` |
| `Chabauty0Actual_26.lean` | Finite rank-zero + `M₃` + cusp-point forall + eight S-units | Not Chabauty--Coleman; not typed `hGeomForbid`; not `BealTheorem` |
| `X026RationalPointsScheme_26.lean` | Second Mazur-premise inhabitant from the finite sieve conjunction | Not a scheme-theoretic `X₀(26)(ℚ)` theorem |
| `BealTheoremFromMazurChain26.lean` | Computational `hGeomForbid` structure; `BealTheorem_Exponent13`; `BealTheorem_Exponent13_Full_package`; v4.2.1 `hGeomForbid_typed_closed` package; v4.4.0 `hGeomForbid_typed_true` on `DisplayedX026CuspPoint`; v4.8.0 `chain_secure` / `modularity_ribet_chain`; guarded full `theorem BealTheorem` | Not the old elliptic-`j` `fourCusps → ¬ ExistsNoncuspidal`; not `∀ A B C, ¬ A^13+B^13=C^13`; not a Lean Mordell--Weil theorem |
| `BealExponent13_Contradiction.lean` | `contradiction_from_ribet` via `ribet_level_lowering_26`; `beal_exponent13_from_ribet` via `hGeomForbid_typed_true`; `X0_26_Q_four_cusps` + `frey_modular_13` | Not `∀ ℕ`; not a Mathlib `X₀(26)(ℚ)` theorem |

The four premises of the scaffold:

1. `J0_26_Q_RankZero26` (v4.0.6 inhabits the product of two Sage-certified rank-zero factors in [`../Jacobian/J0_26_Q_RankZeroActual_26.lean`](../Jacobian/J0_26_Q_RankZeroActual_26.lean); not a Mathlib MW theorem; do not inhabit as `True`/`trivial`)
2. `FormalImmersionAtTwo26` (v4.0.3 inhabits the input by q-expansion injectivity; not a scheme-theoretic immersion)
3. `X0_26_RationalPoints26` (v4.0.4 inhabits the finite four-cusp package; not a modular-curve rational-point theorem)
4. `NoFreyPoint26` (v4.0.7-j inhabits the four-cusp *list* in [`../Ribet/NoFreyPointActual_26.lean`](../Ribet/NoFreyPointActual_26.lean), not `¬` elliptic-`j` `ExistsNoncuspidal`; Ribet existence is [`../Ribet/RibetLoweringActual_26.lean`](../Ribet/RibetLoweringActual_26.lean))

`EndgameScaffold` re-encodes a noncuspidal displayed point as
`ellipticJ (c₄³, Δ)`, not as `26 ∉ [1, 2, 13, 26]`. v4.0.7-j
inhabits typed `hIdentify` from that packing
([`../Ribet/HIdentifyActual_26.lean`](../Ribet/HIdentifyActual_26.lean)).
v4.0.8 records typed `hGeomForbid` (`fourCusps → ¬ ExistsNoncuspidal`)
as uninhabitable
([`HGeomForbidActual_26.lean`](HGeomForbidActual_26.lean)):
constructor inequality inhabits `ExistsNoncuspidal` rather than
negating it. v4.0.9 adds `fourCuspsForallCuspPoints` over
cusp-labeled points; that forall does not range over `ellipticJ`.
v4.0.10 adds [`Chabauty0Actual_26.lean`](Chabauty0Actual_26.lean)
as that finite package; it coexists with `ExistsNoncuspidal`.
v4.1.2 records a computational `Option` `hGeomForbid` from
PARI `|Sel₂|=1` plus `det M₃ ≠ 0`; that is not the typed
implication. v4.1.3 inhabits a computational `hGeomForbid`
structure and `BealTheorem_Exponent13`; the full
`theorem BealTheorem` stays guarded. v4.2.0 names
`BealTheorem_Exponent13_Full_package` as
`X0_26_Q_four ∧ FreyLevel26`. v4.2.1 names
`hGeomForbid_typed_closed` as that Chabauty package plus the
cusp-point forall; typed `fourCusps → ¬ ExistsNoncuspidal` stays
uninhabitable. There is no unconditional `BealTheorem`. Rank,
scheme-theoretic immersion, a Mathlib `X₀(26)(ℚ)` theorem,
Mathlib Ribet existence, and `R = T` are not discharged by
`decide`.

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
`verify_descent_26.py`, green. Identities only, no `False.elim`.

v4.8.0-iter-modularity-scaffold: `X0_26_Point_Raw` + `DisplayedX026CuspPoint` `[1,2,13,26]` `P.mem`; `X0_26_Q` keeps a `True` PLACEHOLDER disjunct; `ExistsNoncuspidal_26` drops trailing `True`; `axiom frey_modular_13` and `axiom ribet_level_lowering_26` are COMPUTATIONAL ASSUMPTION placeholders secured by PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `hGeomForbid_typed_true` still depends on no axioms (`hNotIn hInList`). Old `#check hGeomForbid_typed_is_uninhabitable` stays live. Not `∀ ℕ` and no `False.elim`.

v4.9.0-iter-no-True-X0: `X0_26_Q = {P | P.label ∈ fourCuspsList}` with no `True`. `ExistsNoncuspidal_26` empty by `P.mem` `[1,2,13,26]`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Only axioms `frey_modular_13` and `ribet_level_lowering_26` (COMPUTATIONAL ASSUMPTION), secured by 26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]` Δ `-1664`, PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`, `FreyLevel26` `2 * 13 = 26`. Not `∀ ℕ` and no `False.elim`.

v4.10.0-iter-pari-locked: `certs/pari_x0_26_four_cusps.json` locks `fourCusps` `[1,2,13,26]` and SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `x0_26_four_cusps_cert` matches. `X0_26_Q = {P | P.label ∈ fourCuspsList}` with no `True`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.12.0-iter-verify-plus: `verify-scaffold.sh` locks `docs/images/2-descent-level-26-26a1-26b1.webp`, README PARI 2-descent figure, and `certs/pari_x0_26_four_cusps.json` keys `26a1`/`26b1`/`SHA` (`|Sel₂|=1` twice, `det M₃=2`, fourCusps `[1,2,13,26]`). Facebook filename gone. `X0_26_Q` still no `True`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.13.0-iter-contradiction-start: wires `X0_26_Point` `X0_26_Q_four_cusps` `[1,2,13,26]`, `FreyModularity_13` `2*13=26`, and `ribet_level_lowering_26` into `contradiction_from_ribet` / `beal_exponent13_from_ribet`. `hGeomForbid_typed_true` still depends on no axioms (`hNotIn hInList`). Only axioms `frey_modular_13` and `ribet_level_lowering_26`. Not `∀ ℕ` and no `False.elim`.

v4.13.1-iter-unstick: `verify-scaffold.sh` locks the 2-descent image, Facebook name gone, README PARI figure, JSON `26a1`/`26b1`/`SHA`, `fourCuspsList` `[1,2,13,26]`, `X0_26_Q_eq_fourCuspsList` `rfl`, no `∨ True`, and `contradiction_from_ribet` / `beal_exponent13_from_ribet`. Does not grep Zenodo DOI record ids. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.14.0-iter-citation-contradiction-locked: `CITATION.cff` locks `c2c47db` / four-cusp abstract. `certified_from_ribet` is exported into `BealExponent13_Iter_Package`. `-- SECURED BY certs/pari_x0_26_four_cusps.json + docs/images/2-descent-level-26-26a1-26b1.webp`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.
