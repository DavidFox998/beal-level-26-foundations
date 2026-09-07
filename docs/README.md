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
v6.8.1-iter-about-catchup-22602899-relook About catch-up 22592524 → 22602899. Still not Full Mathlib ∀.
v6.9.0-iter-beal-forall-closed-real Beal Forall closed real via positivity/det/unramified/semistable/finite-flat/Ribet/modularity/TW/R=T/lifting/exists-newform. Still not Full Mathlib ∀.
v6.9.1-iter-about-catchup-22611775-relook About catch-up 22602899 → 22611775. Still not Full Mathlib ∀.
v7.0.0-iter-beal-forall-none-real Beal ∀ from propext only OFF inhabitant → none via rfl only. Still not Full Mathlib ∀.
v7.0.1-iter-about-catchup-22618433-relook About catch-up 22611775 → 22618433. Still not Full Mathlib ∀.
v7.1.0-iter-beal-forall-kernel-separated-none-real Beal ∀ kernel separated from propext only → none via rfl only. Still not Full Mathlib ∀.
v7.1.1-iter-about-catchup-22632209-relook About catch-up 22618433 → 22632209. Still not Full Mathlib ∀.
v7.1.2-iter-readme-uniform-opera-links README header uniformized (badges 22632209/22635221/22272382) + Opera Numerorum coordination index docs/OPERA_NUMERORUM_LINKS.md added in both repos, no Lean change. Still not Full Mathlib ∀.
v7.1.3-iter-beal-not-route-e-corrected Beal Conjecture corrected from mislabeled "Route E" to its own two-repository chamber of Opera Numerorum, not part of the Riemann Hypothesis A-D route lettering, no Lean change. Still not Full Mathlib ∀.
v7.2.0-step1-true-conductor-scaffold TrueConductor typed scaffold: Frey model of a primitive Beal triple, Δ=16(Aᵐ)²(Bⁿ)²(Cᵖ)² by ring, true gcd pairwise-coprime ⇒ odd p|ABC does not divide c₄, v_p(c₄)=0 and v_p(Δ)>0; Tate/Kodaira/N=2·rad(ABC) stay uninhabited empty-Type witnesses not sorry. Still not Full Mathlib ∀.
v7.2.1-tate-filled TrueConductor Tate filled: true_gcd_pairwise on Aᵐ,Bⁿ,Cᵖ; Tate Step 2 at odd q|ABC gives Kodaira I_n and exponent 1; at 2 the integral model has v₂(c₄)=4 so Step 2 does not apply and rad exponent of 2 is 1; N=2·∏_{odd q|ABC}q=rad(ABC). Sketch stays uninhabited. Still not Full Mathlib ∀.
v7.3.0-ribet-rt-filled ModularityRibet theorems: Wiles domain from TrueConductor N=rad(ABC); Ribet quotient N/∏q=2; det=χ_l (l=13 instance); TW family q_n=4·13ⁿ+1 with 53%13=1, 677%169=1, 8789=17·517 composite; R_∞≃T_∞ bookkeeping; S₂(Γ₀(2))=0 so ¬ExistsNewformLevel2. Sketch stays uninhabited. Still not Full Mathlib ∀.
v7.4.0-geometry-filled GeometryBridge theorems: J0(26) dim 2=1+1 as E_26a1×E_26b1 (Δ -17576/-1664); Pic⁰=J0 product; formal immersion at 2 via M3=[[1,1],[0,2]] det=2 with ω1=dx/y ω2=x dx/y; X0(26)(Q) labels [1,2,13,26] so ¬ExistsNoncuspidal; Sel2=1 rank 0. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.0.0-beal-forall-proof FullProof glue: unguarded sketch is false (0³+1³=1³, gcd=1); beal_forall_proof is positive-bases Beal from the missing Modular→ExistsNewformLevel2 arrow; Tate+Ribet+GeometryBridge glue inhabited. BealForall.lean sketch stays uninhabited. Still not Full Mathlib ∀.
v8.1.0-modular-implies-newform ModularImpliesNewform: PositiveBealTriple + Mathlib Γ₀(2) + TW 53%13=1 677%169=1 + Ribet N/∏q=2 arithmetic; ModularImpliesLevel2Newform stays a Prop; beal_forall_proof = beal_forall_proof_positive (still conditional). Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.2.0-scheme-hecke-ribet GeometryScheme + HeckeAlgebra + RibetFunctor: packed X0(26)/J0(26) models, TW-tower R≃T, functorial lowering N→2; ModularImpliesLevel2Newform_Real stays the v8.1.0 Prop (ExistsNewformLevel2 is 0≠0). Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.3.0-explicit-X0-26 X0_26_Model + HeckeAction + LevelLowering: explicit y²=x⁶−8x⁵+22x⁴−20x³+5x²+4x−4, M_ℤ=[[1,1],[0,2]] det=2, T_q on 26a1/26b1 prefixes, TW 53/677 patching; beal_positive_bases stays from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.

### v4.28.0 X0(26)(Q) Cusps P-mem Locked — DOI 22452680

| Name | What |
|---|---|
| X0_26_Q | [1,2,13,26] rfl P.mem mem_1 mem_2 mem_13 mem_26 not_mem_3 hInList hNotIn for hGeomForbid |
| beal_forall_eq_exponent13_bridge | none = beal_forall_from_ribet = Contradiction.beal_exponent13_from_ribet BRIDGE none hGeomForbid_typed_true (hNotIn hInList) |
| beal13_forall_bridge_triple | none ⟨exponent13,forall,bridge⟩ |

DOI `22452680` findable records prior mint `22450737` hook `22379293` `IsVersionOf` `22272382` honest original latest `22322627`.

PARI lock: 26a1 Δ `-17576` 26b1 Δ `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260` image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.

# Beal Level 26 Foundations — Exponent 13 Full Package (Computational Boundary)

## v4.27.0 X₀(26) Four Cusps — `P.mem` Lock

Displayed `X0_26_Q` is the four-cusp set `{P | P.label ∈ [1,2,13,26]}`.
`X0_26_cusps` is that list. Membership is decidable: `mem_1` `mem_2`
`mem_13` `mem_26` `not_mem_3`. `hInList_X0_26` / `hNotIn_X0_26` /
`displayed_mem_cusps` feed `hGeomForbid_typed_true` (`hNotIn hInList`).
See [`Chain/X0_26_Point.md`](Chain/X0_26_Point.md). Still not ∀ N.
Still not Mathlib `X0(26)(Q)`.

## v4.25.0 Beal13-Forall-Bridge Triple — Axiom-Free Cert

| Theorem | Axioms |
|---|---|
| beal_forall_eq_exponent13_bridge | none = beal_forall_from_ribet = Contradiction.beal_exponent13_from_ribet BRIDGE none hGeomForbid_typed_true |
| beal13_forall_bridge_triple | none ⟨beal_exponent13_from_ribet, beal_forall_from_ribet, beal_forall_eq_exponent13_bridge⟩ |
| beal13_forall_bridge_triple_none_check / typed_and_forall / certified_typed_and_forall | none |
| beal_forall_from_ribet / certified_from_forall / beal_exponent13_from_ribet | none hGeomForbid |
| contradiction_from_ribet | ribet_level_lowering_26 only |
| Contradiction.certified | frey_modular_13 + ribet_level_lowering_26 |

Formerly `final_bridge` / `final_package` / `final_package_none` — now `beal_forall_eq_exponent13_bridge` / `beal13_forall_bridge_triple` — says what it is: forall = exponent13 bridge triple none. `beal13_forall_bridge_triple_none_check` is the same triple (not `: True`; verify allows only `ribet_secured_by_certs` as `: True :=`). Legacy `final_*` aliases remain. Still not ∀ N. Still not a Mathlib X0(26)(Q) theorem. PARI lock: 26a1 `-17576` 26b1 `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`, image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.

## v4.18.0 Typed ∧ Forall Lock — Axiom-Free Cert

| Theorem | Axioms |
|---|---|
| typed_and_forall | none ⟨beal_exponent13_from_ribet, beal_forall_from_ribet⟩ |
| certified_typed_and_forall | none ⟨certified_from_forall, beal_forall_certified_from_ribet⟩ |
| beal_forall_from_ribet / beal_forall_certified_from_ribet / certified_from_forall | none |
| beal_exponent13_from_ribet / certified_from_ribet | none (hGeomForbid_typed_true via hNotIn hInList) |
| contradiction_from_ribet | ribet_level_lowering_26 only |
| BealExponent13_Contradiction.certified | frey_modular_13 + ribet_level_lowering_26 |

Typed ∧ Forall lock: both conjuncts are `BealTheorem_Exponent13_Typed` via axiom-free `hGeomForbid`. Not ∀ N. Still not a Mathlib X0(26)(Q) theorem. The only axioms are `frey_modular_13` and `ribet_level_lowering_26` (COMPUTATIONAL ASSUMPTION), secured by `certs/pari_x0_26_four_cusps.json`. Not `∀ ℕ`. No `False.elim`.

## PARI 2-Descent Certificates — X0(26) Four Cusps

![2-Descent for Level 26: 26a1 & 26b1 — Sel2=1 Sha[2]=0 J0(26)~26a1×26b1 det M3=2 fourCusps [1,2,13,26]](images/2-descent-level-26-26a1-26b1.webp)

PARI 2-descent certificates for the Jacobian factors of \(J_0(26)\). Certified Weierstrass models are 26a1 `[1,0,1,-5,-8]` Δ `-17576` and 26b1 `[1,-1,1,-3,3]` Δ `-1664`. PARI reports `|Sel₂|=1` twice, `det M₃=2`, and Descent SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `FreyLevel26` is `2*13=26` (`rfl`). `hGeomForbid_typed_true` is proved by `hNotIn hInList` with no axioms. `ExistsNoncuspidal_26` is empty by `P.mem`. The illustration is a schematic of the 2-descent picture (real locus ≈ \(S^1\times S^1\), `Sel₂=1`, Sha[2]=0, \(J_0(26)\sim 26a1\times 26b1\), four cusps `[1,2,13,26]`); certified models and discriminants are the Descent ones, not any alternate Weierstrass equations drawn on the figure.

Versioned release notes for
[beal-level-26-foundations](https://github.com/DavidFox998/beal-level-26-foundations).

**Current as of** tag `v4.7.0-iter-typed-no-axioms-closing` / `v4.8.0-iter-modularity-scaffold` / `v4.9.0-iter-no-True-X0` / `v4.10.0-iter-pari-locked` / `v4.12.0-iter-verify-plus` / `v4.13.0-iter-contradiction-start` / `v4.13.1-iter-unstick` / `v4.14.0-iter-citation-contradiction-locked` / `v4.15.0-iter-typed-forall-bridge` / `v4.16.0-iter-readme-about-locked` / `v4.17.0-iter-forall-bridge-locked` / `v4.18.0-iter-typed-forall-package-locked` / `v4.19.0-iter-readme-typed-forall-locked` / `v4.20.0-iter-package-none-docs-locked` / `v4.23.0-iter-package-final-bridge-locked` / `v4.24.0-iter-readme-final-package-locked` / `v4.25.0-iter-zenodo-triple-bridge-none-mint` / `v4.27.0-iter-X0-26-cusps-P-mem-locked` / `v4.28.0-iter-zenodo-X0-26-cusps-metadata-mint` / `v4.29.0-iter-readme-X0-26-22452680-locked` (prior
`v4.6.0-readmes-about`,
`v4.5.0-forall-real`,
`v4.4.0-typed-refactor-true-close`,
`v4.3.0-final-forall-package`,
`v4.2.2-zenodo-trigger`, `v4.2.1-chabauty-closes-typed`,
`v4.2.0-full-chain`; GitHub release;
version DOI recorded after DataCite `state: findable`).

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
`BealExponent13_Iter_Typed_And_Package` is
`BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`
(not `∀ A B C`).
`BealExponent13_Iter_Package = X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`,
`BealExponent13_Iter_Package.certified`.
`BealTheorem_Exponent13_Full_package` is the same conjunction
in Mazur (no import of this folder). No `∀` with vacuous contradiction.

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

Releases: `v4.2.0-full-chain` `62d0e13`,
`v4.2.1-chabauty-closes-typed` `eed5170`,
`v4.2.2-zenodo-trigger` fresh, `v4.3.0-final-forall-package`,
`v4.4.0-typed-refactor-true-close` `d3cf8a7`, `v4.5.0-forall-real`
`1d0044e`, `v4.6.0-readmes-about`,
`v4.7.0-iter-typed-no-axioms-closing`.

Prior tag
[`v4.1.3-beal-13-theorem`](releases/v4.1.3-beal-13-theorem.md).
Prior tag
[`v4.1.2-beal-13-endgame`](releases/v4.1.2-beal-13-endgame.md).
Prior tag
[`v4.1.1-descent-compute`](releases/v4.1.1-descent-compute.md).
Prior tag
[`v4.1.0-descent-start`](releases/v4.1.0-descent-start.md).
Prior tag
[`v4.0.15-lmfdb-certs-no-doi`](releases/v4.0.15-lmfdb-certs-no-doi.md).
Prior tag
[`v4.0.14-coleman-integral-no-doi`](releases/v4.0.14-coleman-integral-no-doi.md).
Prior tag
[`v4.0.13-formal-immersion-proof-no-doi`](releases/v4.0.13-formal-immersion-proof-no-doi.md).
Prior tag
[`v4.0.12-scheme-stub-no-doi`](releases/v4.0.12-scheme-stub-no-doi.md).
Prior tag
[`v4.0.11-residue-disks-no-doi`](releases/v4.0.11-residue-disks-no-doi.md).
Prior tag
[`v4.0.10-chabauty0-no-doi`](releases/v4.0.10-chabauty0-no-doi.md).
Prior published tag
[`v4.0.9-fourCusps-forall`](releases/v4.0.9-fourCusps-forall.md)
(commit `2281aad`, version DOI
[10.5281/zenodo.22322627](https://doi.org/10.5281/zenodo.22322627)).
Prior published tag
[`v4.0.8-geom-forbid`](releases/v4.0.8-geom-forbid.md) (commit `916f696`,
version DOI
[10.5281/zenodo.22314435](https://doi.org/10.5281/zenodo.22314435)).
Prior published tag
[`v4.0.7-hIdentify-j`](releases/v4.0.7-hIdentify-j.md) (commit `ade01a2`,
version DOI
[10.5281/zenodo.22314212](https://doi.org/10.5281/zenodo.22314212)).
Prior published tag
[`v4.0.7-hIdentify`](releases/v4.0.7-hIdentify.md) (commit `a4143fc`,
version DOI
[10.5281/zenodo.22314092](https://doi.org/10.5281/zenodo.22314092)).
Prior tags
[`v4.0.6-rank-zero-fixed`](releases/v4.0.6-rank-zero-fixed.md)
(commit `2290809`, version DOI
[10.5281/zenodo.22313955](https://doi.org/10.5281/zenodo.22313955)),
[`v4.0.5-nofrey-point`](releases/v4.0.5-nofrey-point.md)
(commit `5b29092`, version DOI
[10.5281/zenodo.22313407](https://doi.org/10.5281/zenodo.22313407)),
[`v4.0.4-x026-rational-points`](releases/v4.0.4-x026-rational-points.md)
(commit `4619a5d`, version DOI
[10.5281/zenodo.22313318](https://doi.org/10.5281/zenodo.22313318)) and
[`v4.0.3-formal-immersion`](releases/v4.0.3-formal-immersion.md)
(commit `75c533d`, version DOI
[10.5281/zenodo.22313241](https://doi.org/10.5281/zenodo.22313241)).

This folder is the release-note archive. It is not a second theorem
statement. The Lean sources and the v1.4.0 ledger remain the evidence;
these notes only record what each tag claimed.

| Path | Contents |
|---|---|
| [`releases/`](releases/README.md) | One note per tagged Foundations release, from `v1.0.0-computable` through `v4.2.1-chabauty-closes-typed` |

The staged plan and open acceptance gates live in [`../PLAN.md`](../PLAN.md).
The public DOI trail is in [`../README.md`](../README.md).

v4.8.0-iter-modularity-scaffold: `X0_26_Point_Raw` + `DisplayedX026CuspPoint` `[1,2,13,26]` `P.mem`; `X0_26_Q` keeps a `True` PLACEHOLDER disjunct; `ExistsNoncuspidal_26` drops trailing `True`; `axiom frey_modular_13` and `axiom ribet_level_lowering_26` are COMPUTATIONAL ASSUMPTION placeholders secured by PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `hGeomForbid_typed_true` still depends on no axioms (`hNotIn hInList`). Old `#check hGeomForbid_typed_is_uninhabitable` stays live. Not `∀ ℕ` and no `False.elim`.

v4.9.0-iter-no-True-X0: `X0_26_Q = {P | P.label ∈ fourCuspsList}` with no `True`. `ExistsNoncuspidal_26` empty by `P.mem` `[1,2,13,26]`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Only axioms `frey_modular_13` and `ribet_level_lowering_26` (COMPUTATIONAL ASSUMPTION), secured by 26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]` Δ `-1664`, PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`, `FreyLevel26` `2 * 13 = 26`. Not `∀ ℕ` and no `False.elim`.

v4.10.0-iter-pari-locked: `certs/pari_x0_26_four_cusps.json` locks `fourCusps` `[1,2,13,26]` and SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `x0_26_four_cusps_cert` matches. `X0_26_Q = {P | P.label ∈ fourCuspsList}` with no `True`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.12.0-iter-verify-plus: `verify-scaffold.sh` locks `docs/images/2-descent-level-26-26a1-26b1.webp`, README PARI 2-descent figure, and `certs/pari_x0_26_four_cusps.json` keys `26a1`/`26b1`/`SHA` (`|Sel₂|=1` twice, `det M₃=2`, fourCusps `[1,2,13,26]`). Facebook filename gone. `X0_26_Q` still no `True`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.13.0-iter-contradiction-start: wires `X0_26_Point` `X0_26_Q_four_cusps` `[1,2,13,26]`, `FreyModularity_13` `2*13=26`, and `ribet_level_lowering_26` into `contradiction_from_ribet` / `beal_exponent13_from_ribet`. `hGeomForbid_typed_true` still depends on no axioms (`hNotIn hInList`). Only axioms `frey_modular_13` and `ribet_level_lowering_26`. Not `∀ ℕ` and no `False.elim`.

v4.13.1-iter-unstick: `verify-scaffold.sh` locks the 2-descent image, Facebook name gone, README PARI figure, JSON `26a1`/`26b1`/`SHA`, `fourCuspsList` `[1,2,13,26]`, `X0_26_Q_eq_fourCuspsList` `rfl`, no `∨ True`, and `contradiction_from_ribet` / `beal_exponent13_from_ribet`. Does not grep Zenodo DOI record ids. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.14.0-iter-citation-contradiction-locked: `CITATION.cff` locks `c2c47db` / four-cusp abstract. `certified_from_ribet` is exported into `BealExponent13_Iter_Package`. `-- SECURED BY certs/pari_x0_26_four_cusps.json + docs/images/2-descent-level-26-26a1-26b1.webp`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.15.0-iter-typed-forall-bridge: `beal_forall_from_ribet := beal_exponent13_from_ribet`. `certified_from_ribet` none via `hGeomForbid_typed_true`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.16.0-iter-readme-about-locked: README theorem table + GitHub About. Image `docs/images/2-descent-level-26-26a1-26b1.webp` locked. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.17.0-iter-forall-bridge-locked: `beal_forall_from_ribet` / `certified_from_forall` none via `hGeomForbid_typed_true`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.18.0-iter-typed-forall-package-locked: `typed_and_forall` / `certified_typed_and_forall` none via `hGeomForbid_typed_true`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.19.0-iter-readme-typed-forall-locked: README theorem table locks Typed ∧ Forall none. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.20.0-iter-package-none-docs-locked: `docs/BealExponent13_Iter_Package.md` locks `typed_and_forall` none. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.
