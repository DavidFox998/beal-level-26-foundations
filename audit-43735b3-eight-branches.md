# Audit of eight branches from baseline `43735b3`

## Audit scope

This audit consolidates eight completed branches rooted in the pinned
`beal-level-26-foundations` baseline
`43735b3b14a9e844d4b4bdf57fa5f68d29e749ee`.

The audit branch itself starts directly from that baseline. It does not merge,
cherry-pick, or restate any theorem from the audited branches. Its only new
project content is this report.

The common environment is:

- Lean / Mathlib pin: Mathlib `v4.12.0`;
- pinned Mathlib revisions recorded by the project: `809c3fb` and `83739542`;
- input revision: `v4.12.0`;
- no `lake update`;
- no vendor changes;
- structural-verification line: Phase `2b60ccd`, tags `v0.27` through `v0.30`;
- live `beal-conjecture` revisions `ea261b9`, `af520d3`;
- release `v30.0.0-level-26-structural-verification`;
- DOI `10.5281/zenodo.22863527`, concept DOI
  `10.5281/zenodo.22379293`;
- paper draft lineage `2124501`, `d09cdf6`, with a six-page
  `paper.pdf` of approximately 394 KB;
- prior four-branch audit `4bf9da8`.

For every audited head, `git merge-base <head> 43735b3` was checked during this
audit and returned exactly
`43735b3b14a9e844d4b4bdf57fa5f68d29e749ee`.

## Executive conclusion

The branches establish a substantial, honest numerical and structural surface.
They verify displayed formulas, finite computations, arithmetic equalities,
named aliases, dependency wiring, and the exact proposition boundaries at
which the pinned library stops.

They do **not** close any of the four principal foundations obligations:

1. the Frey curve's modularity and Frey-specific mod-13 irreducibility;
2. the local Tate/Néron/inertia theorem at `29`;
3. Ribet level lowering from conductor `928` to level `32`, including the
   needed representation-theoretic hypotheses;
4. the analytic and Selmer inputs needed for the Kolyvagin/Mordell--Weil
   finiteness conclusion.

At this pin the displayed discriminant is

```text
Δ = 16 A⁸ B⁸ (A⁴ + B⁴)².
```

Consequently, `HasNewformAtLevel32` cannot be unconditional. It requires the
actual terms supplying:

- modularity of the displayed Frey curve;
- Frey-specific irreducibility of its residual mod-13 representation;
- the local Néron model, conductor, Tate-uniformization, and inertia result at
  `29`;
- Ribet level lowering with all local and global hypotheses discharged.

The immediate blockers are library-scale formalization gaps, not Lean syntax
errors. Numerical display theorems are inhabited; substantive literature
results remain visible as transparent `def ... : Prop` placeholders. No target
proposition was added as an assumption or axiom during this audit.

## Branch summary

| Branch | Head | Parent | Exact merge base |
|---|---|---|---|
| `tate-v29-numerical` | `5bc763b92641304720dd3d912f278474a6eb45b7` | `b3348df0db82c7040f5506e726b1d07887d9449f` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` |
| `mazur-x0-13-numerical` | `ad2b13dced0a787ba44ebc0cef3233ebc11a0d2c` | `146d463c83f0c350c24b7f5a835b7608044fc207` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` |
| `ribet-928-32-numerical` | `cf2b171f4fbbb95f5573b6a8b8d916b9776c55cf` | `b61bec2bfbd735707fab2abd6d9f3647b3b2b7fd` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` |
| `kolyvagin-fintype-numerical` | `3899ef854da9b17b4867368596dd28510cff5eb7` | `6e88d945e3ede435eb209911abc416bd104e59de` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` |
| `final-bridge-honest-43735b3` | `e3c486bfae54bcd0b45ebbfd92452e69ca3fed16` | `a2fe40e75aad90e4f55dd713628d5fd5ce0e4aba` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` |
| `tate-lib-scaffold` | `e6bc230aaf9501b9dbff437667719735e3e16e2f` | `c18c9fd50e9cd1f20bb911e35173aaf920eafe4e` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` |
| `mazur-lib-scaffold` | `8330a7ca2dc3d3efacb1382b31ec64a4269485e4` | `559ed63aa9c74b78e24010461419657c9ae9e799` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` |
| `ribet-lib-scaffold` | `801bbecc6af2adf473ea209b015c512b0fea8ba4` | `d8d5831b66ecdf04c9edfc872666da2623699d48` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` |
| `kolyvagin-lib-scaffold` | `cca276275f084d15ce015783d12fc1dab5d7282f` | `6c448676be8171e7e444ceb9ef32619e91d607df` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` |

The final bridge is a fifth numerical consolidation branch. The four
foundation areas are represented by four numerical branches and four library
scaffolds; `final-bridge-honest-43735b3` records their conditional interface.

## 1. `tate-v29-numerical`

**Head:** `5bc763b92641304720dd3d912f278474a6eb45b7`

**Files:**

- `Tate_Frey_Conductor_29_Numerical.lean`;
- `docs/TATE_BLOCKER_43735b3.md`;
- target registration in `lakefile.lean`.

**Inhabited theorem surface:**

- `frey_discriminant_formula`;
- `frey_discriminant_nat_formula`;
- `frey_discriminant_one_one`;
- `frey_discriminant_nat_one_one`;
- `valuation_discriminant_at_29`;
- `thirteen_dvd_valuation_discriminant_at_29`;
- `displayed_level_eq_32`;
- `displayed_level_eq_928`;
- `nine_twenty_eight_div_twenty_nine_numerical`;
- `thirty_two_mul_twenty_nine_numerical`.

These theorems prove the displayed discriminant and valuation arithmetic,
including the divisibility consequence under their explicit arithmetic
hypotheses. They also verify the displayed level selectors. They do not
construct a Tate curve, a Néron model, a conductor, or an inertia
representation.

**Dependencies:** pinned arithmetic and valuation interfaces already present
at the baseline and its honest structural lineage.

**Blocker:** the project lacks the local theory connecting the displayed
valuation calculation to Tate uniformization, Kodaira type, the Néron
conductor, and residual inertia at `29`. The full dependency analysis is in
`docs/TATE_BLOCKER_43735b3.md`.

**Verification result:** the numerical root and its blocker documentation were
reported green at the branch head. This audit independently verified the head
identity and exact merge base.

## 2. `mazur-x0-13-numerical`

**Head:** `ad2b13dced0a787ba44ebc0cef3233ebc11a0d2c`

**Files:**

- `Mazur_X0_13_Numerical.lean`;
- `docs/MAZUR_BLOCKER_43735b3.md`;
- target registration in `lakefile.lean`.

**Inhabited theorem surface:**

- `x0_13_genus_zero_numerical`;
- `x0_13_cusp_count_two_numerical`;
- `x0_13_genus_zero_and_two_cusps_numerical`;
- `card_sl2_f13_numerical`;
- `thirteen_sum_two_squares_numerical`;
- `split_cartan_normalizer_order_numerical`;
- `forty_eight_lt_sl2_f13_order_numerical`;
- `split_cartan_index_six_numerical`;
- `mazur_x0_13_numerical_surface`.

The branch proves the displayed numerical facts, including `48 < 2184`. It
does not prove that a specific Frey representation has Borel image, that the
Frey curve has or lacks a rational 13-isogeny, or that the displayed
cardinality comparison classifies the image.

**Dependencies:** baseline finite arithmetic and the existing displayed
`X₀(13)` constants.

**Blocker:** a moduli interpretation of `X₀(13)`, the rational-point argument,
the Frey-specific `j`-invariant identification, and the Galois-image theorem
are absent. Genus zero and two named cusps do not imply that those cusps are
all rational points. The full analysis is in
`docs/MAZUR_BLOCKER_43735b3.md`.

**Verification result:** the numerical root and blocker documentation were
reported green at the branch head. This audit independently verified the head
identity and exact merge base.

## 3. `ribet-928-32-numerical`

**Head:** `cf2b171f4fbbb95f5573b6a8b8d916b9776c55cf`

**Files:**

- `Ribet_928_to_32_Numerical.lean`;
- `docs/RIBET_BLOCKER_43735b3.md`;
- target registration in `lakefile.lean`.

**Inhabited theorem surface:**

- `nine_twenty_eight_div_twenty_nine_numerical`;
- `thirty_two_mul_twenty_nine_numerical`;
- `nine_twenty_eight_ne_thirty_two_numerical`;
- `twenty_nine_nmid_thirty_two_numerical`;
- `displayed_residual_selector_eq_32`;
- `displayed_residual_selector_eq_928`;
- `level_32_full_dimension_one_numerical`;
- `level_32_newform_list_length_one_numerical`;
- `level_32_full_and_new_dimensions_numerical`;
- `lmfdb_32a1_a29_numerical`;
- `displayed_level_16_dimension_zero_numeral`;
- `displayed_sturm_index_numerator_numerical`;
- `displayed_sturm_bound_eight_numerical`;
- `explicit_empty_candidate_set_card_zero`;
- `ribet_928_to_32_numerical_surface`.

The branch proves the displayed division `928 / 29 = 32`, dimension and table
numerics, and the finite candidate-set computation. Division of two natural
numbers is not a level-lowering theorem.

**Dependencies:** the displayed level and coefficient tables, plus baseline
finite arithmetic. The intended theorem additionally depends on the still-open
Tate and Mazur obligations.

**Blocker:** there is no constructed residual representation with proved
absolute irreducibility and local behavior, no modularity theorem for the
displayed Frey curve, and no applicable Ribet level-lowering theorem. The full
analysis is in `docs/RIBET_BLOCKER_43735b3.md`.

**Verification result:** the numerical root and blocker documentation were
reported green at the branch head. This audit independently verified the head
identity and exact merge base.

## 4. `kolyvagin-fintype-numerical`

**Head:** `3899ef854da9b17b4867368596dd28510cff5eb7`

**Files:**

- `Kolyvagin_MW_Rank0_Numerical.lean`;
- `docs/KOLYVAGIN_BLOCKER_43735b3.md`;
- target registration in `lakefile.lean`.

**Inhabited theorem surface:**

- `l_over_omega_26a1_one_third_numerical`;
- `l_over_omega_26b1_one_seventh_numerical`;
- `l_over_omega_26a1_nonzero_numerical`;
- `l_over_omega_26b1_nonzero_numerical`;
- `sel2_card_26a1_one_numerical`;
- `sel2_card_26b1_one_numerical`;
- `sel2_cards_both_one_numerical`;
- `two_pow_sel2_dimensions_one_numerical`;
- `certified_mwrank_values_zero_numerical`;
- `torsion_orders_product_twenty_one_numerical`;
- `curve26a1_discriminant_numerical`;
- `curve26b1_discriminant_numerical`;
- `not_subsingleton_rank_zero_26a1`;
- `not_subsingleton_rank_zero_26b1`;
- `kolyvagin_mw_rank0_numerical_surface`.

The branch correctly distinguishes displayed rational `L/Ω` values from
formal analytic nonvanishing and a finite Mordell--Weil group from a
subsingleton group. The nonzero torsion points refute the older
`IsRankZero := Subsingleton` formulation.

**Dependencies:** structural parent
`6e88d945e3ede435eb209911abc416bd104e59de`, displayed BSD/descent numerics,
and the existing Mordell--Weil point constructions.

**Blocker:** the pin has no elliptic-curve `L`-function and period
identification, no Kato--Kolyvagin theorem in the required form, no formal
Selmer groups and exact sequence, and no conversion of the displayed Selmer
cardinalities into `Fintype` instances. The full analysis is in
`docs/KOLYVAGIN_BLOCKER_43735b3.md`.

**Verification result:** the numerical root and blocker documentation were
reported green at the branch head. This audit independently verified the head
identity and exact merge base.

## 5. `final-bridge-honest-43735b3`

**Head:** `e3c486bfae54bcd0b45ebbfd92452e69ca3fed16`

**File:** `Bridge_43735b3_Honest_Numerical.lean`, with target registration in
`lakefile.lean`.

**Inhabited theorem and record surface:**

- `frey_discriminant_to_valuation_numerical`;
- `displayed_928_to_32_numerical`;
- `mazur_ribet_kolyvagin_numerical_evidence`;
- proposition-valued evidence record `HasNewformAtLevel32`;
- `has_newform_at_level_32_of_assumptions`.

The final theorem is conditional on actual terms:

- `hMazur : frey_no_rational_13_isogeny`;
- `hTate : Frey_conductor_29_is_Neron`;
- `hRibet : Ribet_928_to_32`.

These are fields of an explicit evidence record, not hidden facts. The bridge
also depends on the modularity and residual-representation interfaces exposed
by the structural line. It therefore documents the intended composition
without claiming that the open terms exist.

**Axiom audit:** the reported dependencies of the proved bridge surface are
the standard Lean foundations `propext`, `Classical.choice`, and
`Quot.sound`. No domain theorem is added as an axiom.

**Blocker:** actual inhabitants for modularity, Frey-specific irreducibility,
Mazur, Tate/Néron/inertia, and Ribet level lowering.

**Verification result:** the bridge target was reported green and its
conditional record checked. This audit independently verified the head
identity and exact merge base.

## 6. `tate-lib-scaffold`

**Head:** `e6bc230aaf9501b9dbff437667719735e3e16e2f`

**Modules:**

- `TateCurve/TateParameter.lean`;
- `TateCurve/TateUniformization.lean`;
- `TateCurve/NeronConductor.lean`;
- `TateCurve/InertiaRepresentation.lean`;
- `TateCurve/BlockerDoc.lean`.

**Inhabited surface:**

- structure `TateParameter`;
- numerical wrappers `tate_numerical_layer_uses_only_proved` and
  `displayed_level_928_uses_only_proved`;
- explicit arithmetic function `residualOddEstimate`;
- displayed Kodaira-data carrier `Frey_Kodaira_at_29`.

**Transparent proposition boundaries:**

- `Frey_Tate_q_at_29`;
- `tate_curve_at_29`;
- `Tate_uniformization`;
- `Tate_q`;
- `Frey_Neron_conductor`;
- `Frey_conductor_29_is_Neron`;
- `inertia_at_29_trivial_mod13_full`;
- `inertia_trivial_mod13_when_13_dvd_v`;
- `ribet_unramified_at_29_of_dvd_C`.

The intended forward chain is Tate parameter to Tate uniformization to Néron
conductor to inertia and finally the residual odd-level estimate. The module
names this chain but does not inhabit its literature-scale steps.

**Dependencies:** `tate-v29-numerical` plus missing local elliptic-curve,
valuation, Néron-model, and Galois-representation infrastructure.

**Verification result:** `TateCurve.BlockerDoc` and its registered build root
were reported green. This audit independently verified the head identity and
exact merge base.

## 7. `mazur-lib-scaffold`

**Head:** `8330a7ca2dc3d3efacb1382b31ec64a4269485e4`

**Modules:**

- `MazurCurve/X0_13_Moduli.lean`;
- `MazurCurve/FreyJInvariant.lean`;
- `MazurCurve/GaloisRepresentation.lean`;
- `MazurCurve/BlockerDoc.lean`.

**Inhabited surface:**

- structure `X0_13_Point`;
- type boundary `X0_13_RationalPoints`;
- the Fricke parameterization
  `(t² + 5t + 13)(t⁴ + 7t³ + 20t² + 19t + 1)³ / t`;
- the displayed Frey expression `c₄³ / Δ`;
- wrappers `mazur_numerical_layer_uses_only_proved` and
  `mazur_core_numerics_use_only_proved`.

**Transparent proposition boundaries:**

- `reducible_13_iff_j_in_image`;
- `no_t_gives_Frey_j_when_29_dvd_C`;
- `rho_Frey_mod13`;
- `rho_Frey_mod13_irreducible`;
- `mazur_irreducible_13_via_X0_13`;
- `frey_no_rational_13_isogeny`;
- `mazur_irreducible_13_theorem`;
- `mazur_no_Frey_13_isogeny`.

Genus zero does not mean that `X₀(13)(ℚ)` consists of only two rational
points. Likewise `48 < 2184` does not by itself prove that the Frey image is
non-Borel or irreducible.

**Dependencies:** `mazur-x0-13-numerical` plus a formal modular-curve moduli
interpretation, rational-point classification, and Frey-specific
Galois-representation theory.

**Verification result:** `MazurCurve.BlockerDoc` and its registered build root
were reported green. This audit independently verified the head identity and
exact merge base.

## 8. `ribet-lib-scaffold`

**Head:** `801bbecc6af2adf473ea209b015c512b0fea8ba4`

**Modules:**

- `RibetCurve/Modularity.lean`;
- `RibetCurve/GaloisRep.lean`;
- `RibetCurve/Conductor.lean`;
- `RibetCurve/LevelLowering.lean`;
- `RibetCurve/Newform32.lean`;
- `RibetCurve/KrausElimination.lean`;
- `RibetCurve/BlockerDoc.lean`.

**Inhabited surface:**

- displayed selector theorems `displayed_level_eq_32` and
  `displayed_level_eq_928`;
- numerical wrappers `ribet_numerical_layer_uses_only_proved` and
  `displayed_selector_32_uses_only_proved`;
- aliases `frey_ap` and `newform_32a1_ap` for the existing point-count trace
  and coefficient table, including the displayed `a₂₉(32a1) = -10`.

**Transparent proposition boundaries:**

- `modular_Frey`;
- `residual_Galois_representation_mod13`;
- `residual_Galois_representation_mod13_absolutely_irreducible`;
- `residual_Galois_representation_mod13_unramified_at_29`;
- `Frey_local_conductor_exponent_at_29`;
- `Frey_Neron_conductor_is_32_or_928`;
- `ribet_level_lowering_29_to_32`;
- `Ribet_928_to_32`;
- `Ribet_level_lowering_abstract`;
- `level_32_no_newform_for_Frey_gap3`;
- `level_32_no_newform`;
- `no_newforms_at_32_mod13`;
- `explicit_a29_mod13_complete_Kraus_elimination`.

The equality `928 / 29 = 32` is necessary arithmetic after removal of the
prime `29`; it is not a proof that the prime may be removed from the conductor
of the relevant residual representation.

**Dependencies:** `ribet-928-32-numerical`, the Tate local theorem, the
Mazur/Frey irreducibility theorem, modularity, and a formal Ribet
level-lowering theorem.

**Verification result:** `RibetCurve.BlockerDoc` and its registered build root
were reported green. This audit independently verified the head identity and
exact merge base.

## 9. `kolyvagin-lib-scaffold`

**Head:** `cca276275f084d15ce015783d12fc1dab5d7282f`

**Modules:**

- `KolyvaginCurve/LFunction.lean`;
- `KolyvaginCurve/Periods.lean`;
- `KolyvaginCurve/KatoKolyvagin.lean`;
- `KolyvaginCurve/FiniteGeneration.lean`;
- `KolyvaginCurve/SelmerExactSequence.lean`;
- `KolyvaginCurve/MordellWeilFintype.lean`;
- `KolyvaginCurve/TwoDescent.lean`;
- `KolyvaginCurve/BlockerDoc.lean`.

**Inhabited surface:**

- rational definitions `L_over_Omega_26a1`, `L_over_Omega_26b1`;
- their displayed equalities and rational nonvanishing;
- `not_subsingleton_rank_zero_26a1`;
- `not_subsingleton_rank_zero_26b1`;
- `kolyvagin_numerical_layer_uses_only_proved`.

**Transparent proposition boundaries:**

- `L_26a1`, `L_26b1`;
- `L_26a1_ne_zero`, `L_26b1_ne_zero`;
- `MordellWeil_finitely_generated`;
- `MordellWeil_26a1_finitely_generated`;
- `MordellWeil_26b1_finitely_generated`;
- `Kolyvagin_L_nonzero_imp_MW_rank_zero`;
- `Kolyvagin_TateShafarevich_finite`;
- `twoSelmer_exact_sequence`;
- `singleton_twoSelmer_implies_MW_finite`;
- `MW_rank_zero_fintype`;
- `MW_rank_zero_26a1_fintype`;
- `MW_rank_zero_26b1_fintype`;
- `TwoDescent_implies_MW_rank_zero_fintype`.

The correct endpoint is `Nonempty (Fintype (MordellWeilGroup E))`, not
`Subsingleton (MordellWeilGroup E)`. Displayed `L/Ω ≠ 0` is not formal
`L(E,1) ≠ 0`, and a displayed Selmer-cardinality numeral is not a constructed
finite Selmer group.

**Dependencies:** structural parent
`6e88d945e3ede435eb209911abc416bd104e59de`, numerical parent
`3899ef854da9b17b4867368596dd28510cff5eb7`, and the missing analytic,
Selmer, finite-generation, and Kato--Kolyvagin libraries.

**Verification result:** `lake exe cache get`,
`lake build KolyvaginCurve.BlockerDoc`,
`lake build BealMatveevBealV25B0Search`, and
`bash scripts/verify-matveev-beal.sh` passed at the branch head. The registered
build completed 5,185 jobs. Its printed axioms for
`kolyvagin_numerical_layer_uses_only_proved` were exactly `propext`,
`Classical.choice`, and `Quot.sound`. This audit independently verified the
head identity and exact merge base.

## Cross-branch dependency chain

The intended proof architecture is:

1. construct the displayed Frey curve and prove its modularity;
2. construct its residual mod-13 representation and prove Frey-specific
   absolute irreducibility, using the Mazur/`X₀(13)` input;
3. prove the local Tate parameter, Néron conductor, and residual inertia
   behavior at `29`;
4. apply Ribet level lowering to remove `29` from `928`, obtaining level `32`;
5. identify and eliminate the level-32 newform candidate;
6. separately construct the analytic and Selmer objects needed to turn the
   displayed level-26 numerical evidence into Mordell--Weil finiteness.

The branches now expose every transition in this chain. Exposure is not
closure: the decisive arrows are proposition-valued interfaces without
inhabitants.

## Verification record

The branch histories report the following six project roots green:

- default target;
- `HonestB0Search`;
- `Level26`;
- `BealMatveevBeal`;
- `BealMatveevBealV25Rank3`;
- `BealMatveevBealV25B0Search`.

Recorded green run identifiers are:

- `6b2bb32`;
- `35673305054`;
- `05fda4b`;
- `35668805532`.

During this audit:

- all nine listed heads, including the final bridge, resolved to the stated
  commits;
- all heads had exact merge base `43735b3`;
- branch parents and changed-file surfaces were inspected;
- theorem and `def Prop` surfaces were compared with the branch blocker
  documentation;
- no theorem source was copied into the audit branch;
- no Lean target proposition was introduced as an assumption or axiom;
- the audit branch remained a documentation-only child of `43735b3`.

## Remaining assumptions

The following remain mathematically substantive and unproved at this pin:

1. modularity for the exact displayed Frey curve;
2. construction of its mod-13 Galois representation;
3. absolute irreducibility / absence of a rational 13-isogeny for that Frey
   curve;
4. the required `X₀(13)` moduli and rational-point argument;
5. local Tate uniformization at `29`;
6. construction of the relevant Néron model and conductor exponent;
7. the residual inertia/unramifiedness statement at `29`;
8. Ribet level lowering from `928` to `32` for the constructed
   representation;
9. formal newform and Hecke-eigenvalue comparison sufficient for the Kraus
   elimination;
10. elliptic-curve `L`-functions and real periods for `26a1` and `26b1`;
11. identification of the displayed rational `L/Ω` values with those analytic
    objects;
12. Kato--Kolyvagin in the form needed for algebraic rank zero and
    Tate--Shafarevich finiteness;
13. formal two-Selmer groups and the Selmer exact sequence;
14. Mordell--Weil finite generation for the project point type;
15. conversion from the displayed Selmer and mwrank data to
    `Nonempty (Fintype (MordellWeilGroup E))`.

These are the honest boundaries. The eight branches and final bridge make the
available numerical evidence reusable without asserting that any of these
literature-scale results has already been formalized.

## Publication-surface validation on 2026-09-22

The executable validator
`scripts/validate-publication-surface.sh` was run from a clean checkout of the
baseline, every numerical head, the final bridge, every scaffold head, and the
audit head. It checks the exact merge base, Lean and Mathlib pins, absence of
`lake update`, the live `v0.27`--`v0.30` tags, the external
`beal-conjecture` publication lineage and identifiers, the separate paper
branch and PDF, branch-local theorem and scaffold surfaces, the conditional
bridge, direct Lean elaboration and axiom output, the maximal registered build,
the referee script, and proof-level `sorry` / `sorryAx`.

The final results are:

| Checkout | Head | Validator | Direct source surface | Cache / maximal build / referee |
|---|---|---|---|---|
| baseline `43735b3` | `43735b3b14a9e844d4b4bdf57fa5f68d29e749ee` | PASS | PASS | PASS / PASS / PASS |
| `tate-v29-numerical` | `5bc763b92641304720dd3d912f278474a6eb45b7` | **FAIL** | **FAIL** | PASS / PASS / PASS |
| `mazur-x0-13-numerical` | `ad2b13dced0a787ba44ebc0cef3233ebc11a0d2c` | PASS | PASS | PASS / PASS / PASS |
| `ribet-928-32-numerical` | `cf2b171f4fbbb95f5573b6a8b8d916b9776c55cf` | PASS | PASS | PASS / PASS / PASS |
| `kolyvagin-fintype-numerical` | `3899ef854da9b17b4867368596dd28510cff5eb7` | **FAIL** | **FAIL** | PASS / PASS / PASS |
| `final-bridge-honest-43735b3` | `e3c486bfae54bcd0b45ebbfd92452e69ca3fed16` | **FAIL** | **FAIL** | PASS / PASS / PASS |
| `tate-lib-scaffold` | `e6bc230aaf9501b9dbff437667719735e3e16e2f` | **FAIL** | **FAIL** | PASS / PASS / PASS |
| `mazur-lib-scaffold` | `8330a7ca2dc3d3efacb1382b31ec64a4269485e4` | PASS | PASS | PASS / PASS / PASS |
| `ribet-lib-scaffold` | `801bbecc6af2adf473ea209b015c512b0fea8ba4` | PASS | PASS | PASS / PASS / PASS |
| `kolyvagin-lib-scaffold` | `cca276275f084d15ce015783d12fc1dab5d7282f` | **FAIL** | **FAIL** | PASS / PASS / PASS |
| `audit-43735b3-eight-branches` | `3f48ba73b4b2eb1b2122a9dfbb2c74e50635fc50` | PASS | PASS | PASS / PASS / PASS |

The Tate numerical head fails direct elaboration at
`Tate_Frey_Conductor_29_Numerical.lean:71`: the identifier
`thirteen_dvd_v29_Delta_reexport` is unresolved. Lean consequently reports
`sorryAx` in the affected theorem's axiom output. The Tate scaffold and final
bridge inherit this source-level failure.

The Kolyvagin numerical head fails direct elaboration because
`two_pow_sel2_is_one`, `curve26a1_Δ_reexport`, and
`curve26b1_Δ_reexport` are unresolved. Lean reports `sorryAx` in the affected
numerical surface. The Kolyvagin scaffold inherits this failure.

The bridge's structural checks themselves pass: `HasNewformAtLevel32` is a
local proposition-valued evidence record, and its open library-scale
assumptions are exactly `hMazur`, `hTate`, and `hRibet`. Its validator result
is nevertheless a failure because the imported Tate numerical module does not
compile directly.

For each failed head, the required independent commands

```text
lake exe cache get
lake build BealMatveevBealV25B0Search
bash scripts/verify-matveev-beal.sh
```

all return successfully. That green cached build surface does not establish
that the checked-out source elaborates: direct `lake env lean` detects the
unresolved identifiers and resulting `sorryAx`. The validator therefore treats
the five affected heads as failures rather than allowing cached artifacts to
mask source drift.

All heads passed the publication metadata, exact-merge-base, pin, release-tag,
paper-artifact, and tracked-source placeholder checks reached before direct
elaboration. No tracked Lean source contains a proof-level `sorry` or
`sorryAx`; the reported `sorryAx` terms are generated by Lean after the
unresolved-identifier errors above. The publication-validation branch itself
passes the validator end to end and changes no Lean source.