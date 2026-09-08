#!/usr/bin/env bash
set -euo pipefail

test -f README.md
test -f docs/OPERA_NUMERORUM_LINKS.md
test -f docs/README.md
test -f docs/releases/README.md
test -f lean/README.md
test -f lean/Beal/README.md
test -f lean/Beal/Foundations/README.md
test -f lean/BealLevel26Foundations/README.md
test -f lean/BealLevel26Foundations/Frey/README.md
test -f lean/BealLevel26Foundations/Jacobian/README.md
test -f lean/BealLevel26Foundations/Mazur/README.md
test -f lean/BealLevel26Foundations/Real/README.md
test -f lean/BealLevel26Foundations/Ribet/README.md
test -f sagemath/README.md
test -f sagemath/certs/README.md
test -f scripts/README.md
test -f .github/README.md
test -f PLAN.md
test -f lean-toolchain
test -f lakefile.lean
test -f lean/BealLevel26Foundations.lean
test -f lean/BealLevel26Foundations/FiniteEvidence.lean
test -f lean/BealLevel26Foundations/CoefficientLedger_26.lean
test -f lean/BealLevel26Foundations/M3_Explicit.lean
test -f lean/BealLevel26Foundations/FiniteChecks_26.lean
test -f lean/BealLevel26Foundations/Scaffold.lean
test -f lean/BealLevel26Foundations/Frey/FreyConductorData_26.lean
test -f lean/BealLevel26Foundations/Mazur/Genus_26_Scaffold.lean
test -f lean/BealLevel26Foundations/Mazur/QExpansionCotangent_Scaffold_26.lean
test -f lean/BealLevel26Foundations/Real.lean
test -f lean/BealLevel26Foundations/Real/FreyWeierstrass.lean
test -f lean/BealLevel26Foundations/Real/Conductor_26_Unconditional.lean
test -f lean/BealLevel26Foundations/Frey/FreyConductorUnconditional_26.lean
test -f lean/BealLevel26Foundations/Frey/Conductor_26_Unconditional.lean
test -f lean/BealLevel26Foundations/AbelJacobiDifferential.lean
test -f lean/BealLevel26Foundations/Mazur/Genus_26_Real.lean
test -f lean/BealLevel26Foundations/Mazur/QExpansionCotangent_Real_26.lean
test -f CITATION.cff
test -f LICENSE
test -f docs/releases/v1.0.1-computable.md
test -f docs/releases/v1.3.0.md
test -f docs/releases/v1.4.0.md
test -f docs/releases/v2.0.0-frey.md
test -f docs/releases/v3.0.0-ribet.md
test -f docs/releases/v4.0.0-mazur.md
test -f docs/releases/v4.0.1-jacobian-skeleton.md
test -f docs/releases/v4.0.2-selmer.md
test -f docs/releases/v4.0.3-formal-immersion.md
test -f docs/releases/v4.0.4-x026-rational-points.md
test -f docs/releases/v4.0.5-nofrey-point.md
test -f docs/releases/v4.0.6-rank-zero-fixed.md
test -f docs/releases/v4.0.7-hIdentify.md
test -f docs/releases/v4.0.7-hIdentify-j.md
test -f docs/releases/v4.0.8-geom-forbid.md
test -f docs/releases/v4.0.9-fourCusps-forall.md
test -f docs/releases/v4.0.10-chabauty0-no-doi.md
test -f docs/releases/v4.0.11-residue-disks-no-doi.md
test -f docs/releases/v4.0.12-scheme-stub-no-doi.md
test -f docs/releases/v4.0.13-formal-immersion-proof-no-doi.md
test -f docs/releases/v4.0.14-coleman-integral-no-doi.md
test -f docs/releases/v4.0.15-lmfdb-certs-no-doi.md
test -f docs/releases/v4.1.0-descent-start.md
test -f docs/releases/v4.1.1-descent-compute.md
test -f docs/releases/v4.1.2-beal-13-endgame.md
test -f docs/releases/v4.1.3-beal-13-theorem.md
test -f docs/releases/v4.2.0-full-chain.md
test -f docs/releases/v4.2.1-chabauty-closes-typed.md
test -f docs/releases/v4.2.2-zenodo-trigger.md
test -f docs/releases/v4.3.0-final-forall-package.md
test -f docs/releases/v4.4.0-typed-refactor-true-close.md
test -f docs/releases/v4.5.0-forall-real.md
test -f docs/releases/v4.6.0-readmes-about.md
test -f docs/releases/v4.7.0-iter-typed-no-axioms-closing.md
test -f docs/releases/v4.8.0-iter-modularity-scaffold.md
test -f docs/releases/v4.9.0-iter-no-True-X0.md
test -f docs/releases/v4.10.0-iter-pari-locked.md
test -f docs/releases/v4.12.0-iter-verify-plus.md
test -f docs/releases/v4.13.0-iter-contradiction-start.md
test -f docs/releases/v4.13.1-iter-unstick.md
test -f docs/images/2-descent-level-26-26a1-26b1.webp
test -f lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean
test -f lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
test -f docs/BealExponent13_Iter_Package.md
test -f certs/pari_x0_26_four_cusps.json
test -f docs/NEXT_STEPS.md
test -f lean/BealLevel26Foundations/Chain/X0_26_Point.lean
test -f docs/Chain/X0_26_Point.md
test -f docs/releases/v4.27.0-iter-X0-26-cusps-P-mem-locked.md
test -f docs/releases/v4.28.0-iter-zenodo-X0-26-cusps-metadata-mint.md
test -f docs/releases/v4.29.0-iter-readme-X0-26-22452680-locked.md
test -f docs/releases/v4.30.0-iter-zenodo-22456594-metadata-fix.md
test -f docs/Chain/README.md
test -f docs/Modularity/README.md
test -f docs/Mazur/README.md
test -f docs/Final/README.md
test -f docs/Final/BealExponent13_Forall.md
test -f lean/BealLevel26Foundations/Modularity/FreyModularity_13.lean
test -f lean/BealLevel26Foundations/Modularity/RibetLevelLowering_26.lean
test -f lean/BealLevel26Foundations/Modularity/README.md
test -f docs/CHANGELOG.md
test -f lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
test -f lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
test -f lean/BealLevel26Foundations/Final/README.md
test -f lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
test -f lean/BealLevel26Foundations/Chain/README.md
test -f lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
test -f lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
test -f lean/BealLevel26Foundations/Certs/Descent_26.json
test -f scripts/verify_descent_26.py
test -f lean/BealLevel26Foundations/Descent/README.md
test -f lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean
test -f lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
test -f lean/BealLevel26Foundations/Descent/Selmer_26.lean
test -f lean/BealLevel26Foundations/Blueprint/README.md
test -f lean/BealLevel26Foundations/Certs/LMFDB_26.json
test -f lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean
test -f scripts/fetch_LMFDB.py
test -f scripts/verify_lmfdb_26.py
test -f lean/BealLevel26Foundations/Jacobian/ResidueDisksProof_26.lean
test -f lean/BealLevel26Foundations/Jacobian/ColemanIntegral_26.lean
test -f lean/BealLevel26Foundations/Jacobian/ColemanNonVanishing_26.lean
test -f lean/BealLevel26Foundations/Jacobian/J0_26_Scheme_26.lean
test -f lean/BealLevel26Foundations/Jacobian/AbelJacobi_26.lean
test -f lean/BealLevel26Foundations/Jacobian/ResidueDisks_26.lean
test -f lean/BealLevel26Foundations/Jacobian/MordellWeilSieve_26.lean
test -f lean/BealLevel26Foundations/Mazur/X026RationalPointsScheme_26.lean
test -f lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
test -f lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
test -f lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
test -f lean/Beal/Foundations/EndgameScaffold.lean
test -f lean/BealLevel26Foundations/Jacobian/J0_26_DecompActual.lean
test -f lean/BealLevel26Foundations/Jacobian/PicardAbelJacobiIdentification_26.lean
test -f lean/BealLevel26Foundations/Ribet/LevelLowering_26.lean
test -f lean/BealLevel26Foundations/Real/LevelLowering_26.lean
test -f lean/Beal/Foundations/LevelLowering_26.lean
test -f sagemath/level_26_ledger.json
test -f sagemath/foundations_doi_manifest.json
test -f sagemath/certs/j0_26_decomposition.json
test -f sagemath/certs/formal_immersion_M3.json
test -f sagemath/j0_26_decomp_foundation.sage
test -f sagemath/j0_26_decomp_foundations.sage
test -f sagemath/formal_immersion_M3.sage
test -f lean/Beal/Foundations.lean
test -f lean/Beal.lean
test -f lean/Beal/Foundations/J0_26_Decomp.lean
test -f lean/Beal/Foundations/J0DecompositionCertificate.lean
test -f lean/Beal/Foundations/FormalImmersionM3.lean
test -f lean/Beal/Foundations/FormalImmersionM3Certificate.lean
test -f lean/BealLevel26Foundations/GaloisRep/FreyGaloisRepReal.lean
test -f lean/BealLevel26Foundations/GaloisRep/FreyDeltaSeparated.lean
test -f lean/BealLevel26Foundations/GaloisRep/GaloisDetCyclotomicReal.lean
test -f lean/BealLevel26Foundations/GaloisRep/GaloisUnramifiedSemistableReal.lean
test -f lean/BealLevel26Foundations/GaloisRep/GaloisFiniteFlatAt13Real.lean
test -f lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean
test -f lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean
test -f lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean
test -f lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean
test -f lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/HeckeAlgebra.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/RibetFunctor.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/HeckeAction.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/LevelLowering.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixedCore.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed_5_100.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed_901_1000.lean
test -f lean/BealLevel26Foundations/Beal/FullProof/X0_2_Genus.lean
test -f docs/Beal/X0_2_Genus.md
test -f lean/BealLevel26Foundations/Beal/FullProof/Beal_4_13_13_Size_Table.lean
test -f certs/Beal_4_13_13_Size_Table.lean
test -f lean/BealLevel26Foundations/Beal_4_13_13_Size_C_ge_B_plus_2.lean
test -f certs/Beal_4_13_13_Size_C_ge_B_plus_2_Table.lean
test -f docs/Beal/Beal_4_13_13_Size_C_ge_B_plus_2.md
test -f docs/Beal/Beal_4_13_13_Size.md
test -f lean/BealLevel26Foundations/Beal/FullProof.lean
test -f docs/Beal/TrueConductor.md
test -f docs/Beal/ModularityRibet.md
test -f docs/Beal/GeometryBridge.md
test -f docs/Beal/BealForallProof.md
test -f docs/Beal/ModularImpliesNewform.md
test -f docs/Beal/GeometryScheme.md
test -f docs/Beal/HeckeAlgebra.md
test -f docs/Beal/RibetFunctor.md
test -f docs/Beal/X0_26_Model.md
test -f docs/Beal/HeckeAction.md
test -f docs/Beal/LevelLowering.md
test -f docs/Beal/RibetMazur.md
test -f lean/BealLevel26Foundations/Tate/RealTateAlgorithm.lean
test -f lean/BealLevel26Foundations/RT/PatchingWitnessReal.lean
test -f lean/BealLevel26Foundations/RT/TaylorWilesInfiniteFamily.lean

grep -q "def rho_bar_Frey_13_real_algorithm_inhabited" \
  lean/BealLevel26Foundations/GaloisRep/FreyGaloisRepReal.lean
grep -q "def frey_Delta13_formula" \
  lean/BealLevel26Foundations/GaloisRep/FreyDeltaSeparated.lean
grep -q "theorem frey_Delta13_ne_0_of_pos_real" \
  lean/BealLevel26Foundations/GaloisRep/FreyDeltaSeparated.lean
grep -q "def FreyGaloisRep13_real_algorithm_inhabited_separated" \
  lean/BealLevel26Foundations/GaloisRep/FreyDeltaSeparated.lean
grep -q "def beal_forall_in_kernel_from_delta_separated" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def cyclotomicCharacter13" \
  lean/BealLevel26Foundations/GaloisRep/GaloisDetCyclotomicReal.lean
grep -q "def frey_det_eq_cyclotomic_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisDetCyclotomicReal.lean
grep -q "def frey_det_eq_cyclotomic_real_lemma" \
  lean/BealLevel26Foundations/GaloisRep/GaloisDetCyclotomicReal.lean
grep -q "def rho_bar_Frey_13_real_algorithm_inhabited_det" \
  lean/BealLevel26Foundations/GaloisRep/GaloisDetCyclotomicReal.lean
grep -q "def FreyCurveSeparated_det.token" \
  lean/BealLevel26Foundations/GaloisRep/GaloisDetCyclotomicReal.lean
grep -q "def beal_forall_in_kernel_from_det_separated" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def frey_unramified_outside_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisUnramifiedSemistableReal.lean
grep -q "def frey_semistable_at_2_13_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisUnramifiedSemistableReal.lean
grep -q "def frey_unramified_outside_real_lemma" \
  lean/BealLevel26Foundations/GaloisRep/GaloisUnramifiedSemistableReal.lean
grep -q "def rho_bar_Frey_13_real_algorithm_inhabited_unramified" \
  lean/BealLevel26Foundations/GaloisRep/GaloisUnramifiedSemistableReal.lean
grep -q "def FreyCurveSeparated_unramified.token" \
  lean/BealLevel26Foundations/GaloisRep/GaloisUnramifiedSemistableReal.lean
grep -q "def beal_forall_in_kernel_from_unramified_separated" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def frey_finite_flat_at_13_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisFiniteFlatAt13Real.lean
grep -q "def frey_finite_flat_at_13_real_lemma" \
  lean/BealLevel26Foundations/GaloisRep/GaloisFiniteFlatAt13Real.lean
grep -q "def rho_bar_Frey_13_real_algorithm_inhabited_finite_flat" \
  lean/BealLevel26Foundations/GaloisRep/GaloisFiniteFlatAt13Real.lean
grep -q "def FreyCurveSeparated_finite_flat.token" \
  lean/BealLevel26Foundations/GaloisRep/GaloisFiniteFlatAt13Real.lean
grep -q "def beal_forall_in_kernel_from_finite_flat_separated" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def ribet_level_26_div_13_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean
grep -q "def frey_ribet_level_lowering_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean
grep -q "def frey_ribet_level_lowering_real_lemma" \
  lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean
grep -q "def frey_modularity_at_26_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean
grep -q "def rho_bar_Frey_13_real_algorithm_inhabited_ribet" \
  lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean
grep -q "def FreyCurveSeparated_ribet.token" \
  lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean
grep -q "def beal_forall_in_kernel_from_ribet_separated" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def frey_TW_primes_Q_n_real_infinite_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean
grep -q "def frey_R_T_patching_witness_real_infinite_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean
grep -q "def frey_modular_lifting_at_26_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean
grep -q "def frey_modular_lifting_at_26_real_lemma" \
  lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean
grep -q "def rho_bar_Frey_13_real_algorithm_inhabited_modular_lifting" \
  lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean
grep -q "def FreyCurveSeparated_modular_lifting.token" \
  lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean
grep -q "def beal_forall_in_kernel_from_modular_lifting_separated" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def frey_exists_newform_level_2_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean
grep -q "def frey_exists_newform_level_2_real_lemma" \
  lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean
grep -q "def ExistsNewformLevel2_real_witness" \
  lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean
grep -q "def rho_bar_Frey_13_real_algorithm_inhabited_exists_newform" \
  lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean
grep -q "def FreyCurveSeparated_exists_newform.token" \
  lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean
grep -q "def beal_forall_in_kernel_from_exists_newform_separated" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def frey_beal_forall_closed_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean
grep -q "def frey_beal_forall_closed_real_lemma" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean
grep -q "def BealForall_real_witness" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean
grep -q "def rho_bar_Frey_13_real_algorithm_inhabited_beal_forall_closed" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean
grep -q "def FreyCurveSeparated_beal_forall_closed.token" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean
grep -q "def beal_forall_in_kernel_from_beal_forall_closed_separated" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def frey_beal_forall_none_formula" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean
grep -q "def frey_beal_forall_none_real_lemma" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean
grep -q "def BealForall_real_witness_none" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean
grep -q "def rho_bar_Frey_13_real_algorithm_inhabited_beal_forall_none" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean
grep -q "def FreyCurveSeparated_beal_forall_none.token" \
  lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean
grep -q "def beal_forall_in_kernel_from_beal_forall_none_separated" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def beal_forall_in_kernel_from_beal_forall_none_separated_none" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def beal_forall_from_none_formula_displayed" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "theorem tate_real_conductor_26" \
  lean/BealLevel26Foundations/Tate/RealTateAlgorithm.lean
grep -q "def R_T_patching_witness_real" \
  lean/BealLevel26Foundations/RT/PatchingWitnessReal.lean
grep -q "def R_T_patching_witness_real_infinite" \
  lean/BealLevel26Foundations/RT/PatchingWitnessReal.lean
grep -q "def TW_primes_Q_n_real_infinite" \
  lean/BealLevel26Foundations/RT/PatchingWitnessReal.lean
grep -q "def Q_1" \
  lean/BealLevel26Foundations/RT/TaylorWilesInfiniteFamily.lean
grep -q "def Q_2" \
  lean/BealLevel26Foundations/RT/TaylorWilesInfiniteFamily.lean
grep -q "def ChebotarevToken" \
  lean/BealLevel26Foundations/RT/TaylorWilesInfiniteFamily.lean
grep -q "def TW_infinite_family_exists" \
  lean/BealLevel26Foundations/RT/TaylorWilesInfiniteFamily.lean
grep -q "def beal_forall_in_kernel_from_real_algorithms" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
grep -q "def beal_forall_in_kernel_from_infinite_TW" \
  lean/BealLevel26Foundations/Chain/BealForallInKernel.lean
if grep -nE \
    '^import[[:space:]]+(BealLevel26Foundations\.Final|BealLevel26Foundations\.Mazur\.BealTheoremFromMazurChain26|BealLevel26Foundations\.Chain\.PathLock|BealLevel26Foundations\.Chain\.BealForallInKernel|BealLevel26Foundations\.Beal\.BealForall)' \
    lean/BealLevel26Foundations/GaloisRep/FreyGaloisRepReal.lean \
    lean/BealLevel26Foundations/GaloisRep/FreyDeltaSeparated.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisDetCyclotomicReal.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisUnramifiedSemistableReal.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisFiniteFlatAt13Real.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean \
    lean/BealLevel26Foundations/Tate/RealTateAlgorithm.lean \
    lean/BealLevel26Foundations/RT/PatchingWitnessReal.lean \
    lean/BealLevel26Foundations/RT/TaylorWilesInfiniteFamily.lean; then
  echo "FAIL: real-algorithm modules must not import Forall / Mazur / PathLock / kernel (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal" \
    lean/BealLevel26Foundations/GaloisRep/FreyDeltaSeparated.lean; then
  echo "FAIL: FreyDeltaSeparated must not import FreyGaloisRepReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisDetCyclotomicReal.lean; then
  echo "FAIL: GaloisDetCyclotomicReal must not import FreyGaloisRepReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisUnramifiedSemistableReal.lean; then
  echo "FAIL: GaloisUnramifiedSemistableReal must not import FreyGaloisRepReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Tate.RealTateAlgorithm" \
    lean/BealLevel26Foundations/GaloisRep/GaloisUnramifiedSemistableReal.lean; then
  echo "FAIL: GaloisUnramifiedSemistableReal must not import Tate (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisFiniteFlatAt13Real.lean; then
  echo "FAIL: GaloisFiniteFlatAt13Real must not import FreyGaloisRepReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Tate.RealTateAlgorithm" \
    lean/BealLevel26Foundations/GaloisRep/GaloisFiniteFlatAt13Real.lean; then
  echo "FAIL: GaloisFiniteFlatAt13Real must not import Tate (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean; then
  echo "FAIL: GaloisRibetModularityAt26Real must not import FreyGaloisRepReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Tate.RealTateAlgorithm" \
    lean/BealLevel26Foundations/GaloisRep/GaloisRibetModularityAt26Real.lean; then
  echo "FAIL: GaloisRibetModularityAt26Real must not import Tate (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean; then
  echo "FAIL: GaloisModularLiftingAt26Real must not import FreyGaloisRepReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Tate.RealTateAlgorithm" \
    lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean; then
  echo "FAIL: GaloisModularLiftingAt26Real must not import Tate (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.RT.PatchingWitnessReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisModularLiftingAt26Real.lean; then
  echo "FAIL: GaloisModularLiftingAt26Real must not import PatchingWitnessReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean; then
  echo "FAIL: GaloisExistsNewformLevel2Real must not import FreyGaloisRepReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Tate.RealTateAlgorithm" \
    lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean; then
  echo "FAIL: GaloisExistsNewformLevel2Real must not import Tate (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.RT.PatchingWitnessReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean; then
  echo "FAIL: GaloisExistsNewformLevel2Real must not import PatchingWitnessReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Chain.Level2" \
    lean/BealLevel26Foundations/GaloisRep/GaloisExistsNewformLevel2Real.lean; then
  echo "FAIL: GaloisExistsNewformLevel2Real must not import Level2 (false-label lock)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean; then
  echo "FAIL: GaloisBealForallClosedReal must not import FreyGaloisRepReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Tate.RealTateAlgorithm" \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean; then
  echo "FAIL: GaloisBealForallClosedReal must not import Tate (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.RT.PatchingWitnessReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean; then
  echo "FAIL: GaloisBealForallClosedReal must not import PatchingWitnessReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Chain.Level2" \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean; then
  echo "FAIL: GaloisBealForallClosedReal must not import Level2 (false-label lock)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.GaloisRep.FreyGaloisRepReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean; then
  echo "FAIL: GaloisBealForallNoneReal must not import FreyGaloisRepReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Tate.RealTateAlgorithm" \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean; then
  echo "FAIL: GaloisBealForallNoneReal must not import Tate (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.RT.PatchingWitnessReal" \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean; then
  echo "FAIL: GaloisBealForallNoneReal must not import PatchingWitnessReal (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Chain.Level2" \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean; then
  echo "FAIL: GaloisBealForallNoneReal must not import Level2 (false-label lock)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.RT.PatchingWitnessReal" \
    lean/BealLevel26Foundations/RT/TaylorWilesInfiniteFamily.lean; then
  echo "FAIL: TaylorWilesInfiniteFamily must not import PatchingWitnessReal (cycle)"
  exit 1
fi

grep -q "v1.0.1" README.md
grep -q "v1.3.0" README.md
grep -q "v1.4.0" README.md
grep -q "v2.0.0" README.md
grep -q "v2.0.0-frey" README.md
grep -q "v3.0.0" README.md
grep -q "v3.0.0-ribet" README.md
grep -q "v4.0.0" README.md
grep -q "v4.0.0-mazur" README.md
grep -q "v4.0.1-jacobian-skeleton" README.md
grep -q "v4.0.2-selmer" README.md
grep -q "v4.0.3-formal-immersion" README.md
grep -q "v4.0.4-x026-rational-points" README.md
grep -q "v4.0.5-nofrey-point" README.md
grep -q "v4.0.6-rank-zero-fixed" README.md
grep -q "v4.0.7-hIdentify" README.md
grep -q "v4.0.7-hIdentify-j" README.md
grep -q "v4.0.8-geom-forbid" README.md
grep -q "v4.0.9-fourCusps-forall" README.md
grep -q "v4.0.10-chabauty0-no-doi" README.md
grep -q "v4.0.11-residue-disks-no-doi" README.md
grep -q "v4.0.12-scheme-stub-no-doi" README.md
grep -q "v4.0.13-formal-immersion-proof-no-doi" README.md
grep -q "v4.0.14-coleman-integral-no-doi" README.md
grep -q "v4.0.15-lmfdb-certs-no-doi" README.md
grep -q "v4.1.0-descent-start" README.md
grep -q "v4.1.1-descent-compute" README.md
grep -q "v4.1.2-beal-13-endgame" README.md
grep -q "v4.1.3-beal-13-theorem" README.md
grep -q "v4.2.0-full-chain" README.md
grep -q "v4.2.1-chabauty-closes-typed" README.md
grep -q "v4.2.2-zenodo-trigger" README.md
grep -q "v4.3.0-final-forall-package" README.md
grep -q "v4.4.0-typed-refactor-true-close" README.md
grep -q "v4.5.0-forall-real" README.md
grep -q "v4.6.0-readmes-about" README.md
grep -q "v4.7.0-iter-typed-no-axioms-closing" README.md
grep -q "v4.8.0-iter-modularity-scaffold" README.md
grep -q "v4.9.0-iter-no-True-X0" README.md
grep -q "v4.10.0-iter-pari-locked" README.md
grep -q "v4.12.0-iter-verify-plus" README.md
grep -q "v4.13.0-iter-contradiction-start" README.md
grep -q "v4.13.1-iter-unstick" README.md
grep -q "v4.0.3-formal-immersion" docs/README.md
grep -q "v4.0.4-x026-rational-points" docs/README.md
grep -q "v4.0.5-nofrey-point" docs/README.md
grep -q "v4.0.6-rank-zero-fixed" docs/README.md
grep -q "v4.0.7-hIdentify" docs/README.md
grep -q "v4.0.7-hIdentify-j" docs/README.md
grep -q "v4.0.8-geom-forbid" docs/README.md
grep -q "v4.0.9-fourCusps-forall" docs/README.md
grep -q "v4.0.10-chabauty0-no-doi" docs/README.md
grep -q "v4.0.11-residue-disks-no-doi" docs/README.md
grep -q "v4.0.12-scheme-stub-no-doi" docs/README.md
grep -q "v4.0.13-formal-immersion-proof-no-doi" docs/README.md
grep -q "v4.0.14-coleman-integral-no-doi" docs/README.md
grep -q "v4.0.15-lmfdb-certs-no-doi" docs/README.md
grep -q "v4.1.0-descent-start" docs/README.md
grep -q "v4.1.1-descent-compute" docs/README.md
grep -q "v4.1.2-beal-13-endgame" docs/README.md
grep -q "v4.1.3-beal-13-theorem" docs/README.md
grep -q "v4.2.0-full-chain" docs/README.md
grep -q "v4.2.1-chabauty-closes-typed" docs/README.md
grep -q "v4.2.2-zenodo-trigger" docs/README.md
grep -q "v4.3.0-final-forall-package" docs/README.md
grep -q "v4.4.0-typed-refactor-true-close" docs/README.md
grep -q "v4.5.0-forall-real" docs/README.md
grep -q "v4.6.0-readmes-about" docs/README.md
grep -q "v4.7.0-iter-typed-no-axioms-closing" docs/README.md
grep -q "v4.8.0-iter-modularity-scaffold" docs/README.md
grep -q "v4.9.0-iter-no-True-X0" docs/README.md
grep -q "v4.10.0-iter-pari-locked" docs/README.md
grep -q "v4.12.0-iter-verify-plus" docs/README.md
grep -q "v4.13.0-iter-contradiction-start" docs/README.md
grep -q "v4.13.1-iter-unstick" docs/README.md
grep -q "v4.0.3-formal-immersion" docs/releases/README.md
grep -q "v4.0.4-x026-rational-points" docs/releases/README.md
grep -q "v4.0.5-nofrey-point" docs/releases/README.md
grep -q "v4.0.6-rank-zero-fixed" docs/releases/README.md
grep -q "v4.0.7-hIdentify" docs/releases/README.md
grep -q "v4.0.7-hIdentify-j" docs/releases/README.md
grep -q "v4.0.8-geom-forbid" docs/releases/README.md
grep -q "v4.0.9-fourCusps-forall" docs/releases/README.md
grep -q "v4.0.10-chabauty0-no-doi" docs/releases/README.md
grep -q "v4.0.11-residue-disks-no-doi" docs/releases/README.md
grep -q "v4.0.12-scheme-stub-no-doi" docs/releases/README.md
grep -q "v4.0.13-formal-immersion-proof-no-doi" docs/releases/README.md
grep -q "v4.0.14-coleman-integral-no-doi" docs/releases/README.md
grep -q "v4.0.15-lmfdb-certs-no-doi" docs/releases/README.md
grep -q "v4.1.0-descent-start" docs/releases/README.md
grep -q "v4.1.1-descent-compute" docs/releases/README.md
grep -q "v4.1.2-beal-13-endgame" docs/releases/README.md
grep -q "v4.1.3-beal-13-theorem" docs/releases/README.md
grep -q "v4.2.0-full-chain" docs/releases/README.md
grep -q "v4.2.1-chabauty-closes-typed" docs/releases/README.md
grep -q "v4.2.2-zenodo-trigger" docs/releases/README.md
grep -q "v4.3.0-final-forall-package" docs/releases/README.md
grep -q "v4.4.0-typed-refactor-true-close" docs/releases/README.md
grep -q "v4.5.0-forall-real" docs/releases/README.md
grep -q "v4.6.0-readmes-about" docs/releases/README.md
grep -q "v4.7.0-iter-typed-no-axioms-closing" docs/releases/README.md
grep -q "v4.8.0-iter-modularity-scaffold" docs/releases/README.md
grep -q "v4.9.0-iter-no-True-X0" docs/releases/README.md
grep -q "v4.10.0-iter-pari-locked" docs/releases/README.md
grep -q "v4.12.0-iter-verify-plus" docs/releases/README.md
grep -q "v4.13.0-iter-contradiction-start" docs/releases/README.md
grep -q "v4.13.1-iter-unstick" docs/releases/README.md
grep -q "v4.0.3-formal-immersion" lean/README.md
grep -q "v4.0.4-x026-rational-points" lean/README.md
grep -q "v4.0.5-nofrey-point" lean/README.md
grep -q "v4.0.6-rank-zero-fixed" lean/README.md
grep -q "v4.0.7-hIdentify" lean/README.md
grep -q "v4.0.7-hIdentify-j" lean/README.md
grep -q "v4.0.8-geom-forbid" lean/README.md
grep -q "v4.0.9-fourCusps-forall" lean/README.md
grep -q "v4.0.10-chabauty0-no-doi" lean/README.md
grep -q "v4.0.11-residue-disks-no-doi" lean/README.md
grep -q "v4.0.12-scheme-stub-no-doi" lean/README.md
grep -q "v4.0.13-formal-immersion-proof-no-doi" lean/README.md
grep -q "v4.0.14-coleman-integral-no-doi" lean/README.md
grep -q "v4.0.15-lmfdb-certs-no-doi" lean/README.md
grep -q "v4.1.0-descent-start" lean/README.md
grep -q "v4.1.1-descent-compute" lean/README.md
grep -q "v4.1.2-beal-13-endgame" lean/README.md
grep -q "v4.1.3-beal-13-theorem" lean/README.md
grep -q "v4.2.0-full-chain" lean/README.md
grep -q "v4.2.1-chabauty-closes-typed" lean/README.md
grep -q "v4.2.2-zenodo-trigger" lean/README.md
grep -q "v4.3.0-final-forall-package" lean/README.md
grep -q "v4.4.0-typed-refactor-true-close" lean/README.md
grep -q "v4.5.0-forall-real" lean/README.md
grep -q "v4.6.0-readmes-about" lean/README.md
grep -q "v4.7.0-iter-typed-no-axioms-closing" lean/README.md
grep -q "v4.8.0-iter-modularity-scaffold" lean/README.md
grep -q "v4.9.0-iter-no-True-X0" lean/README.md
grep -q "v4.10.0-iter-pari-locked" lean/README.md
grep -q "v4.12.0-iter-verify-plus" lean/README.md
grep -q "v4.13.0-iter-contradiction-start" lean/README.md
grep -q "v4.13.1-iter-unstick" lean/README.md
grep -q "v4.0.3-formal-immersion" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.6-rank-zero-fixed" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.7-hIdentify" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.7-hIdentify-j" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.8-geom-forbid" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.9-fourCusps-forall" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.10-chabauty0-no-doi" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.11-residue-disks-no-doi" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.12-scheme-stub-no-doi" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.13-formal-immersion-proof-no-doi" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.14-coleman-integral-no-doi" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.15-lmfdb-certs-no-doi" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.1.0-descent-start" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.1.1-descent-compute" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.1.2-beal-13-endgame" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.1.3-beal-13-theorem" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.2.0-full-chain" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.2.1-chabauty-closes-typed" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.2.2-zenodo-trigger" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.3.0-final-forall-package" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.4.0-typed-refactor-true-close" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.5.0-forall-real" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.6.0-readmes-about" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.7.0-iter-typed-no-axioms-closing" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.8.0-iter-modularity-scaffold" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.9.0-iter-no-True-X0" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.10.0-iter-pari-locked" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.12.0-iter-verify-plus" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.13.0-iter-contradiction-start" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.13.1-iter-unstick" lean/BealLevel26Foundations/Jacobian/README.md
grep -q "v4.0.4-x026-rational-points" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.6-rank-zero-fixed" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.7-hIdentify" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.7-hIdentify-j" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.8-geom-forbid" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.9-fourCusps-forall" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.10-chabauty0-no-doi" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.11-residue-disks-no-doi" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.12-scheme-stub-no-doi" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.13-formal-immersion-proof-no-doi" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.14-coleman-integral-no-doi" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.15-lmfdb-certs-no-doi" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.1.0-descent-start" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.1.1-descent-compute" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.1.2-beal-13-endgame" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.1.3-beal-13-theorem" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.2.0-full-chain" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.2.1-chabauty-closes-typed" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.2.2-zenodo-trigger" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.3.0-final-forall-package" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.4.0-typed-refactor-true-close" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.5.0-forall-real" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.6.0-readmes-about" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.7.0-iter-typed-no-axioms-closing" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.8.0-iter-modularity-scaffold" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.9.0-iter-no-True-X0" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.10.0-iter-pari-locked" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.12.0-iter-verify-plus" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.13.0-iter-contradiction-start" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.13.1-iter-unstick" lean/BealLevel26Foundations/Mazur/README.md
grep -q "v4.0.5-nofrey-point" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.6-rank-zero-fixed" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.7-hIdentify" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.7-hIdentify-j" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.8-geom-forbid" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.9-fourCusps-forall" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.10-chabauty0-no-doi" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.11-residue-disks-no-doi" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.12-scheme-stub-no-doi" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.13-formal-immersion-proof-no-doi" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.14-coleman-integral-no-doi" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.15-lmfdb-certs-no-doi" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.1.0-descent-start" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.1.1-descent-compute" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.1.2-beal-13-endgame" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.1.3-beal-13-theorem" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.2.0-full-chain" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.2.1-chabauty-closes-typed" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.2.2-zenodo-trigger" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.3.0-final-forall-package" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.4.0-typed-refactor-true-close" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.5.0-forall-real" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.6.0-readmes-about" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.7.0-iter-typed-no-axioms-closing" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.8.0-iter-modularity-scaffold" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.9.0-iter-no-True-X0" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.10.0-iter-pari-locked" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.12.0-iter-verify-plus" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.13.0-iter-contradiction-start" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.13.1-iter-unstick" lean/BealLevel26Foundations/Ribet/README.md
grep -q "v4.0.6-rank-zero-fixed" sagemath/README.md
grep -q "v4.0.7-hIdentify" sagemath/README.md
grep -q "v4.0.7-hIdentify-j" sagemath/README.md
grep -q "v4.0.8-geom-forbid" sagemath/README.md
grep -q "v4.0.9-fourCusps-forall" sagemath/README.md
grep -q "v4.0.10-chabauty0-no-doi" sagemath/README.md
grep -q "v4.0.11-residue-disks-no-doi" sagemath/README.md
grep -q "v4.0.12-scheme-stub-no-doi" sagemath/README.md
grep -q "v4.0.13-formal-immersion-proof-no-doi" sagemath/README.md
grep -q "v4.0.14-coleman-integral-no-doi" sagemath/README.md
grep -q "v4.0.15-lmfdb-certs-no-doi" sagemath/README.md
grep -q "v4.1.0-descent-start" sagemath/README.md
grep -q "v4.1.1-descent-compute" sagemath/README.md
grep -q "v4.1.2-beal-13-endgame" sagemath/README.md
grep -q "v4.1.3-beal-13-theorem" sagemath/README.md
grep -q "v4.2.0-full-chain" sagemath/README.md
grep -q "v4.2.1-chabauty-closes-typed" sagemath/README.md
grep -q "v4.2.2-zenodo-trigger" sagemath/README.md
grep -q "v4.3.0-final-forall-package" sagemath/README.md
grep -q "v4.4.0-typed-refactor-true-close" sagemath/README.md
grep -q "v4.5.0-forall-real" sagemath/README.md
grep -q "v4.6.0-readmes-about" sagemath/README.md
grep -q "v4.7.0-iter-typed-no-axioms-closing" sagemath/README.md
grep -q "v4.8.0-iter-modularity-scaffold" sagemath/README.md
grep -q "v4.9.0-iter-no-True-X0" sagemath/README.md
grep -q "v4.10.0-iter-pari-locked" sagemath/README.md
grep -q "v4.12.0-iter-verify-plus" sagemath/README.md
grep -q "v4.13.0-iter-contradiction-start" sagemath/README.md
grep -q "v4.13.1-iter-unstick" sagemath/README.md
for readme in \
  README.md \
  docs/README.md \
  lean/README.md \
  lean/BealLevel26Foundations/README.md \
  lean/BealLevel26Foundations/Chain/README.md \
  lean/BealLevel26Foundations/Final/README.md \
  lean/BealLevel26Foundations/Mazur/README.md \
  lean/BealLevel26Foundations/Certs/README.md
do
  grep -q "v4.6.0-readmes-about" "$readme"
  grep -q "v4.7.0-iter-typed-no-axioms-closing" "$readme"
  grep -q "v4.8.0-iter-modularity-scaffold" "$readme"
  grep -q "v4.9.0-iter-no-True-X0" "$readme"
  grep -q "v4.10.0-iter-pari-locked" "$readme"
  grep -q "v4.12.0-iter-verify-plus" "$readme"
  grep -q "v4.13.0-iter-contradiction-start" "$readme"
  grep -q "v4.13.1-iter-unstick" "$readme"
  grep -q "BealExponent13_Iter_Package" "$readme"
  grep -q "d3cf8a7" "$readme"
  grep -q "1d0044e" "$readme"
  grep -q "hNotIn hInList" "$readme"
  grep -q "depends on no axioms" "$readme"
  grep -q "not \`∀ ℕ\`" "$readme"
  grep -q "no \`False.elim\`" "$readme"
  grep -q "22452680" "$readme"
  grep -q "22456594" "$readme"
  grep -q "v6.0.0-iter-real-algorithms" "$readme"
  grep -q "v6.0.1-iter-about-catchup-22558788" "$readme"
  grep -q "v6.1.0-iter-tw-infinite-family" "$readme"
  grep -q "v6.1.1-iter-about-catchup-22559449" "$readme"
  grep -q "v6.2.0-iter-frey-delta-separated" "$readme"
  grep -q "v6.2.1-iter-about-catchup-22562014" "$readme"
  grep -q "v6.3.0-iter-det-cyclotomic-real" "$readme"
  grep -q "v6.3.1-iter-about-catchup-22565376" "$readme"
  grep -q "v6.4.0-iter-unramified-semistable-real" "$readme"
  grep -q "v6.4.1-iter-about-catchup-22572211" "$readme"
  grep -q "v6.5.0-iter-finite-flat-at-13-real" "$readme"
  grep -q "v6.5.1-iter-about-catchup-22582199" "$readme"
  grep -q "v6.6.0-iter-ribet-modularity-at-26-real" "$readme"
  grep -q "v6.6.1-iter-about-catchup-22587409" "$readme"
  grep -q "v6.7.0-iter-modular-lifting-at-26-real" "$readme"
  grep -q "v6.7.1-iter-about-catchup-22592524" "$readme"
  grep -q "v6.8.0-iter-exists-newform-level-2-real" "$readme"
  grep -q "v6.8.1-iter-about-catchup-22602899-relook" "$readme"
  grep -q "v6.9.0-iter-beal-forall-closed-real" "$readme"
  grep -q "v6.9.1-iter-about-catchup-22611775-relook" "$readme"
  grep -q "v7.0.0-iter-beal-forall-none-real" "$readme"
  grep -q "v7.0.1-iter-about-catchup-22618433-relook" "$readme"
  grep -q "v7.1.0-iter-beal-forall-kernel-separated-none-real" "$readme"
  grep -q "v7.1.1-iter-about-catchup-22632209-relook" "$readme"
  grep -q "v7.1.2-iter-readme-uniform-opera-links" "$readme"
  grep -q "v7.1.3-iter-beal-not-route-e-corrected" "$readme"
  grep -q "v7.2.0-step1-true-conductor-scaffold" "$readme"
  grep -q "v7.2.1-tate-filled" "$readme"
  grep -q "v7.3.0-ribet-rt-filled" "$readme"
  grep -q "v7.4.0-geometry-filled" "$readme"
  grep -q "v8.0.0-beal-forall-proof" "$readme"
  grep -q "v8.1.0-modular-implies-newform" "$readme"
  grep -q "v8.2.0-scheme-hecke-ribet" "$readme"
  grep -q "v8.3.0-explicit-X0-26" "$readme"
  grep -q "v8.4.0-formal-immersion" "$readme"
  grep -q "v8.5.0-cotangent-sheaf" "$readme"
  grep -q "v8.6.0-level-lowering-term" "$readme"
  grep -q "v8.7.0-ribet-q-mazur" "$readme"
  grep -q "v8.8.0-ribet-proof" "$readme"
  grep -q "v8.9.0-explicit-J0N" "$readme"
  grep -q "v8.10.0-frey-aq-pm1-real" "$readme"
  grep -q "v8.11.0-frey-ell-case" "$readme"
  grep -q "v8.12.0-fermat-four-plus-RinfTinf-ell" "$readme"
  grep -q "v8.13.0-mixed-ell-plus-dirichlet" "$readme"
  grep -q "v8.14.0-mixed-odd-A" "$readme"
  grep -q "v8.15.0-dirichlet-up-to-1000" "$readme"
  grep -q "v8.16.0-q2-table-100M" "$readme"
  grep -q "v8.17.0-twaux-26-and-10000" "$readme"
  grep -q "v8.18.0-product" "$readme"
  grep -q "v8.19.0-ExistsNewformLevel2" "$readme"
  grep -q "v8.19.1-beal-4-13-13-size" "$readme"
  grep -q "v8.19.2-C-ge-B+2" "$readme"
done
test -f docs/assets/v6.7.0/ribet_26_to_2.jpg
test -f docs/assets/v6.7.0/ribet_26_to_2.png
test -f docs/assets/v6.7.0/ribet_26_to_2.webp
test -f docs/assets/v6.7.0/tw_qn_infinite_family.jpg
test -f docs/assets/v6.7.0/tw_qn_infinite_family.png
test -f docs/assets/v6.7.0/tw_qn_infinite_family.webp
test -f docs/assets/v6.7.0/galois_token.jpg
test -f docs/assets/v6.7.0/galois_token.png
test -f docs/assets/v6.7.0/galois_token.webp
grep -q 'og:image" content="https://davidfox998.github.io/beal-level-26-foundations/assets/v6.7.0/ribet_26_to_2.jpg"' \
  docs/index.html
grep -q 'og:image:type" content="image/jpeg"' docs/index.html
grep -q 'assets/v6.7.0/ribet_26_to_2.jpg' docs/facebook-share.json
grep -q 'image/jpeg' docs/facebook-share.json
test ! -e extensions/facebook
test ! -e docs/images/797726399_1063690106418837_5544926896290683567_n.webp
grep -q "assets/v6.7.0/ribet_26_to_2.jpg" docs/About.md
grep -q "assets/v6.7.0/tw_qn_infinite_family.jpg" docs/About.md
grep -q "assets/v6.7.0/galois_token.jpg" docs/About.md
grep -q "assets/v6.7.0/ribet_26_to_2.jpg" docs/Final/FINAL.md
grep -q "assets/v6.7.0/tw_qn_infinite_family.jpg" docs/Final/FINAL.md
grep -q "assets/v6.7.0/galois_token.jpg" docs/Final/FINAL.md
grep -q "docs/assets/v6.7.0/ribet_26_to_2.jpg" README.md
grep -q "docs/assets/v6.7.0/tw_qn_infinite_family.jpg" README.md
grep -q "docs/assets/v6.7.0/galois_token.jpg" README.md
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  sagemath/README.md
grep -qi "genuine cohomological 2-Selmer" \
  lean/BealLevel26Foundations/Jacobian/README.md
grep -q "scheme-theoretic" \
  lean/BealLevel26Foundations/Jacobian/README.md
grep -q "Jacobian/" README.md
grep -q "FreyCurveExists" README.md
grep -q "LevelLowering_26" README.md
grep -q "v1.0.1-computable" CITATION.cff
grep -q "cohomological 2-Selmer" README.md

if grep -RInE \
  --exclude-dir=.git \
  --exclude-dir=.lake \
  --exclude-dir=.cache \
  '^[[:space:]]*(sorry|admit)([[:space:]]|$)' \
  --include='*.lean' .; then
  echo "FAIL: unfinished Lean declaration found"
  exit 1
fi

while IFS= read -r line; do
  case "$line" in
    *Modularity/FreyModularity_13.lean:*axiom[[:space:]]frey_modular_13*)
      ;;
    *Modularity/RibetLevelLowering_26.lean:*axiom[[:space:]]ribet_level_lowering_26*)
      ;;
    *)
      echo "FAIL: unexpected axiom: $line"
      exit 1
      ;;
  esac
done < <(grep -RInE \
  --exclude-dir=.git \
  --exclude-dir=.lake \
  --exclude-dir=.cache \
  '^[[:space:]]*axiom[[:space:]]+' \
  --include='*.lean' . || true)

while IFS= read -r line; do
  case "$line" in
    *Modularity/RibetLevelLowering_26.lean:*ribet_secured_by_certs*)
      ;;
    *)
      echo "FAIL: unexpected True := : $line"
      exit 1
      ;;
  esac
done < <(grep -RInE \
  --exclude-dir=.git \
  --exclude-dir=.lake \
  --exclude-dir=.cache \
  ':[[:space:]]*True[[:space:]]*:=' \
  --include='*.lean' . || true)

grep -q "def coefficientMatrix" lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "def BinaryQuartic.hasFpPointForTwist" \
  lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "theorem M3_eq" lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "theorem M3_det_nonzero" lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "theorem all_80_bad_prime_checks_pass" \
  lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "theorem finiteCandidateAudit_not_singleton" \
  lean/BealLevel26Foundations/FiniteEvidence.lean
grep -q "theorem ledger_byteForByte" \
  lean/BealLevel26Foundations/CoefficientLedger_26.lean
grep -q "theorem det_ledgerM3_ne_zero" \
  lean/BealLevel26Foundations/M3_Explicit.lean
grep -q "theorem finite_checks_at_2_and_13" \
  lean/BealLevel26Foundations/FiniteChecks_26.lean
grep -q "theorem certifiedDecompositionDimension_eq_two" \
  lean/Beal/Foundations/J0_26_Decomp.lean
grep -q "theorem certifiedDecomposition_two_distinct_newforms" \
  lean/Beal/Foundations/J0_26_Decomp.lean
grep -q "theorem qexp26a1_prefix_eq_ledger" \
  lean/Beal/Foundations/J0_26_Decomp.lean
grep -q "theorem qexp26b1_prefix_eq_ledger" \
  lean/Beal/Foundations/J0_26_Decomp.lean
grep -q "theorem certifiedJ0Dimension26_eq_two" \
  lean/Beal/Foundations/J0DecompositionCertificate.lean
grep -q "theorem certifiedM3_eq" \
  lean/Beal/Foundations/FormalImmersionM3.lean
grep -q "theorem certifiedM3_det" \
  lean/Beal/Foundations/FormalImmersionM3.lean
grep -q "theorem certifiedM3_eq_ledgerM3" \
  lean/Beal/Foundations/FormalImmersionM3.lean
grep -q "theorem certifiedM3_eq_ledgerM3" \
  lean/Beal/Foundations/FormalImmersionM3Certificate.lean
grep -q "theorem certifiedM3_det_nonzero" \
  lean/Beal/Foundations/FormalImmersionM3Certificate.lean

grep -q 'roots := #\[`BealLevel26Foundations, `Beal\]' lakefile.lean
grep -q 'roots := #\[`BealLevel26Foundations.Scaffold\]' lakefile.lean
grep -q 'roots := #\[`BealLevel26Foundations.Real\]' lakefile.lean
grep -q 'roots := #\[`BealLevel26Foundations.Beal.FullProof\]' lakefile.lean
grep -q "structure PrimitiveBealTriple" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem frey_Delta_of_equation" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem pairwise_coprime" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem odd_prime_not_dvd_c4" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem true_gcd_pairwise" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem tate_odd_prime" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem tate_two" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "def kodairaTate" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "def conductorExponentTate" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem frey_minimal_model_at_odd_prime" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem frey_conductor_exponent_one_odd" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem frey_conductor_two" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "theorem frey_global_conductor" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "structure FreyTwoAdicExponentOneCertificate" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "structure FreyTwoAdicConductorCertificate" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.TrueConductor" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.ModularityRibet" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.GeometryBridge" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.BealForallProof" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.ModularImpliesNewform" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.GeometryScheme" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.HeckeAlgebra" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.RibetFunctor" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.X0_26_Model" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.HeckeAction" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.LevelLowering" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "import BealLevel26Foundations.Beal.FullProof.RibetMazur" \
  lean/BealLevel26Foundations/Beal/FullProof.lean
grep -q "theorem wiles_modularity_Frey" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem ribet_level_lowering_general" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem ribet_level_quotient" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "def TW_primes_Q" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem TW_Q_infinite" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem TW_q53_mod13" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem TW_q677_mod169" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "abbrev HeckeAlgebra_26" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "structure TaylorWilesPatchingData" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "def R_T_scaffold" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem localizedRankOne_from_Patching" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem S2_Gamma0_2_zero" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem no_newform_level2" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem ribet_step_2_contradiction" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean
grep -q "theorem J0_26_dim" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean
grep -q "theorem J0_26_isogeny" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean
grep -q "theorem PicardAbelJacobiIdentification_26" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean
grep -q "theorem formal_immersion_X0_26_to_J0_26_at_2" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean
grep -q "theorem no_noncuspidal_Q_points" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean
grep -q "theorem GeometryBridge" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean
if grep -q "import BealLevel26Foundations.Beal.FullProof.ModularityRibet" \
    lean/BealLevel26Foundations.lean \
    lean/BealLevel26Foundations/Beal/BealForall.lean \
    lean/BealLevel26Foundations/Chain/BealForallInKernel.lean \
    lean/BealLevel26Foundations/Chain/PathLock.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: none chain must not import ModularityRibet"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Beal.FullProof.GeometryBridge" \
    lean/BealLevel26Foundations.lean \
    lean/BealLevel26Foundations/Beal/BealForall.lean \
    lean/BealLevel26Foundations/Chain/BealForallInKernel.lean \
    lean/BealLevel26Foundations/Chain/PathLock.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: none chain must not import GeometryBridge"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Beal.FullProof.BealForallProof" \
    lean/BealLevel26Foundations.lean \
    lean/BealLevel26Foundations/Beal/BealForall.lean \
    lean/BealLevel26Foundations/Chain/BealForallInKernel.lean \
    lean/BealLevel26Foundations/Chain/PathLock.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: none chain must not import BealForallProof"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Beal.FullProof.ModularImpliesNewform" \
    lean/BealLevel26Foundations.lean \
    lean/BealLevel26Foundations/Beal/BealForall.lean \
    lean/BealLevel26Foundations/Chain/BealForallInKernel.lean \
    lean/BealLevel26Foundations/Chain/PathLock.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: none chain must not import ModularImpliesNewform"
  exit 1
fi
if grep -E -q "import BealLevel26Foundations.Beal.FullProof.(GeometryScheme|HeckeAlgebra|RibetFunctor|X0_26_Model|HeckeAction|LevelLowering|RibetMazur|TWPrimes|TWPrimesPratt|TWPrimesQ2|TWAuxEllFixed|X0_2_Genus|Beal_4_13_13_Size_Table)" \
    lean/BealLevel26Foundations.lean \
    lean/BealLevel26Foundations/Beal/BealForall.lean \
    lean/BealLevel26Foundations/Chain/BealForallInKernel.lean \
    lean/BealLevel26Foundations/Chain/PathLock.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: none chain must not import GeometryScheme / HeckeAlgebra / RibetFunctor / X0_26_Model / HeckeAction / LevelLowering / RibetMazur / TWPrimes / TWPrimesPratt / TWPrimesQ2 / TWAuxEllFixed / X0_2_Genus / Beal_4_13_13_Size_Table"
  exit 1
fi
if grep -E -q "import BealLevel26Foundations.Beal_4_13_13_Size" \
    lean/BealLevel26Foundations.lean \
    lean/BealLevel26Foundations/Beal/BealForall.lean \
    lean/BealLevel26Foundations/Chain/BealForallInKernel.lean \
    lean/BealLevel26Foundations/Chain/PathLock.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallNoneReal.lean \
    lean/BealLevel26Foundations/GaloisRep/GaloisBealForallClosedReal.lean \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: none chain must not import size tables"
  exit 1
fi
grep -q "def X0_26_f" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "def cotangent_Z" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "def cotangent_Z2" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "def cotangent_Z3" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "theorem formal_immersion_at_2" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "theorem formal_immersion_at_3" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "theorem X0_26_Q_points_cusps_model_real" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "theorem cotangent_Z3_det_isUnit" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "theorem cotangent_Z2_det_not_unit" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "abbrev coordinateRing_X0_26" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "abbrev kaehlerDifferentials_X0_26" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "theorem hyperelliptic_kaehler_relation" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "def cotangentSheaf_X0_26" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "theorem cotangent_Z3_is_unit_sheaf" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "def basis_H0_Omega1" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "def HeckeOperator_Tq_coeff" \
  lean/BealLevel26Foundations/Beal/FullProof/HeckeAction.lean
grep -q "theorem R_inf_eq_T_inf_patched" \
  lean/BealLevel26Foundations/Beal/FullProof/HeckeAction.lean
grep -q "theorem level_lowering_to_2" \
  lean/BealLevel26Foundations/Beal/FullProof/LevelLowering.lean
grep -q "def Frey_GaloisRep" \
  lean/BealLevel26Foundations/Beal/FullProof/LevelLowering.lean
grep -q "theorem level_lowering_to_2_term" \
  lean/BealLevel26Foundations/Beal/FullProof/LevelLowering.lean
grep -q "theorem beal_positive_bases" \
  lean/BealLevel26Foundations/Beal/FullProof/LevelLowering.lean
grep -q "theorem beal_positive_bases_unconditional" \
  lean/BealLevel26Foundations/Beal/FullProof/LevelLowering.lean
grep -q "def q_expansion_26a1" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def q_expansion_26b1" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem mazur_principle_step" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem ribet_iterated" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def ribet_iterated_arrow" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_from_ribet" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def HeckeAction_N" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem mazur_step_real" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem ribet_iterated_real" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def ModularImpliesLevel2Newform_real" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_from_ribet_real" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "structure X0_N_Model" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "structure J0_N_Model" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def HeckeAction_N_real" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem frey_a_q_is_pm1" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem mazur_step_real_fixed" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem ribet_iterated_real_fixed" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_from_ribet_real_fixed" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def J0_N_real" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem frey_a_q_real" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem frey_rho_unramified_iff_13_dvd_vqDelta" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def Frey13Case" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def odd_q_divisors_with_13dvd" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def FreyEllCase5" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def FreyEllCase5Weak" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def ell_of_q" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def HeckeAction_N_real_ell" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem frey_a_q_real_ell" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem frey_rho_unramified_iff_ell_dvd_vqDelta" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem trace_eq_pm_qplus1_when_unramified" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem mazur_step_ell" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem ribet_iterated_ell_case" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem N_div_Prod_eq_2_of_FreyEllCase5" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_from_ribet_ell_case" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem ell_of_q_dvd_vqDelta" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem fermat_four_lemma" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def FermatFourCase" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def FreyEllCase5Complete" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def find_prime_congruent_one_mod" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def HeckeAction_N_real_ell_upgraded" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem mazur_step_real_ell_upgraded" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem ribet_iterated_ell_upgraded" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_from_ribet_ell_upgraded" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_pow2_exponents" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem not_FreyEllCase5_of_exp_four_reduced" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def FreyEllCase5Mixed" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "structure TWAuxEllFixed" \
  lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixedCore.lean
grep -q "def find_prime_congruent_one_mod_explicit" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_pow2_base" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem mixed_covers_4_13_13" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem thirteen_dvd_Delta_of_mixed_pow2_A" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem ribet_iterated_ell_mixed" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_from_ribet_ell_mixed" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem exists_prime_one_mod_ell_listed" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem mod_pow4_odd" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem mod_pow13_odd" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_4_13_13_mod8" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_4_13_13_mod13" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem not_beal_4_13_13_of_A_eq_one" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem FreyEllCase5Mixed_4_13_13_iff_pow2_A" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def beal_4_13_13_size" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem not_forall_pow13_mod8" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem exists_prime_one_mod_ell_all" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean
grep -q "def InTWEll1000" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean
grep -q "theorem Q1_not_dvd_N_of_Q1_gt_N" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean
grep -q "theorem exists_prime_one_mod_ell_sq_all" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean
grep -q "def find_next_prime_one_mod_gt_exists" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean
grep -q "theorem prime_of_pratt" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimesPratt.lean
grep -q "theorem q2_witness_919" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimesQ2_901_1000.lean
grep -q "def TWAuxEllFixed.of5_26" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def TWAuxEllFixed.of7_26" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def TWAuxEllFixed.of5_26_gt" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def TWAuxEllFixed.of5_10000" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def TWAuxEllFixed_inhabited_for_every_ell_le_1000" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def primes_le_1000" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean
grep -q "def next_Q1_gt_N" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean
grep -q "def InTWEll1000_complete" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimes.lean
grep -q "theorem TWAuxEllFixedExists_26_all" \
  lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed.lean
grep -q "theorem TWAuxEllFixedExists_10000_all" \
  lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed.lean
grep -q "theorem TWAuxEllFixedExists_all_N_le_10000" \
  lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed.lean
grep -q "theorem TWAuxEllFixed_inhabited_for_every_ell_le_1000_product" \
  lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed.lean
grep -q "def of_ℓ_N_product" \
  lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed.lean
grep -q "def TWAuxEllFixed.of_N_le" \
  lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixedCore.lean
grep -q "def genus_X0_2_rat" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_2_Genus.lean
grep -q "theorem ExistsNewformLevel2_eq_zero_ne_zero" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_2_Genus.lean
grep -q "inductive BealAArm" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem beal_odd_A_ge3_not_mixed" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def beal_from_ribet_upside_down" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def beal_mixed_pow2_implies_level_2_newform" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem C13_sub_B13_ge_13_mul_B_pow_12" \
  lean/BealLevel26Foundations/Beal/FullProof/Beal_4_13_13_Size_Table.lean
grep -q "theorem beal_4_13_13_size_lower_bound" \
  lean/BealLevel26Foundations/Beal/FullProof/Beal_4_13_13_Size_Table.lean
grep -q "theorem beal_4_13_13_size_B_le_100_C_succ" \
  lean/BealLevel26Foundations/Beal/FullProof/Beal_4_13_13_Size_Table.lean
grep -q "def zsigmondy_13" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def beal_odd_A_ge3_size_gap" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "def beal_size_B_le_100_table" \
  certs/Beal_4_13_13_Size_Table.lean
grep -q "def beal_4_13_13_C_eq_B_plus_1_diff" \
  certs/Beal_4_13_13_Size_Table.lean
grep -q "theorem C13_sub_B13_ge_26_mul_B_pow_12_of_C_ge_B_plus_2" \
  lean/BealLevel26Foundations/Beal_4_13_13_Size_C_ge_B_plus_2.lean
grep -q "theorem beal_4_13_13_A_pow4_ge_26_mul_B12_of_C_ge_B_plus_2" \
  lean/BealLevel26Foundations/Beal_4_13_13_Size_C_ge_B_plus_2.lean
grep -q "theorem size_table_C_eq_B_plus_2_lower_bound_B_le_100" \
  lean/BealLevel26Foundations/Beal_4_13_13_Size_C_ge_B_plus_2.lean
grep -q "def beal_4_13_13_size_C_eq_B_plus_2_full_table" \
  certs/Beal_4_13_13_Size_C_ge_B_plus_2_Table.lean
grep -q "def zsigmondy_13" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
grep -q "theorem primes5to100_eq_Icc_filter" \
  lean/BealLevel26Foundations/Beal/FullProof/TWPrimes_5_100.lean
grep -q "def twaux_10000_941" \
  lean/BealLevel26Foundations/Beal/FullProof/TWAuxEllFixed_901_1000.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean
if grep -q "import BealLevel26Foundations.Beal.FullProof.X0_26_Model" \
    lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean; then
  echo "FAIL: RibetMazur must not import X0_26_Model"
  exit 1
fi
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/HeckeAction.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/LevelLowering.lean
grep -q "structure X0_26_Scheme" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean
grep -q "structure J0_26_Scheme" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean
grep -q "theorem PicardAbelJacobiScheme" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean
grep -q "def AbelJacobiMap" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean
grep -q "theorem formal_immersion_scheme_at_2" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean
grep -q "theorem X0_26_Q_points_cusps" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean
grep -q "def HeckeOperator_Tq" \
  lean/BealLevel26Foundations/Beal/FullProof/HeckeAlgebra.lean
grep -q "def HeckeAlgebra_T" \
  lean/BealLevel26Foundations/Beal/FullProof/HeckeAlgebra.lean
grep -q "def HeckeAlgebra_T_infinite_level" \
  lean/BealLevel26Foundations/Beal/FullProof/HeckeAlgebra.lean
grep -q "theorem R_inf_eq_T_inf" \
  lean/BealLevel26Foundations/Beal/FullProof/HeckeAlgebra.lean
grep -q "structure GaloisRepModularLevel" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetFunctor.lean
grep -q "theorem ribet_level_lowering_functor" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetFunctor.lean
grep -q "def ModularImpliesLevel2Newform_Real" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetFunctor.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/HeckeAlgebra.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/RibetFunctor.lean
grep -q "structure PositiveBealTriple" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "theorem sketch_fails_on_zero_one_counterexample" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "def ModularImpliesLevel2Newform" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "theorem beal_forall_proof_positive" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "theorem modular_implies_level2_arithmetic" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "theorem TW_Q_base_53" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "theorem TW_Q_base_677" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "def Gamma0_2" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "structure GaloisRepModular" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "theorem modular_implies_ribet_level_two" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean
grep -q "beal_forall_proof_positive" \
  lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean
grep -q "theorem sketch_fails_on_zero_one" \
  lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean
grep -q "theorem beal_forall_glue" \
  lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean
grep -q "theorem beal_forall_proof" \
  lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean
grep -q "theorem beal_forall_positive_of_newform_arrow" \
  lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean
grep -q "def ModularImpliesLevel2Newform" \
  lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean
grep -q "def beal_forall_from_Is13Case_sketch_stays_uninhabited" \
  lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean
if grep -nE \
    '^import[[:space:]]+(BealLevel26Foundations\.Beal\.BealForall|BealLevel26Foundations\.GaloisRep\.GaloisBealForallNoneReal|BealLevel26Foundations\.GaloisRep\.GaloisBealForallClosedReal|BealLevel26Foundations\.Chain\.PathLock|BealLevel26Foundations\.Chain\.BealForallInKernel|BealLevel26Foundations\.Mazur|BealLevel26Foundations\.RT\.PatchingWitnessReal|BealLevel26Foundations\.RT\.TaylorWilesScaffold)' \
    lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean \
    lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean \
    lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean \
    lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean \
    lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean \
    lean/BealLevel26Foundations/Beal/FullProof/HeckeAlgebra.lean \
    lean/BealLevel26Foundations/Beal/FullProof/RibetFunctor.lean \
    lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean \
    lean/BealLevel26Foundations/Beal/FullProof/HeckeAction.lean \
    lean/BealLevel26Foundations/Beal/FullProof/LevelLowering.lean \
    lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean; then
  echo "FAIL: FullProof Step 2/3/4/5/6/7 must not import none-chain / Forall / Mazur / none RT tokens"
  exit 1
fi
if grep -nE '^[[:space:]]*False\.elim|^[[:space:]]*exact[[:space:]]+False\.elim' \
    lean/BealLevel26Foundations/Beal/FullProof/ModularityRibet.lean \
    lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean \
    lean/BealLevel26Foundations/Beal/FullProof/GeometryBridge.lean \
    lean/BealLevel26Foundations/Beal/FullProof/BealForallProof.lean \
    lean/BealLevel26Foundations/Beal/FullProof/ModularImpliesNewform.lean \
    lean/BealLevel26Foundations/Beal/FullProof/GeometryScheme.lean \
    lean/BealLevel26Foundations/Beal/FullProof/HeckeAlgebra.lean \
    lean/BealLevel26Foundations/Beal/FullProof/RibetFunctor.lean \
    lean/BealLevel26Foundations/Beal/FullProof/X0_26_Model.lean \
    lean/BealLevel26Foundations/Beal/FullProof/HeckeAction.lean \
    lean/BealLevel26Foundations/Beal/FullProof/LevelLowering.lean \
    lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean \
    lean/BealLevel26Foundations/Beal/FullProof.lean; then
  echo "FAIL: FullProof track must not use False.elim"
  exit 1
fi

if grep -RInE \
  'frey_conductor_data|tate_step2_odd_prime_external' \
  lean/BealLevel26Foundations/Real/FreyWeierstrass.lean \
  lean/BealLevel26Foundations/Real/Conductor_26_Unconditional.lean \
  lean/BealLevel26Foundations/Frey/FreyConductorUnconditional_26.lean \
  lean/BealLevel26Foundations/Frey/Conductor_26_Unconditional.lean; then
  echo "FAIL: parent conductor axioms leaked into the real arithmetic module"
  exit 1
fi

grep -q "theorem freyCurve_c4" \
  lean/BealLevel26Foundations/Real/FreyWeierstrass.lean
grep -q "theorem freyCurve_c6" \
  lean/BealLevel26Foundations/Real/FreyWeierstrass.lean
grep -q "theorem freyCurve_discriminant" \
  lean/BealLevel26Foundations/Real/FreyWeierstrass.lean
grep -q "theorem oddPrimeMultiplicativeValuationInput26_values" \
  lean/BealLevel26Foundations/Frey/Conductor_26_Unconditional.lean
grep -q "theorem freyDiscriminantValuation26_pos" \
  lean/BealLevel26Foundations/Frey/Conductor_26_Unconditional.lean
grep -q "structure TateKodairaBoundary26" \
  lean/BealLevel26Foundations/Frey/Conductor_26_Unconditional.lean
grep -q "structure LevelLowering_26" \
  lean/BealLevel26Foundations/Ribet/LevelLowering_26.lean
grep -q "theorem LevelLowering_26.representation_data" \
  lean/BealLevel26Foundations/Ribet/LevelLowering_26.lean
grep -q "theorem LevelLowering_26.level_data" \
  lean/BealLevel26Foundations/Ribet/LevelLowering_26.lean
grep -q "theorem LevelLowering_26.lowering_relation" \
  lean/BealLevel26Foundations/Ribet/LevelLowering_26.lean
grep -q "theorem exactDivides_mul_self_of_not_dvd" \
  lean/BealLevel26Foundations/Ribet/LevelLowering_26.lean
grep -q "structure RibetTheoremBoundary26" \
  lean/BealLevel26Foundations/Ribet/LevelLowering_26.lean
if grep -q "def LevelLowering_26 : Prop" \
    lean/BealLevel26Foundations/Ribet/LevelLowering_26.lean; then
  echo "FAIL: LevelLowering_26 must be typed certificate data, not an opaque Prop"
  exit 1
fi
grep -q "structure J0_26_Q_RankZero26" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "structure FormalImmersionAtTwo26" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "structure X0_26_RationalPoints26" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "structure NoFreyPoint26" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "theorem FormalImmersionAtTwo26.input_certificate" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "theorem BealTheoremFromMazurChain26" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE 'decide' \
    lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean |
    grep -E 'rankZero|rationalPointsAreFourCusps|R[[:space:]]*=[[:space:]]*T'; then
  echo "FAIL: rank, cusps, or R=T must not be decided"
  exit 1
fi
grep -q "def PicardAbelJacobiIdentification_26" \
  lean/BealLevel26Foundations/Jacobian/PicardAbelJacobiIdentification_26.lean
grep -q "theorem qExpansion_cotangent_compatibility_of_picard_bridge" \
  lean/BealLevel26Foundations/Mazur/QExpansionCotangent_Real_26.lean
if grep -q "def PicardAbelJacobiIdentification_26" \
    lean/BealLevel26Foundations/Mazur/QExpansionCotangent_Real_26.lean; then
  echo "FAIL: PicardAbelJacobiIdentification_26 must live in Jacobian/, not QExpansionCotangent_Real_26"
  exit 1
fi
if grep -q "theorem picardAbelJacobiIdentification_26" \
    lean/BealLevel26Foundations/Mazur/QExpansionCotangent_Real_26.lean \
    lean/BealLevel26Foundations/Jacobian/PicardAbelJacobiIdentification_26.lean; then
  echo "FAIL: formal-coordinate model must not discharge the geometric Picard boundary"
  exit 1
fi
grep -q "def s1" lean/BealLevel26Foundations/Jacobian/J0_26_DecompActual.lean
grep -q "def s2" lean/BealLevel26Foundations/Jacobian/J0_26_DecompActual.lean
grep -q "theorem certifiedJ0_26_eq_26a_times_26b" \
  lean/BealLevel26Foundations/Jacobian/J0_26_DecompActual.lean
grep -q "theorem certifiedM3_eq" \
  lean/BealLevel26Foundations/Jacobian/J0_26_DecompActual.lean
grep -q "theorem certifiedM3_det" \
  lean/BealLevel26Foundations/Jacobian/J0_26_DecompActual.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/J0_26_DecompActual.lean
test -f lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean
grep -q "def sUnitsFromDecomposition" \
  lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean
grep -q "theorem sUnitAudit26_retains_all_eight" \
  lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean
grep -q "theorem sUnitAudit26_not_singleton" \
  lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean
grep -q "theorem sUnitAudit26_is_not_genuine_2Selmer" \
  lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean
grep -q "def MwrankCertificateSoundness_26" \
  lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean
grep -q "theorem MwrankCertificateSoundness_26.certified" \
  lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean
grep -q "remains future" \
  lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean
if grep -nE \
    'theorem[[:space:]]+(genuineCohomological2Selmer|twoSelmerIdentification|SelmerGroup_eq)' \
    lean/BealLevel26Foundations/Jacobian/TwoSelmer_vs_SUnits_26.lean; then
  echo "FAIL: must not identify the S-unit audit with genuine 2-Selmer"
  exit 1
fi
test -f lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "def cotangentInjective" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "theorem qExpansionM3_det_by_ring" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "theorem qExpansionM3_cotangent_injective" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "theorem cotangentMap_injective_at_two" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "theorem cotangentInjective_of_picard" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "def FormalImmersionAtTwo26.of_qExpansion" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "theorem FormalImmersionAtTwo26.of_qExpansion_replaces_premise" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "def formalImmersion_at_2_surjective_from_M3" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "theorem formalImmersion_at_2_surjective_from_M3.certified" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "completed local rings" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
grep -q "scheme-theoretic" \
  lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE 'decide' \
    lean/BealLevel26Foundations/Jacobian/FormalImmersionActual_26.lean |
    grep -E 'rationalPointsAreFourCusps|X0_26'; then
  echo "FAIL: X0(26)(Q) must not be decided"
  exit 1
fi
test -f lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean
grep -q "def displayedCusps26" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean
grep -q "def fourCuspsFromQExpansion" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean
grep -q "theorem fourCuspsFromQExpansion.certified" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean
grep -q "def X0_26_RationalPoints26.of_qExpansion" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean
grep -q "theorem X0_26_RationalPoints26.of_qExpansion_replaces_premise" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean
grep -q "Not a modular-curve" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE 'decide' \
    lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean |
    grep -E 'rationalPointsAreFourCusps|X0_26'; then
  echo "FAIL: X0(26)(Q) must not be decided"
  exit 1
fi
if grep -nE 'NoFreyPoint26[[:space:]]*(where|:|=)' \
    lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean; then
  echo "FAIL: NoFreyPoint26 must not be inhabited in the four-cusp file"
  exit 1
fi
if grep -nE 'J0_26_Q_RankZero26[[:space:]]*(where|:|=)|rankZero[[:space:]]*:=[[:space:]]*True|⟨[[:space:]]*True[[:space:]]*,[[:space:]]*trivial[[:space:]]*⟩' \
    lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean; then
  echo "FAIL: must not inhabit J0_26_Q_RankZero26 as True/trivial"
  exit 1
fi
test -f lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean
grep -q "def displayedTargetLevel26" \
  lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean
grep -q "def ribetExistenceFromQExpansion" \
  lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean
grep -q "theorem ribetExistenceFromQExpansion.certified" \
  lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean
grep -q "def ofBealFreyLowering" \
  lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean
grep -q "ExistsFreyWitness" \
  lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean
grep -q "Not a Mathlib Ribet" \
  lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE 'J0_26_Q_RankZero26[[:space:]]*(where|:|=)|rankZero[[:space:]]*:=[[:space:]]*True|⟨[[:space:]]*True[[:space:]]*,[[:space:]]*trivial[[:space:]]*⟩' \
    lean/BealLevel26Foundations/Ribet/RibetLoweringActual_26.lean; then
  echo "FAIL: must not inhabit J0_26_Q_RankZero26 as True/trivial"
  exit 1
fi
test -f lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean
grep -q "def fourCuspAbsencePackage" \
  lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean
grep -q "theorem fourCuspAbsencePackage.certified" \
  lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean
grep -q "def NoFreyPoint26.of_qExpansion" \
  lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean
grep -q "theorem NoFreyPoint26.of_qExpansion_replaces_premise" \
  lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean
grep -q "displayedCusps" \
  lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean
grep -q "Not from Ribet existence" \
  lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean
if grep -nE 'ofBealFreyLowering|ribetExistenceFromQExpansion' \
    lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean; then
  echo "FAIL: NoFreyPointActual_26 must prove absence, not Ribet existence"
  exit 1
fi
if grep -nE \
    'theorem[[:space:]]+(NoFreyPoint26\.not_exists|noNoncuspidalLevel26FreyPoint)|hGeomForbid_of_qExpansion' \
    lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean; then
  echo "FAIL: NoFreyPointActual_26 must not Lean-negate elliptic-j ExistsNoncuspidal"
  exit 1
fi
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE 'J0_26_Q_RankZero26[[:space:]]*(where|:|=)|rankZero[[:space:]]*:=[[:space:]]*True|⟨[[:space:]]*True[[:space:]]*,[[:space:]]*trivial[[:space:]]*⟩' \
    lean/BealLevel26Foundations/Ribet/NoFreyPointActual_26.lean; then
  echo "FAIL: must not inhabit J0_26_Q_RankZero26 as True/trivial"
  exit 1
fi
test -f lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
grep -q "def productRankZeroFromCertifiedFactors" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
grep -q "def J0_26_Q_RankZero26.of_qExpansion" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
grep -q "theorem J0_26_Q_RankZero26.of_qExpansion_replaces_premise" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
grep -q "MwrankCertificateSoundness_26" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
grep -q "sUnitAudit26_is_not_genuine_2Selmer" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
if grep -nE 'selmerGroup|IsDedekindDomain' \
    lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean; then
  echo "FAIL: rank-zero package must not use IsDedekindDomain.selmerGroup"
  exit 1
fi
if grep -nE 'rankZero[[:space:]]*:=[[:space:]]*True|⟨[[:space:]]*True[[:space:]]*,[[:space:]]*trivial[[:space:]]*⟩' \
    lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean; then
  echo "FAIL: must not inhabit J0_26_Q_RankZero26 as True/trivial"
  exit 1
fi
if grep -nE \
    'theorem[[:space:]]+(genuineCohomological2Selmer|twoSelmerIdentification|SelmerGroup_eq)' \
    lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean; then
  echo "FAIL: must not identify the S-unit audit with genuine 2-Selmer"
  exit 1
fi
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
grep -q "displayedTargetLevel" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "hGeomForbid" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "ExistsFreyWitness" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "hIdentify" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "¬ ExistsNoncuspidalLevel26FreyPoint" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "DisplayedX026PointKind" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "ellipticJ" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "fourCuspsForallCuspPoints" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "fourCuspsForallAllKinds_is_false" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "DisplayedX026CuspPoint" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "import BealLevel26Foundations.Descent.Selmer_26" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "def rankZero_unconditional" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "theorem rankZero_unconditional.certified" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "X026RationalPointsActual_26" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "computational boundary" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "def hGeomForbid : Option Prop" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "Mathlib has no \`SelmerGroup\`" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
grep -q "not a Lean Mordell--Weil theorem" \
  lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean
if grep -q "import BealLevel26Foundations.Jacobian.ColemanNonVanishing_26" \
    lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean; then
  echo "FAIL: EndgameScaffold must not import ColemanNonVanishing_26 (cycle)"
  exit 1
fi
if grep -nE \
    'def[[:space:]]+hGeomForbid[[:space:]]*:[[:space:]]*Prop[[:space:]]*:=' \
    lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean; then
  echo "FAIL: Option hGeomForbid must remain Option Prop, not the typed implication"
  exit 1
fi
test -f lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "import BealLevel26Foundations.Mazur.EndgameScaffold" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "structure hGeomForbid" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "def hGeomForbid_computational" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "theorem BealTheorem_Exponent13" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "theorem BealTheorem" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "hGeomForbid_typed" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "X026RationalPointsActual_26" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "computational boundary" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "MordellWeil.rank" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "SelmerGroup" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "hGeomForbid_typed_is_uninhabitable" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]*:' \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: full theorem BealTheorem must stay guarded by a hypothesis"
  exit 1
fi
if grep -nE \
    'fourCusps[[:space:]]*→[[:space:]]*¬[[:space:]]*ExistsNoncuspidal' \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean |
    grep -nE '^[[:space:]]*(def|theorem)[[:space:]]+hGeomForbid_computational'; then
  echo "FAIL: must not inhabit typed fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi
if grep -nE 'Prop[[:space:]]*:=[[:space:]]*True|:=[[:space:]]*trivial' \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: computational BealTheorem package must not be True/trivial"
  exit 1
fi
grep -q "import BealLevel26Foundations.Chain.FreyCurve_13_26" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "import BealLevel26Foundations.Chain.RationalPoints_26_FourCusps_26" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "def hGeomForbid_typed_computational" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "theorem hGeomForbid_typed_is_computationally_inhabited" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -qF "def hGeomForbid_typed_computational : Prop :=" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "X0_26_Q_four" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -qF "def BealTheorem_Exponent13_Full_package : Prop :=" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -qF "def BealTheorem_Exponent13_Full : Prop :=" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
if grep -nE 'BealTheorem_Exponent13_Full[[:space:]]*:[[:space:]]*∀' \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: BealTheorem_Exponent13_Full must not claim ∀ A B C Fermat/Beal"
  exit 1
fi
grep -qF "def FreyLevel26 : Prop := 2 * 13 = 26" \
  lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
grep -qF "def FreyToX0_26 : Prop := 26 = 2 * 13" \
  lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
grep -q "theorem freyLevel26_computational" \
  lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
grep -q "theorem freyToX0_26_computational" \
  lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
grep -q "no Ribet" \
  lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
grep -q "def X0_26_Q_four" \
  lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
grep -q "def X0_26_Q_eq_fourCusps" \
  lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
grep -q "def fourCuspsList" \
  lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
grep -q "theorem fourCuspsList_complete_computational" \
  lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
grep -q "def hGeomForbid_typed_closed : Prop" \
  lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
grep -q "theorem hGeomForbid_typed_is_now_computationally_inhabitable" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
if grep -nE \
    'hGeomForbid_typed_closed[[:space:]]*:[[:space:]]*\(?fourCusps[[:space:]]*→' \
    lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: hGeomForbid_typed_closed must stay a Prop package, not fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi
if grep -nE '^[[:space:]]*False\.elim|^[[:space:]]*exact[[:space:]]+False\.elim' \
    lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: must not inhabit typed fourCusps → ¬ ExistsNoncuspidal by contradiction"
  exit 1
fi
grep -q "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260" \
  lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
grep -q "Not \`X₀(26)(ℚ)" \
  lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
grep -q "hGeomForbid_typed_is_uninhabitable" \
  lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
if grep -nE 'Prop[[:space:]]*:=[[:space:]]*True|:=[[:space:]]*trivial' \
    lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean \
    lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean; then
  echo "FAIL: Chain packages must not be True/trivial"
  exit 1
fi
if grep -nE \
    '^[[:space:]]*(def|theorem)[[:space:]]+hGeomForbid[[:space:]]' \
    lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean \
    lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean; then
  echo "FAIL: must not inhabit typed hGeomForbid fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean \
    lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Mazur.BealTheoremFromMazurChain26" \
    lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean; then
  echo "FAIL: RationalPoints_26_FourCusps_26 must not import BealTheoremFromMazurChain26 (cycle)"
  exit 1
fi
grep -qF "def BealExponent13_Iter_Package : Prop :=" \
  lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
grep -q "theorem BealExponent13_Iter_Package.certified" \
  lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
grep -qF "def BealExponent13_Final_Package : Prop :=" \
  lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
grep -q "theorem BealExponent13_Final_Package.certified" \
  lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
grep -q "Deprecated alias of \`BealExponent13_Iter_Package\`" \
  lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
grep -q "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260" \
  lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
if grep -nE 'BealExponent13_Final[[:space:]]*:[[:space:]]*∀' \
    lean/BealLevel26Foundations/Final/BealExponent13_Final.lean; then
  echo "FAIL: BealExponent13_Final_Package must not claim ∀ A B C"
  exit 1
fi
if grep -nE 'Prop[[:space:]]*:=[[:space:]]*True|:=[[:space:]]*trivial' \
    lean/BealLevel26Foundations/Final/BealExponent13_Final.lean; then
  echo "FAIL: Final package must not be True/trivial"
  exit 1
fi
if grep -nE '^[[:space:]]*False\.elim|^[[:space:]]*exact[[:space:]]+False\.elim' \
    lean/BealLevel26Foundations/Final/BealExponent13_Final.lean; then
  echo "FAIL: Final package must not inhabit a forall by contradiction"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Final.BealExponent13_Final" \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: BealTheoremFromMazurChain26 must not import Final (cycle)"
  exit 1
fi
grep -q "import BealLevel26Foundations.Mazur.BealTheoremFromMazurChain26" \
  lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
grep -q "import BealLevel26Foundations.Modularity.RibetLevelLowering_26" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "import BealLevel26Foundations.Modularity.FreyModularity_13" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "import BealLevel26Foundations.Chain.X0_26_Point" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "theorem chain_secure" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "modularity_ribet_chain" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
if grep -q "import BealLevel26Foundations.Mazur.BealTheoremFromMazurChain26" \
    lean/BealLevel26Foundations/Chain/X0_26_Point.lean \
    lean/BealLevel26Foundations/Modularity/FreyModularity_13.lean \
    lean/BealLevel26Foundations/Modularity/RibetLevelLowering_26.lean; then
  echo "FAIL: modularity / X0_26_Point must not import BealTheoremFromMazurChain26 (cycle)"
  exit 1
fi
grep -q "structure X0_26_Point_Raw" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -qF "def fourCuspsList : List Nat :=" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "def isCuspPoint" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "def X0_26_Q" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -qF "{P | P.label ∈ fourCuspsList}" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "theorem X0_26_Q_eq_fourCuspsList" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "def x0_26_four_cusps_cert" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "SECURED BY" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "theorem X0_26_Q_four_cusps" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
echo "----- certs/pari_x0_26_four_cusps.json -----"
cat certs/pari_x0_26_four_cusps.json
echo "----- end certs/pari_x0_26_four_cusps.json -----"
cat certs/pari_x0_26_four_cusps.json | grep -q "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260"
python3 - <<'PY'
import json
from pathlib import Path
j = json.loads(Path("certs/pari_x0_26_four_cusps.json").read_text())
sha = "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260"
if j.get("SHA") != sha:
    raise SystemExit(f"FAIL: SHA {j.get('SHA')!r} != {sha}")
if j.get("fourCusps") != [1, 2, 13, 26]:
    raise SystemExit(f"FAIL: fourCusps {j.get('fourCusps')!r} != [1, 2, 13, 26]")
if j.get("M3_det") != 2:
    raise SystemExit(f"FAIL: M3_det {j.get('M3_det')!r} != 2")
if j.get("frey_level") != "2*13=26":
    raise SystemExit(f"FAIL: frey_level {j.get('frey_level')!r}")
if j.get("26a1", {}).get("ainv") != [1, 0, 1, -5, -8] or j.get("26a1", {}).get("disc") != -17576:
    raise SystemExit(f"FAIL: 26a1 {j.get('26a1')!r}")
if j.get("26b1", {}).get("ainv") != [1, -1, 1, -3, 3] or j.get("26b1", {}).get("disc") != -1664:
    raise SystemExit(f"FAIL: 26b1 {j.get('26b1')!r}")
if "SHA_cert" in j or "curve_26a1" in j or "curve_26b1" in j:
    raise SystemExit("FAIL: lock JSON must use keys 26a1/26b1/SHA")
for key in ("26a1", "26b1"):
    if j[key].get("sel2") != 1:
        raise SystemExit(f"FAIL: {key} sel2 {j[key].get('sel2')!r} != 1")
    if j[key].get("rank") != 0:
        raise SystemExit(f"FAIL: {key} rank {j[key].get('rank')!r} != 0")
img = Path("docs/images/2-descent-level-26-26a1-26b1.webp")
if not img.is_file():
    raise SystemExit("FAIL: missing docs/images/2-descent-level-26-26a1-26b1.webp")
if img.stat().st_size < 300000:
    raise SystemExit(f"FAIL: 2-descent image too small ({img.stat().st_size} bytes)")
print("verified pari_x0_26_four_cusps.json SHA + fourCuspsList")
print("verified v4.12.0-iter-verify-plus image + JSON keys + Sel2")
PY
grep -q "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260" \
  certs/pari_x0_26_four_cusps.json
grep -qE '"fourCusps":[[:space:]]*\[1,[[:space:]]*2,[[:space:]]*13,[[:space:]]*26\]' \
  certs/pari_x0_26_four_cusps.json
test ! -e docs/images/797726399_1063690106418837_5544926896290683567_n.webp
test ! -f docs/images/797726399_1063690106418837_5544926896290683567_n.webp
grep -q "PARI 2-Descent Certificates" README.md
grep -q "docs/images/2-descent-level-26-26a1-26b1.webp" README.md
grep -q "def fourCuspsList" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -qE '\[1,[[:space:]]*2,[[:space:]]*13,[[:space:]]*26\]' \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "theorem X0_26_Q_eq_fourCuspsList" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -A3 "theorem X0_26_Q_eq_fourCuspsList" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean | grep -q rfl
# v4.13.1: do not grep unconfirmed Zenodo version-DOI record ids.
# v4.30.0: lock confirmed 22452680 + 22456594 so stale README badges fail.
grep -q "2-descent-level-26-26a1-26b1.webp" docs/README.md
grep -q "2-descent-level-26-26a1-26b1.webp" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
if grep -nE 'SHA_cert|curve_26a1|curve_26b1' certs/pari_x0_26_four_cusps.json; then
  echo "FAIL: lock JSON must not use SHA_cert or curve_26a1/curve_26b1"
  exit 1
fi
if grep -nE -- '-1216|-1831858856' certs/pari_x0_26_four_cusps.json; then
  echo "FAIL: lock JSON must use certified discriminants -17576/-1664"
  exit 1
fi
if grep -nE '∨[[:space:]]*True|or[[:space:]]+True' \
    lean/BealLevel26Foundations/Chain/X0_26_Point.lean; then
  echo "FAIL: X0_26_Q must not use a True disjunct"
  exit 1
fi
grep -q "def ExistsNoncuspidal_26" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "structure FreyCurve13" \
  lean/BealLevel26Foundations/Modularity/FreyModularity_13.lean
grep -q "axiom frey_modular_13" \
  lean/BealLevel26Foundations/Modularity/FreyModularity_13.lean
grep -q "COMPUTATIONAL ASSUMPTION" \
  lean/BealLevel26Foundations/Modularity/FreyModularity_13.lean
grep -q "def freyLevel26_computational" \
  lean/BealLevel26Foundations/Modularity/FreyModularity_13.lean
grep -q "def frey_conductor_26" \
  lean/BealLevel26Foundations/Modularity/FreyModularity_13.lean
grep -q "axiom ribet_level_lowering_26" \
  lean/BealLevel26Foundations/Modularity/RibetLevelLowering_26.lean
grep -q "PLACEHOLDER AXIOM" \
  lean/BealLevel26Foundations/Modularity/RibetLevelLowering_26.lean
grep -q "COMPUTATIONAL ASSUMPTION" \
  lean/BealLevel26Foundations/Modularity/RibetLevelLowering_26.lean
grep -q "theorem ribet_secured_by_certs" \
  lean/BealLevel26Foundations/Modularity/RibetLevelLowering_26.lean
grep -q "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260" \
  lean/BealLevel26Foundations/Modularity/RibetLevelLowering_26.lean
if grep -nE '^[[:space:]]*False\.elim|^[[:space:]]*exact[[:space:]]+False\.elim' \
    lean/BealLevel26Foundations/Chain/X0_26_Point.lean \
    lean/BealLevel26Foundations/Modularity/FreyModularity_13.lean \
    lean/BealLevel26Foundations/Modularity/RibetLevelLowering_26.lean \
    lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean \
    lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean; then
  echo "FAIL: modularity scaffold must not use False.elim"
  exit 1
fi
grep -q "frey_modular_13" \
  lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean
grep -q "ribet_level_lowering_26" \
  lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean
grep -q "X0_26_Q_four_cusps" \
  lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean
grep -q "theorem contradiction_from_ribet" \
  lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean
grep -q "theorem beal_exponent13_from_ribet" \
  lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean
grep -q "STILL NOT ∀ N" \
  lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean
grep -q "import BealLevel26Foundations.Mazur.BealExponent13_Contradiction" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "beal_exponent13_from_ribet" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
if grep -q "import BealLevel26Foundations.Final" \
    lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean; then
  echo "FAIL: Contradiction must not import Final (cycle)"
  exit 1
fi
if grep -q "import BealLevel26Foundations.Mazur.BealExponent13_Contradiction" \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: BealTheoremFromMazurChain26 must not import Contradiction (cycle)"
  exit 1
fi
if grep -nE 'BealExponent13_Contradiction[[:space:]]*:[[:space:]]*∀' \
    lean/BealLevel26Foundations/Mazur/BealExponent13_Contradiction.lean \
    lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean; then
  echo "FAIL: Contradiction must not claim ∀ A B C"
  exit 1
fi
grep -qF "def fourCuspsList : List Nat :=" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "structure DisplayedX026CuspPoint" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "DisplayedX026CuspPoint" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "def fourCuspsForallCuspPoints" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "def ExistsNoncuspidal_26" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "def fourCuspsList_complete_computational" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "def hGeomForbid_typed_true" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "#check hGeomForbid_typed_true" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "#check hGeomForbid_typed_is_uninhabitable" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -qF "def BealTheorem_Exponent13_Typed : Prop :=" \
  lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
grep -q "theorem BealTheorem_Exponent13_Typed.certified" \
  lean/BealLevel26Foundations/Final/BealExponent13_Final.lean
if grep -nE 'BealTheorem_Exponent13_Typed[[:space:]]*:[[:space:]]*∀' \
    lean/BealLevel26Foundations/Final/BealExponent13_Final.lean; then
  echo "FAIL: BealTheorem_Exponent13_Typed must not claim ∀ A B C"
  exit 1
fi
grep -q "import BealLevel26Foundations.Final.BealExponent13_Final" \
  lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
grep -qF "def BealExponent13_Iter_Typed_And_Package : Prop :=" \
  lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
grep -q "theorem BealExponent13_Iter_Typed_And_Package.certified" \
  lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
grep -qF "def BealTheorem_Exponent13_Forall_Computational : Prop :=" \
  lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
grep -q "theorem BealTheorem_Exponent13_Forall_Computational.certified" \
  lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
grep -q "beal_forall_from_ribet" \
  lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
grep -q "beal_prime_divisor_13" \
  lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
grep -q "beal_forall_reduces_to_exponent13" \
  lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
grep -q "beal_prime_divisor_13" docs/Final/BealExponent13_Forall.md
grep -q "v4.31.0" docs/Final/BealExponent13_Forall.md
grep -q "Reduction to p=13" docs/Final/BealExponent13_Forall.md
grep -q "certified_from_forall" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "typed_and_forall" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "certified_typed_and_forall" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "def final_bridge" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "def final_package" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "beal_forall_eq_exponent13_bridge" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "beal13_forall_bridge_triple" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "typed_and_forall" docs/BealExponent13_Iter_Package.md
grep -q "final_package" docs/BealExponent13_Iter_Package.md
grep -q "beal13_forall_bridge_triple" docs/BealExponent13_Iter_Package.md
grep -q "final_package" README.md
grep -q "final_package" docs/README.md
grep -q "beal13_forall_bridge_triple" README.md
grep -q "beal13_forall_bridge_triple" docs/README.md
grep -q "22452680" README.md
grep -q "22456594" README.md
grep -q "X0_26_cusps" README.md
grep -q "beal_forall_eq_exponent13_bridge" \
  lean/BealLevel26Foundations/Final/BealExponent13_Iter_Package.lean
grep -q "X0_26_cusps" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "theorem X0_26_Q_eq_cusps" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -A3 "theorem X0_26_Q_eq_cusps" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean | grep -q rfl
grep -q "theorem mem_1" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "theorem mem_2" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "theorem mem_13" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "theorem mem_26" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "theorem not_mem_3" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "def hInList_X0_26" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "def hNotIn_X0_26" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "def hInList_label" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "def hNotIn_label" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "theorem displayed_mem_cusps" \
  lean/BealLevel26Foundations/Chain/X0_26_Point.lean
grep -q "hInList_label" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "displayed_mem_cusps" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
grep -q "X0_26_cusps" docs/Chain/X0_26_Point.md
grep -q "P.mem" docs/Chain/X0_26_Point.md
grep -q "mem_1" docs/Chain/X0_26_Point.md
if grep -nE 'BealExponent13_Iter[[:space:]]*:[[:space:]]*∀' \
    lean/BealLevel26Foundations/Final/BealExponent13_Final.lean \
    lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean; then
  echo "FAIL: Iter package must not claim ∀ A B C"
  exit 1
fi
grep -q "We do not use the word final" docs/NEXT_STEPS.md
grep -q "BealExponent13_Contradiction" docs/NEXT_STEPS.md
grep -q "v4.8.0" docs/NEXT_STEPS.md
grep -q "v4.9.0" docs/NEXT_STEPS.md
grep -q "v4.10.0" docs/NEXT_STEPS.md
grep -q "v4.12.0" docs/NEXT_STEPS.md
grep -q "v4.13.0" docs/NEXT_STEPS.md
grep -q "v4.13.1" docs/NEXT_STEPS.md
grep -q "no True" docs/NEXT_STEPS.md
grep -q "pari_x0_26_four_cusps.json" docs/NEXT_STEPS.md
grep -qi "waiting" docs/NEXT_STEPS.md
grep -q "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260" \
  lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean
if grep -nE 'BealTheorem_Exponent13_Forall[[:space:]]*:[[:space:]]*∀' \
    lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean; then
  echo "FAIL: BealTheorem_Exponent13_Forall_Computational must not claim ∀ A B C"
  exit 1
fi
if grep -nE 'Prop[[:space:]]*:=[[:space:]]*True|:=[[:space:]]*trivial' \
    lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean; then
  echo "FAIL: Forall package must not be True/trivial"
  exit 1
fi
if grep -nE '^[[:space:]]*False\.elim|^[[:space:]]*exact[[:space:]]+False\.elim' \
    lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean; then
  echo "FAIL: Forall package must not inhabit a forall by contradiction"
  exit 1
fi
grep -q "fourCuspsForallCuspPoints" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsActual_26.lean
grep -q "fourCuspsForallCuspPoints" \
  lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
grep -q "fourCuspsForallAllKinds_is_false" \
  lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
test -f lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean
grep -q "def hIdentify" \
  lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean
grep -q "def HIdentify26.of_qExpansion" \
  lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean
grep -q "def hIdentifyFinitePackage" \
  lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean
grep -q "theorem remainingGeometricIdentify.certified" \
  lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean
grep -q "sUnitAudit26_is_not_genuine_2Selmer" \
  lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean
if grep -nE 'hIdentify_typed_is_uninhabitable' \
    lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean; then
  echo "FAIL: typed hIdentify is the elliptic-j packing, not the old uninhabitable implication"
  exit 1
fi
if grep -nE \
    'theorem[[:space:]]+(genuineCohomological2Selmer|twoSelmerIdentification|SelmerGroup_eq)' \
    lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean; then
  echo "FAIL: must not identify the S-unit audit with genuine 2-Selmer"
  exit 1
fi
if grep -nE 'selmerGroup|IsDedekindDomain' \
    lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean; then
  echo "FAIL: hIdentify package must not use IsDedekindDomain.selmerGroup"
  exit 1
fi
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean \
    lean/BealLevel26Foundations/Mazur/EndgameScaffold.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
test -f lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
grep -q "def HGeomForbid26.of_qExpansion" \
  lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
grep -q "theorem ellipticJ_ne_four_cusp_labels" \
  lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
grep -q "theorem hGeomForbid_typed_is_uninhabitable" \
  lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
grep -q "theorem remainingGeometricForbid.certified" \
  lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
grep -q "sUnitAudit26_is_not_genuine_2Selmer" \
  lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean
if grep -nE \
    '^[[:space:]]*(def|theorem)[[:space:]]+hGeomForbid[[:space:]]' \
    lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean; then
  echo "FAIL: must not inhabit typed hGeomForbid fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi
if grep -nE \
    'theorem[[:space:]]+(genuineCohomological2Selmer|twoSelmerIdentification|SelmerGroup_eq)' \
    lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean; then
  echo "FAIL: must not identify the S-unit audit with genuine 2-Selmer"
  exit 1
fi
if grep -nE 'selmerGroup|IsDedekindDomain' \
    lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean; then
  echo "FAIL: hGeomForbid package must not use IsDedekindDomain.selmerGroup"
  exit 1
fi
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Mazur/HGeomForbidActual_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
test -f lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
grep -q "def chabauty0Package" \
  lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
grep -q "theorem chabauty0Package.certified" \
  lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
grep -q "theorem remainingGeometricForbid.certified" \
  lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
grep -q "fourCuspsForallCuspPoints" \
  lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
grep -q "fourCuspsForallAllKinds_is_false" \
  lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
grep -q "sUnitAudit26_is_not_genuine_2Selmer" \
  lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
grep -q "Not Chabauty" \
  lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean
if grep -nE \
    '^[[:space:]]*(def|theorem)[[:space:]]+hGeomForbid[[:space:]]' \
    lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean; then
  echo "FAIL: must not inhabit typed hGeomForbid fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi
if grep -nE 'rankZero[[:space:]]*:=[[:space:]]*True|⟨[[:space:]]*True[[:space:]]*,[[:space:]]*trivial[[:space:]]*⟩|FreyModLRep.*:=[[:space:]]*True|RibetLowering_26.*:=[[:space:]]*True' \
    lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean \
    lean/BealLevel26Foundations/Ribet/HIdentifyActual_26.lean; then
  echo "FAIL: must not inhabit representation or rank-zero data as True/trivial"
  exit 1
fi
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Mazur/Chabauty0Actual_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
test -f lean/BealLevel26Foundations/Jacobian/ResidueDisks_26.lean
grep -q "def ResidueDiskAt2ContainsOnlyCusp" \
  lean/BealLevel26Foundations/Jacobian/ResidueDisks_26.lean
grep -q "def Chabauty0DiskEquality" \
  lean/BealLevel26Foundations/Jacobian/ResidueDisks_26.lean
grep -q "Not a residue-disk" \
  lean/BealLevel26Foundations/Jacobian/ResidueDisks_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/ResidueDisks_26.lean
test -f lean/BealLevel26Foundations/Jacobian/MordellWeilSieve_26.lean
grep -q "def X0_26_Q_EqualsFourCuspsAsScheme" \
  lean/BealLevel26Foundations/Jacobian/MordellWeilSieve_26.lean
grep -q "not a scheme-theoretic" \
  lean/BealLevel26Foundations/Jacobian/MordellWeilSieve_26.lean
grep -q "sUnitAudit26_is_not_genuine_2Selmer" \
  lean/BealLevel26Foundations/Jacobian/MordellWeilSieve_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/MordellWeilSieve_26.lean
test -f lean/BealLevel26Foundations/Mazur/X026RationalPointsScheme_26.lean
grep -q "def X0_26_RationalPoints26_as_scheme" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsScheme_26.lean
grep -q "Not a scheme-theoretic" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsScheme_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Mazur/X026RationalPointsScheme_26.lean
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Jacobian/ResidueDisks_26.lean \
    lean/BealLevel26Foundations/Jacobian/MordellWeilSieve_26.lean \
    lean/BealLevel26Foundations/Mazur/X026RationalPointsScheme_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE \
    '^[[:space:]]*(def|theorem)[[:space:]]+hGeomForbid[[:space:]]' \
    lean/BealLevel26Foundations/Jacobian/ResidueDisks_26.lean \
    lean/BealLevel26Foundations/Jacobian/MordellWeilSieve_26.lean \
    lean/BealLevel26Foundations/Mazur/X026RationalPointsScheme_26.lean; then
  echo "FAIL: must not inhabit typed hGeomForbid fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi
test -f lean/BealLevel26Foundations/Blueprint/README.md
test -f lean/BealLevel26Foundations/Jacobian/J0_26_Scheme_26.lean
grep -q "def J0_26_Scheme_26" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Scheme_26.lean
grep -q "structure J0_26_Scheme" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Scheme_26.lean
grep -q "Not a Mathlib Jacobian" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Scheme_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Scheme_26.lean
test -f lean/BealLevel26Foundations/Jacobian/AbelJacobi_26.lean
grep -q "structure AbelJacobi_26" \
  lean/BealLevel26Foundations/Jacobian/AbelJacobi_26.lean
grep -q "Not a map of schemes" \
  lean/BealLevel26Foundations/Jacobian/AbelJacobi_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/AbelJacobi_26.lean
if grep -nE 'isJacobianOfX0_26[[:space:]]*:=[[:space:]]*True|goodReductionAtTwo[[:space:]]*:=[[:space:]]*True|mordellWeilRankZero[[:space:]]*:=[[:space:]]*True|sendsInfinityCuspToZero[[:space:]]*:=[[:space:]]*True|cuspImageTorsion[[:space:]]*:=[[:space:]]*True|⟨[[:space:]]*True[[:space:]]*,[[:space:]]*trivial[[:space:]]*⟩' \
    lean/BealLevel26Foundations/Jacobian/J0_26_Scheme_26.lean \
    lean/BealLevel26Foundations/Jacobian/AbelJacobi_26.lean; then
  echo "FAIL: must not inhabit J0_26_Scheme or AbelJacobi as True/trivial"
  exit 1
fi
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Jacobian/J0_26_Scheme_26.lean \
    lean/BealLevel26Foundations/Jacobian/AbelJacobi_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
test -f lean/BealLevel26Foundations/Jacobian/ResidueDisksProof_26.lean
grep -q "def diskEqualityFromImmersion" \
  lean/BealLevel26Foundations/Jacobian/ResidueDisksProof_26.lean
grep -q "theorem diskEqualityFromImmersion.certified" \
  lean/BealLevel26Foundations/Jacobian/ResidueDisksProof_26.lean
grep -q "Not a residue-disk" \
  lean/BealLevel26Foundations/Jacobian/ResidueDisksProof_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/ResidueDisksProof_26.lean
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Jacobian/ResidueDisksProof_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE \
    '^[[:space:]]*(def|theorem)[[:space:]]+hGeomForbid[[:space:]]' \
    lean/BealLevel26Foundations/Jacobian/ResidueDisksProof_26.lean; then
  echo "FAIL: must not inhabit typed hGeomForbid fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi
test -f lean/BealLevel26Foundations/Jacobian/ColemanIntegral_26.lean
grep -q "def ColemanVanishesOnRankZero" \
  lean/BealLevel26Foundations/Jacobian/ColemanIntegral_26.lean
grep -q "theorem ColemanVanishesOnRankZero.certified" \
  lean/BealLevel26Foundations/Jacobian/ColemanIntegral_26.lean
grep -q "Not a Coleman integral" \
  lean/BealLevel26Foundations/Jacobian/ColemanIntegral_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/ColemanIntegral_26.lean
test -f lean/BealLevel26Foundations/Jacobian/ColemanNonVanishing_26.lean
grep -q "def DifferentialNonZeroOnDisk" \
  lean/BealLevel26Foundations/Jacobian/ColemanNonVanishing_26.lean
grep -q "def Chabauty0ForcesCusp" \
  lean/BealLevel26Foundations/Jacobian/ColemanNonVanishing_26.lean
grep -q "Not a Chabauty" \
  lean/BealLevel26Foundations/Jacobian/ColemanNonVanishing_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Jacobian/ColemanNonVanishing_26.lean
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Jacobian/ColemanIntegral_26.lean \
    lean/BealLevel26Foundations/Jacobian/ColemanNonVanishing_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE \
    '^[[:space:]]*(def|theorem)[[:space:]]+hGeomForbid[[:space:]]' \
    lean/BealLevel26Foundations/Jacobian/ColemanIntegral_26.lean \
    lean/BealLevel26Foundations/Jacobian/ColemanNonVanishing_26.lean; then
  echo "FAIL: must not inhabit typed hGeomForbid fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi

test -f lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean
grep -q "def LMFDB_26a1_rankZero" \
  lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean
grep -q "def LMFDB_26b1_rankZero" \
  lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean
grep -q "def J0_26_rankZero_from_LMFDB" \
  lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean
grep -q "Not a Mordell--Weil theorem" \
  lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean
if grep -nE 'Prop[[:space:]]*:=[[:space:]]*True|:=[[:space:]]*trivial' \
    lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean; then
  echo "FAIL: LMFDB rank must not be True/trivial"
  exit 1
fi
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE \
    '^[[:space:]]*(def|theorem)[[:space:]]+hGeomForbid[[:space:]]' \
    lean/BealLevel26Foundations/Certs/LMFDBCert_26.lean; then
  echo "FAIL: must not inhabit typed hGeomForbid fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi

test -f lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean
test -f lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
test -f lean/BealLevel26Foundations/Descent/Selmer_26.lean
grep -q "def EC_26a1_aInv" \
  lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean
grep -q "def EC_26b1_aInv" \
  lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean
grep -q "factor26a1.a1" \
  lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean
grep -q -- "-17576" \
  lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean
grep -q -- "-1664" \
  lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean
grep -q "def TwoCoverings_26a1_finitePackage" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "def SelmerBound_26a1" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "def SelmerBound_26b1" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "def TorsionOrder_26a1" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "def TorsionOrder_26b1" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "SelmerBound_26a1 : ℕ := 1" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "TorsionOrder_26a1 : ℕ := 3" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "Not a Selmer" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "Not a two-descent" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean
grep -q "def Sha2_26a1_trivial" \
  lean/BealLevel26Foundations/Descent/Selmer_26.lean
grep -q "def RankZero_26a1_from_Selmer" \
  lean/BealLevel26Foundations/Descent/Selmer_26.lean
grep -q "def RankZero_26b1_from_Selmer" \
  lean/BealLevel26Foundations/Descent/Selmer_26.lean
grep -q "Not a Selmer" \
  lean/BealLevel26Foundations/Descent/Selmer_26.lean
grep -q "Not a Mordell--Weil theorem" \
  lean/BealLevel26Foundations/Descent/Selmer_26.lean
grep -qF "Not Sha[2] triviality" \
  lean/BealLevel26Foundations/Descent/Selmer_26.lean
grep -q "0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151" \
  lean/BealLevel26Foundations/Descent/Selmer_26.lean
grep -q "import BealLevel26Foundations.Descent.Selmer_26" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
grep -q "do not replace" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
grep -q "Not a Selmer" \
  lean/BealLevel26Foundations/Jacobian/J0_26_Q_RankZeroActual_26.lean
if grep -nE 'Prop[[:space:]]*:=[[:space:]]*True|:=[[:space:]]*trivial' \
    lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean \
    lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean \
    lean/BealLevel26Foundations/Descent/Selmer_26.lean; then
  echo "FAIL: Descent ranks/Selmer names must not be True/trivial"
  exit 1
fi
if grep -nE -- '-1216|-1831858856|-213' \
    lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean; then
  echo "FAIL: Descent Weierstrass models must use certified 26a1/26b1 a-invariants"
  exit 1
fi
if grep -nE '^[[:space:]]*theorem BealTheorem[[:space:]]' \
    lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean \
    lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean \
    lean/BealLevel26Foundations/Descent/Selmer_26.lean; then
  echo "FAIL: unconditional BealTheorem is not allowed"
  exit 1
fi
if grep -nE \
    '^[[:space:]]*(def|theorem)[[:space:]]+hGeomForbid[[:space:]]' \
    lean/BealLevel26Foundations/Descent/EllipticCurve_26a1_26b1_26.lean \
    lean/BealLevel26Foundations/Descent/TwoDescent_26a1_26.lean \
    lean/BealLevel26Foundations/Descent/Selmer_26.lean; then
  echo "FAIL: must not inhabit typed hGeomForbid fourCusps → ¬ ExistsNoncuspidal"
  exit 1
fi

python3 scripts/verify_coefficient_ledger.py
python3 scripts/verify_v1_3_0_certs.py
python3 scripts/replay_level26_hensel.py
python3 scripts/verify_lmfdb_26.py
python3 scripts/verify_descent_26.py

echo "OK: Beal Level-26 Foundations computable release is internally consistent"