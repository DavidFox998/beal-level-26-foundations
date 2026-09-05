#!/usr/bin/env bash
set -euo pipefail

test -f README.md
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
  '^[[:space:]]*(axiom|sorry|admit)([[:space:]]|$)|:[[:space:]]*True[[:space:]]*:=' \
  --include='*.lean' .; then
  echo "FAIL: unfinished or vacuous Lean declaration found"
  exit 1
fi

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
grep -q "theorem BealTheorem_Exponent13_Full" \
  lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean
if grep -nE 'BealTheorem_Exponent13_Full[[:space:]]*:[[:space:]]*∀' \
    lean/BealLevel26Foundations/Mazur/BealTheoremFromMazurChain26.lean; then
  echo "FAIL: BealTheorem_Exponent13_Full must not claim ∀ A B C Fermat/Beal"
  exit 1
fi
grep -q "def FreyConductorDivides26 : Prop := 2 * 13 = 26" \
  lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
grep -q "def FreyToX0_26 : Prop := 26 = 2 * 13" \
  lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
grep -q "theorem freyToX0_26_computational" \
  lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
grep -q "no Ribet" \
  lean/BealLevel26Foundations/Chain/FreyCurve_13_26.lean
grep -q "def X0_26_Q_eq_fourCusps" \
  lean/BealLevel26Foundations/Chain/RationalPoints_26_FourCusps_26.lean
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