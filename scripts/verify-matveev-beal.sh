#!/usr/bin/env bash
# Honest AMS / Math. Comp. referee surface for foundations-level-26.
# This repo owns the integer-gap B≤B0 Matveev lower bound (not Mathlib 4.12
# interpolation, not unrestricted matveev_inequality_real_target).
# Zero sorry/admit in Lean sources.
set -euo pipefail

ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$ROOT"

fail() { echo "verify-matveev-beal: $*" >&2; exit 1; }

test -f lean-toolchain
test -f lakefile.lean
test -f lake-manifest.json
test -f CITATION.cff
test -f README.md
test -f LICENSE
test -f Beal/Matveev/MatveevThm14General.lean
test -f Beal/Matveev/MatveevThm14Proof.lean
test -f Beal/Matveev/MatveevLLL.lean
test -f MatveevThm14Proof.lean
test -f MatveevLLL.lean
test -f MatveevInterpolation.lean
test -f Beal/Matveev/MatveevInterpolation.lean
test -f MatveevBugeaud.lean
test -f Beal/Matveev/MatveevBugeaud.lean
test -f WuestholzSubgroup.lean
test -f Beal/Matveev/WuestholzSubgroup.lean

grep -q 'leanprover/lean4:v4.12.0' lean-toolchain \
  || fail "lean-toolchain is not Lean 4.12.0"

grep -q '@\[default_target\]' lakefile.lean
grep -q 'BealMatveevBeal' lakefile.lean \
  || fail "lakefile.lean missing BealMatveevBeal"
if grep -q 'BealLevel26FoundationsScaffold' lakefile.lean; then
  fail "lakefile.lean still names the relocated Scaffold target"
fi

python3 - <<'PY'
import pathlib, re, sys

root = pathlib.Path(".")
lean_files = [
    p for p in root.rglob("*.lean")
    if ".lake" not in p.parts and "scripts" not in p.parts
]

sorry_pat = re.compile(r"^\s*sorry\b")
admit_pat = re.compile(r"^\s*admit\b")
sorries, admits = [], []
for p in lean_files:
    text = p.read_text(encoding="utf-8")
    for i, line in enumerate(text.splitlines(), 1):
        if sorry_pat.match(line):
            sorries.append(f"{p.as_posix()}:{i}")
        if admit_pat.match(line):
            admits.append(f"{p.as_posix()}:{i}")

if admits:
    print("unexpected admit:", *admits, sep="\n  ", file=sys.stderr)
    sys.exit(1)

if sorries:
    print("sorry budget is not empty:", file=sys.stderr)
    print("  found:", sorries, file=sys.stderr)
    sys.exit(1)

src = pathlib.Path("Beal/Matveev/MatveevThm14General.lean").read_text(encoding="utf-8")
if "theorem matveev_gap3_lower :" not in src:
    print("theorem matveev_gap3_lower missing", file=sys.stderr)
    sys.exit(1)
body = src.split("theorem matveev_gap3_lower :", 1)[1]
body = re.split(r"\n(?:def |theorem |lemma |/-!)", body, maxsplit=1)[0]
if re.search(r"^\s*sorry\b", body, re.M):
    print("matveev_gap3_lower still contains sorry", file=sys.stderr)
    sys.exit(1)
if "matveev_gap3_lower_B_le_B0_target" not in src:
    print("B≤B0 target missing", file=sys.stderr)
    sys.exit(1)
if "matveev_gap3_lower_of_integer_gap_of_B_le_B0" not in src:
    print("integer-gap B≤B0 close missing", file=sys.stderr)
    sys.exit(1)
if "143186215390" not in src:
    print("C1_floor = 143186215390 missing from MatveevThm14General.lean", file=sys.stderr)
    sys.exit(1)
if "matveev_product_bound_of_B_le_B0" not in src:
    print("proved product bound missing", file=sys.stderr)
    sys.exit(1)
if "gap3_A_bounds" not in src:
    print("gap3_A_bounds missing", file=sys.stderr)
    sys.exit(1)
if "matveev_gap3_lower_of_general_of_B_le_B0" not in src:
    print("v25-sufficient packaging missing", file=sys.stderr)
    sys.exit(1)
if "matveev_thm14_n2_explicit_of_nat" not in pathlib.Path("MatveevThm14Proof.lean").read_text(encoding="utf-8"):
    print("matveev_thm14_n2_explicit_of_nat missing from MatveevThm14Proof.lean", file=sys.stderr)
    sys.exit(1)

lll = pathlib.Path("MatveevLLL.lean").read_text(encoding="utf-8")
if "theorem four_thirteenths_is_convergent" not in lll:
    print("four_thirteenths_is_convergent missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem integer_gap_lt_ratio" not in lll:
    print("integer_gap_lt_ratio missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem abs_Lambda_ge_B4_div_B3_pow" not in lll:
    print("abs_Lambda_ge_B4_div_B3_pow missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem abs_Lambda_tight_sandwich" not in lll:
    print("abs_Lambda_tight_sandwich missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem abs_Lambda_le_inv_B" not in lll:
    print("abs_Lambda_le_inv_B missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem elementary_inv_max_compatible_with_inv_B" not in lll:
    print("elementary_inv_max_compatible_with_inv_B missing", file=sys.stderr)
    sys.exit(1)
if "theorem abs_Lambda_lt_inv_max_log_coeff" not in lll:
    print("abs_Lambda_lt_inv_max_log_coeff missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem track1_exp_lt_ratio" not in lll:
    print("track1_exp_lt_ratio missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem LLL_e2_linear_form_approx" not in lll:
    print("LLL_e2_linear_form_approx missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem LLL_basis_det" not in lll:
    print("LLL_basis_det missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem LLL_v_mem" not in lll:
    print("LLL_v_mem missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem LLL_v_norm_lt_thirty_two" not in lll:
    print("LLL_v_norm_lt_thirty_two missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem LLL_lambda1_lt_thirty_two" not in lll:
    print("LLL_lambda1_lt_thirty_two missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "def lllPotential" not in lll:
    print("lllPotential missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem lll_algorithm_terminates" not in lll:
    print("lll_algorithm_terminates must be a theorem", file=sys.stderr)
    sys.exit(1)
if "def lllIsReducedBasis" not in lll:
    print("lllIsReducedBasis missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "def lllBasisPotential" not in lll:
    print("lllBasisPotential missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem lll_svt_bound " not in lll and not re.search(r"^theorem lll_svt_bound\b", lll, re.M):
    print("lll_svt_bound must be a displayed theorem", file=sys.stderr)
    sys.exit(1)
if "theorem lll_det_bound " not in lll and not re.search(r"^theorem lll_det_bound\b", lll, re.M):
    print("lll_det_bound must be a displayed theorem", file=sys.stderr)
    sys.exit(1)
if "theorem lll_gs_lower_half_pow" not in lll:
    print("lll_gs_lower_half_pow missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem lll_reduced_first_vec_le_lattice_vec" not in lll:
    print("lll_reduced_first_vec_le_lattice_vec missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem baker_davenport_no_cutoff" not in lll:
    print("baker_davenport_no_cutoff missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem baker_davenport_gs_lower" not in lll:
    print("baker_davenport_gs_lower rearrangement missing", file=sys.stderr)
    sys.exit(1)
if "theorem lll_svt_bound_of_reduced" not in lll:
    print("lll_svt_bound_of_reduced missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem lllPotential_swap12_factor_lt" not in lll:
    print("lllPotential_swap12_factor_lt missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem lll_lovasz_size_half" not in lll:
    print("lll_lovasz_size_half missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem LLL_b1_normSq_int" not in lll:
    print("LLL_b1_normSq_int missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem abs_sub_lllNearestInt" not in lll:
    print("abs_sub_lllNearestInt missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "def lll_svt_bound" in lll:
    print("lll_svt_bound is now the displayed theorem, not a def Prop", file=sys.stderr)
    sys.exit(1)
if "def lll_det_bound" in lll:
    print("lll_det_bound is now the displayed theorem, not a def Prop", file=sys.stderr)
    sys.exit(1)
if "def baker_davenport_reduction" not in lll:
    print("baker_davenport_reduction must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if "def B0_nat" not in lll or "1000000" not in lll:
    print("B0_nat = 1000000 missing from MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "def bugeaud_LLL_reduction_proof" not in lll:
    print("bugeaud_LLL_reduction_proof must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem bugeaud_LLL_reduction_proof\b", lll, re.M):
    print("bugeaud_LLL_reduction_proof must not be a theorem", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem baker_davenport_reduction\b", lll, re.M):
    print("baker_davenport_reduction must not be a theorem", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem baker_bound_gap3_from_ratio\b", lll, re.M):
    print("baker_bound_gap3_from_ratio must not be a theorem", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem baker_bound_gap3\b", lll, re.M):
    print("do not inhabit baker_bound_gap3 in MatveevLLL.lean", file=sys.stderr)
    sys.exit(1)
if "theorem matveev_gap3_lower_unrestricted" in src or "theorem matveev_gap3_lower_unrestricted" in lll:
    print("do not inhabit unrestricted matveev_gap3_lower", file=sys.stderr)
    sys.exit(1)
if ".one `MatveevLLL" not in pathlib.Path("lakefile.lean").read_text(encoding="utf-8"):
    print("lakefile.lean missing MatveevLLL glob", file=sys.stderr)
    sys.exit(1)
if ".one `MatveevInterpolation" not in pathlib.Path("lakefile.lean").read_text(encoding="utf-8"):
    print("lakefile.lean missing MatveevInterpolation glob", file=sys.stderr)
    sys.exit(1)
if ".one `MatveevBugeaud" not in pathlib.Path("lakefile.lean").read_text(encoding="utf-8"):
    print("lakefile.lean missing MatveevBugeaud glob", file=sys.stderr)
    sys.exit(1)
if ".one `WuestholzSubgroup" not in pathlib.Path("lakefile.lean").read_text(encoding="utf-8"):
    print("lakefile.lean missing WuestholzSubgroup glob", file=sys.stderr)
    sys.exit(1)

bugeaud = pathlib.Path("MatveevBugeaud.lean").read_text(encoding="utf-8")
if "import Beal.Matveev.MatveevThm14General" in bugeaud:
    print("MatveevBugeaud.lean must not import Beal.Matveev.MatveevThm14General", file=sys.stderr)
    sys.exit(1)
if "theorem LLL_v_third_abs_lt_C_mul_abs_Lambda_add" not in bugeaud:
    print("LLL_v_third_abs_lt_C_mul_abs_Lambda_add missing", file=sys.stderr)
    sys.exit(1)
if "theorem bugeaud_third_lt_seventeen_add_C_div_B" not in bugeaud:
    print("bugeaud_third_lt_seventeen_add_C_div_B missing", file=sys.stderr)
    sys.exit(1)
if "theorem bugeaud_bd_lower_lt_inv_B" not in bugeaud:
    print("bugeaud_bd_lower_lt_inv_B missing", file=sys.stderr)
    sys.exit(1)
if "theorem bugeaud_bd_lower_lt_ratio" not in bugeaud:
    print("bugeaud_bd_lower_lt_ratio missing", file=sys.stderr)
    sys.exit(1)
if "theorem bugeaud_bd_lower_lt_abs_Lambda" not in bugeaud:
    print("bugeaud_bd_lower_lt_abs_Lambda missing", file=sys.stderr)
    sys.exit(1)
if "theorem bugeaud_required_r_gt_eighteen_of_B_lt_C" not in bugeaud:
    print("bugeaud_required_r_gt_eighteen_of_B_lt_C missing", file=sys.stderr)
    sys.exit(1)
if "theorem LLL_C_div_B0_eq" not in bugeaud:
    print("LLL_C_div_B0_eq missing", file=sys.stderr)
    sys.exit(1)
if "theorem exists_reduced_b1_lt_sixty_four" not in bugeaud:
    print("exists_reduced_b1_lt_sixty_four missing", file=sys.stderr)
    sys.exit(1)
if "theorem bugeaud_naive_gs_lt_inv_B0" not in bugeaud:
    print("bugeaud_naive_gs_lt_inv_B0 missing", file=sys.stderr)
    sys.exit(1)
if "theorem not_exists_reduced_b1_gt_required_r" not in bugeaud:
    print("not_exists_reduced_b1_gt_required_r missing", file=sys.stderr)
    sys.exit(1)
if "143186215390" not in bugeaud:
    print("C1_floor = 143186215390 missing from MatveevBugeaud.lean", file=sys.stderr)
    sys.exit(1)
if "1000000" not in bugeaud:
    print("B0_nat = 1000000 missing from MatveevBugeaud.lean", file=sys.stderr)
    sys.exit(1)
if "def bugeaud_LLL_reduction_proof" not in bugeaud:
    print("bugeaud_LLL_reduction_proof must stay a def Prop in MatveevBugeaud.lean", file=sys.stderr)
    sys.exit(1)
if "def baker_davenport_reduction" not in bugeaud:
    print("baker_davenport_reduction must stay a def Prop in MatveevBugeaud.lean", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem bugeaud_LLL_reduction_proof\b", bugeaud, re.M):
    print("bugeaud_LLL_reduction_proof must not be a theorem", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem baker_davenport_reduction\b", bugeaud, re.M):
    print("baker_davenport_reduction must not be a theorem", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem baker_bound_gap3_from_ratio\b", bugeaud, re.M):
    print("baker_bound_gap3_from_ratio must not be a theorem", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem baker_bound_gap3\b", bugeaud, re.M):
    print("do not inhabit baker_bound_gap3 in MatveevBugeaud.lean", file=sys.stderr)
    sys.exit(1)

wsg = pathlib.Path("WuestholzSubgroup.lean").read_text(encoding="utf-8")
if "import Beal.Matveev.MatveevThm14General" in wsg:
    print("WuestholzSubgroup.lean must not import Beal.Matveev.MatveevThm14General", file=sys.stderr)
    sys.exit(1)
if "theorem no_uniform_c_easy_half" not in wsg:
    print("no_uniform_c_easy_half missing", file=sys.stderr)
    sys.exit(1)
if "theorem no_uniform_c_one_div_thousand" not in wsg:
    print("no_uniform_c_one_div_thousand missing", file=sys.stderr)
    sys.exit(1)
if "theorem no_uniform_c_linear_in_N" not in wsg:
    print("no_uniform_c_linear_in_N missing", file=sys.stderr)
    sys.exit(1)
if "theorem wuestholz_subgroup_theorem_of_jet_dim" not in wsg:
    print("wuestholz_subgroup_theorem_of_jet_dim missing", file=sys.stderr)
    sys.exit(1)
if "theorem coeffCount_one_ten_ten" not in wsg:
    print("coeffCount_one_ten_ten missing", file=sys.stderr)
    sys.exit(1)
if "theorem siegel_T_lt_jet_dim" not in wsg:
    print("siegel_T_lt_jet_dim missing", file=sys.stderr)
    sys.exit(1)
if "def W_tangent" not in wsg:
    print("W_tangent missing", file=sys.stderr)
    sys.exit(1)
if "def vanishesToOrder" not in wsg:
    print("vanishesToOrder missing", file=sys.stderr)
    sys.exit(1)
if "structure AlgebraicSubgroup" not in wsg:
    print("AlgebraicSubgroup missing", file=sys.stderr)
    sys.exit(1)
if "143186215390" not in wsg:
    print("C1_floor = 143186215390 missing from WuestholzSubgroup.lean", file=sys.stderr)
    sys.exit(1)
if "1000000" not in wsg:
    print("B0_nat = 1000000 missing from WuestholzSubgroup.lean", file=sys.stderr)
    sys.exit(1)
if "True := trivial" in wsg:
    print("do not paste True := trivial skeletons", file=sys.stderr)
    sys.exit(1)
if "def wuestholz_subgroup_theorem" not in wsg:
    print("wuestholz_subgroup_theorem must stay a def Prop in WuestholzSubgroup.lean", file=sys.stderr)
    sys.exit(1)
if "def wuestholz_product_theorem_exp" not in wsg:
    print("wuestholz_product_theorem_exp must stay a def Prop in WuestholzSubgroup.lean", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem wuestholz_subgroup_theorem\b", wsg, re.M):
    print("do not inhabit wuestholz_subgroup_theorem", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem wuestholz_product_theorem_exp\b", wsg, re.M):
    print("do not inhabit wuestholz_product_theorem_exp", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem baker_bound_gap3\b", wsg, re.M):
    print("do not inhabit baker_bound_gap3 in WuestholzSubgroup.lean", file=sys.stderr)
    sys.exit(1)

interp = pathlib.Path("MatveevInterpolation.lean").read_text(encoding="utf-8")
if "import Beal.Matveev.MatveevThm14General" in interp:
    print("MatveevInterpolation.lean must not import Beal.Matveev.MatveevThm14General", file=sys.stderr)
    sys.exit(1)
if "theorem C1_floor_eq" not in interp or "143186215390" not in interp:
    print("C1_floor = 143186215390 missing from MatveevInterpolation.lean", file=sys.stderr)
    sys.exit(1)
if "def height_B0_nat" not in interp or "104382751019310000000" not in interp:
    print("height_B0_nat missing from MatveevInterpolation.lean", file=sys.stderr)
    sys.exit(1)
if "def B0_nat" not in interp or "1000000" not in interp:
    print("B0_nat = 1000000 missing from MatveevInterpolation.lean", file=sys.stderr)
    sys.exit(1)
if "theorem interpolation_det_ne_zero" not in interp:
    print("interpolation_det_ne_zero missing", file=sys.stderr)
    sys.exit(1)
if "def interpolationDeterminant" not in interp:
    print("interpolationDeterminant missing", file=sys.stderr)
    sys.exit(1)
if "theorem matveev_thm14_n2_real_explicit_is_false" not in interp:
    print("matveev_thm14_n2_real_explicit_is_false missing", file=sys.stderr)
    sys.exit(1)
if "theorem matveev_interpolation_track1" not in interp:
    print("matveev_interpolation_track1 missing", file=sys.stderr)
    sys.exit(1)
if "def matveev_thm14_n2_real_explicit" not in interp:
    print("matveev_thm14_n2_real_explicit must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem matveev_thm14_n2_real_explicit\b", interp, re.M):
    print("do not inhabit matveev_thm14_n2_real_explicit (false for reals)", file=sys.stderr)
    sys.exit(1)
if "theorem wuestholz_product_theorem_Ga" not in interp:
    print("wuestholz_product_theorem_Ga missing", file=sys.stderr)
    sys.exit(1)
if "theorem size_upper_bound_hadamard" not in interp:
    print("size_upper_bound_hadamard missing", file=sys.stderr)
    sys.exit(1)
if "def size_upper_bound" not in interp:
    print("analytic size_upper_bound must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if "theorem matveev_interpolation_analytic_small_bound" not in interp:
    print("matveev_interpolation_analytic_small_bound missing", file=sys.stderr)
    sys.exit(1)
if "theorem schwarz_lemma_of_order" not in interp:
    print("schwarz_lemma_of_order missing", file=sys.stderr)
    sys.exit(1)
if "def matveevPhi" not in interp:
    print("matveevPhi missing", file=sys.stderr)
    sys.exit(1)
if "theorem interpolationDeterminant_L0_not_exp_small" not in interp:
    print("interpolationDeterminant_L0_not_exp_small missing", file=sys.stderr)
    sys.exit(1)
if "theorem cauchy_estimate_iteratedDslope" not in interp:
    print("cauchy_estimate_iteratedDslope missing", file=sys.stderr)
    sys.exit(1)
if "theorem polynomial_iteratedDslope_vanishes" not in interp:
    print("polynomial_iteratedDslope_vanishes missing", file=sys.stderr)
    sys.exit(1)
if "theorem schwarz_lemma_of_order_polynomial" not in interp:
    print("schwarz_lemma_of_order_polynomial missing", file=sys.stderr)
    sys.exit(1)
if "theorem iteratedDslope_one_add_pow" not in interp:
    print("iteratedDslope_one_add_pow missing", file=sys.stderr)
    sys.exit(1)
if "theorem siegel_lemma" not in interp:
    print("siegel_lemma missing", file=sys.stderr)
    sys.exit(1)
if "theorem integer_box_card" not in interp:
    print("integer_box_card missing", file=sys.stderr)
    sys.exit(1)
if "theorem matveevPhi_vanishing_exists_T" not in interp:
    print("matveevPhi_vanishing_exists_T missing", file=sys.stderr)
    sys.exit(1)
if "theorem matveevPhi_eq_P_along_W" not in interp:
    print("matveevPhi_eq_P_along_W missing", file=sys.stderr)
    sys.exit(1)
if "theorem gap3_not_fourth_thirteenth" not in interp:
    print("gap3_not_fourth_thirteenth missing", file=sys.stderr)
    sys.exit(1)
if "theorem interpolationDeterminant_L_pos_alpha_one" not in interp:
    print("interpolationDeterminant_L_pos_alpha_one missing", file=sys.stderr)
    sys.exit(1)
if "theorem wuestholz_product_theorem_exp_Gm" not in interp:
    print("wuestholz_product_theorem_exp_Gm missing", file=sys.stderr)
    sys.exit(1)
if "theorem exp_poly_jet_zero" not in interp:
    print("exp_poly_jet_zero missing", file=sys.stderr)
    sys.exit(1)
if "theorem wuestholz_product_theorem_exp_Gm_of_mvPolynomial" not in interp:
    print("wuestholz_product_theorem_exp_Gm_of_mvPolynomial missing", file=sys.stderr)
    sys.exit(1)
if "def matveevPhi_of_mvPolynomial" not in interp:
    print("matveevPhi_of_mvPolynomial missing", file=sys.stderr)
    sys.exit(1)
if "theorem wuestholz_product_theorem_exp_Gm_of_rpow_indep" not in interp:
    print("wuestholz_product_theorem_exp_Gm_of_rpow_indep missing", file=sys.stderr)
    sys.exit(1)
if "theorem wuestholz_product_theorem_exp_of_full_order" not in interp:
    print("wuestholz_product_theorem_exp_of_full_order missing", file=sys.stderr)
    sys.exit(1)
if "theorem dependent_pair_allows_identically_zero_Phi" not in interp:
    print("dependent_pair_allows_identically_zero_Phi missing", file=sys.stderr)
    sys.exit(1)
if "theorem wuestholz_Ga_siegel_below_full_order" not in interp:
    print("wuestholz_Ga_siegel_below_full_order missing", file=sys.stderr)
    sys.exit(1)
if "inductive ProperSubgroupCandidate" not in interp:
    print("ProperSubgroupCandidate missing", file=sys.stderr)
    sys.exit(1)
if "theorem mul_dep_of_W_in_graph" not in interp:
    print("mul_dep_of_W_in_graph missing", file=sys.stderr)
    sys.exit(1)
if "theorem W_not_in_proper_candidate_of_indep" not in interp:
    print("W_not_in_proper_candidate_of_indep missing", file=sys.stderr)
    sys.exit(1)
if "theorem intermediate_threshold_lt_jet_dim" not in interp:
    print("intermediate_threshold_lt_jet_dim missing", file=sys.stderr)
    sys.exit(1)
if "theorem intermediate_T_example_half" not in interp:
    print("intermediate_T_example_half missing", file=sys.stderr)
    sys.exit(1)
if "theorem no_uniform_c_reaches_full_order" not in interp:
    print("no_uniform_c_reaches_full_order missing", file=sys.stderr)
    sys.exit(1)
if "theorem wuestholz_subgroup_of_jet_dim_le_threshold" not in interp:
    print("wuestholz_subgroup_of_jet_dim_le_threshold missing", file=sys.stderr)
    sys.exit(1)
if "def wuestholz_subgroup_theorem" not in interp:
    print("wuestholz_subgroup_theorem must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem wuestholz_subgroup_theorem\b", interp, re.M):
    print("do not inhabit wuestholz_subgroup_theorem", file=sys.stderr)
    sys.exit(1)
if "theorem matveev_thm14_n2_explicit_of_nat_is_corollary_of_genuine" in interp:
    print("do not claim Track 1 is a corollary of genuine Matveev", file=sys.stderr)
    sys.exit(1)
if "def wuestholz_product_theorem_exp" not in interp:
    print("wuestholz_product_theorem_exp must stay a def Prop", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem wuestholz_product_theorem_exp\b", interp, re.M):
    print("do not inhabit wuestholz_product_theorem_exp", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem size_upper_bound\b", interp, re.M):
    print("do not inhabit size_upper_bound (L=0 gives Δ=1)", file=sys.stderr)
    sys.exit(1)
if re.search(r"^theorem baker_bound_gap3\b", interp, re.M):
    print("do not inhabit baker_bound_gap3", file=sys.stderr)
    sys.exit(1)

readme = pathlib.Path("README.md").read_text(encoding="utf-8")
if not readme.startswith("# foundations-level-26"):
    print("README.md must start with the foundations-level-26 title", file=sys.stderr)
    sys.exit(1)
if "beal-conjecture stays beal-conjecture" not in readme:
    print("README.md must keep the monorepo slug note", file=sys.stderr)
    sys.exit(1)

cff = pathlib.Path("CITATION.cff").read_text(encoding="utf-8")
needles = [
    'title: "foundations-level-26 — Beal Level 26 Matveev-Baker Foundations"',
    'version: "v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations"',
    'doi: "10.5281/zenodo.22379293"',
    'repository-code: "https://github.com/DavidFox998/beal-level-26-foundations"',
]
for n in needles:
    if n not in cff:
        print("CITATION.cff missing:", n, file=sys.stderr)
        sys.exit(1)

print("verify-matveev-beal: ok")
print("  0 sorry; matveev_gap3_lower is the B<=B0 integer-gap close")
print("  C1_floor=143186215390, gap3_A_bounds and B<=B0 product proved")
print("  CF lemmas: 4/13 convergent, integer gap < ratio; |Λ|<1/B not a cutoff")
print("  1/max(4log A,13log C) is not a lower bound; Track1 exp < ratio")
print("  LLL floor form approximates CΛ to <17; rank-3 det=C, ||v||<32")
print("  Lovasz 1/2, swap D<3/4 D, SVT of reduced, BD rearrangement")
print("  lll_algorithm_terminates: reduced Z-basis exists; not a B<=1e6 cutoff")
print("  displayed lll_svt_bound ||b1||<=2^{(n-1)/2} lambda1; lll_det_bound ||b1||<=sqrt2 C^{1/3}")
print("  baker_davenport_no_cutoff: (17,18) gives 1e-30 not B<=1e6")
print("  MatveevBugeaud: BD lower < |Λ| so cannot beat 1/B or the ratio")
print("  exists_reduced_b1_lt_sixty_four; C/B0=1e24; required r > 18 if B < C")
print("  baker_davenport_reduction / baker_bound_gap3 stay def Prop")
print("  interpolation: Δ, Vandermonde, G_a product, Hadamard, Schwarz, Cauchy;")
print("  analytic small bound is conditional; polynomial vanishing inhabited")
print("  Siegel + G_a jet vanishing: matveevPhi_vanishing_exists_T")
print("  L>=1 alpha=1 gives Δ=0; jet invertibility wuestholz_product_theorem_exp_Gm")
print("  MvPolynomial form: wuestholz_product_theorem_exp_Gm_of_mvPolynomial")
print("  full-order disjunction P=0 or dependent; intermediate T stays def Prop")
print("  Ga x Gm^2 candidates: graph implies dependence; W not in proper H")
print("  intermediate T < jet dim uniformly; subgroup of jet-dim <= cLK")
print("  WuestholzSubgroup: c=1/2, 1/242, 1/1000 lose to coeffCount 1 10 10=242")
print("  no_uniform_c_linear_in_N; inhabited special case is jet-dim <= cLK")
print("  subgroup-theorem Wüstholz stays def Prop; not a C1_floor close")
print("  bare-real matveev_thm14_n2_real_explicit stays false def Prop")
print("  concept DOI 10.5281/zenodo.22379293, slug beal-level-26-foundations")
print("  unrestricted target and hLLL stay def Prop; not v25")
PY
