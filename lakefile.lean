import Lake
open Lake DSL

package beal_matveev_beal where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

/-- Relocated v24.4.0 package (DOI 10.5281/zenodo.22732209, db7a556).
    Modules are `BealLevel26Foundations.Beal.FullProof.*`.
    `BealConjecture.Level26.BealLevel26Foundations.*` are local wrappers. -/
require beal_level_26_foundations from git
  "https://github.com/DavidFox998/beal-conjecture" @ "main"
  / "Level26/BealLevel26Foundations"

/-- Re-export wrappers so the requested import path resolves. -/
lean_lib BealConjecture where
  globs := #[.submodules `BealConjecture]

@[default_target]
lean_lib «BealMatveevBeal» where
  globs := #[.submodules `Beal.Matveev, .one `MatveevThm14Proof, .one `MatveevLLL,
    .one `MatveevInterpolation, .one `MatveevBugeaud, .one `WuestholzSubgroup,
    .one `WuestholzProduct, .one `MatveevThreeLogs, .one `BealKraus, .one `BealKrausZsig,
    .one `BealCatalanZsig, .one `BealDarmonMerel, .one `BealDarmonMerel44p,
    .one `BealFLT13, .one `BealGenuineV25, .one `BealTrueV25,
    .one `BealUnconditionalV25, .one `BealGap1, .one `BealGap2, .one `BealGap4,
    .one `BealGap5, .one `BealGap6, .one `BealGap7, .one `BealGap8,
    .one `BealGap9, .one `BealGap10, .one `BealGap11, .one `BealGap12,     .one `BealGap13,
    .one `BealGap14, .one `BealGap15, .one `BealGapK,
    .one `EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6,
    .one `BugeaudLaurent, .one `PAdicLLL, .one `PAdicLLL_ZeroAxiom]

/-- Rank-3 v25 *shape* wrappers. Not the default target: keeps
    `lake build BealMatveevBeal` independent of this file. Does
    not mint v25. -/
lean_lib «BealMatveevBealV25Rank3» where
  globs := #[.one `BealMatveevBealV25Rank3]

/-- Gap-3 `B ≤ B0` search slice. Not the default target. Does
    not mint v25. Does not claim the full million-B search.
    `Gap3B0Million` is the foldl wiring for 10k shards of 100;
    those shards are not `native_decide`'d.
    `LLLTargetB8_C1_lower_bound` is `C1' ≤ 8` impossible on a
    solution via `|Λ| ≤ 2/B⁹`; `¬ LLL_reduces_C1_to_lt_nine`
    stays `def Prop`. `DarmonMerelFrey4413` is the displayed
    Frey curve for signature `(4,4,13)`; level-32 table stays
    `def Prop`. -/
lean_lib «BealMatveevBealV25B0Search» where
  globs := #[.one `BealMatveevBealV25B0Search, .one `LLLTargetB8, .one `Gap3B0Million,
    .one `LLLTargetB8_C1_lower_bound, .one `DarmonMerelFrey4413]
