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
    .one `BealGap9, .one `BealGap10, .one `BealGap11, .one `BealGap12, .one `BealGap13,
    .one `BealGap14]
