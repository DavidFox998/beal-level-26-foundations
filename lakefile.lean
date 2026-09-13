import Lake
open Lake DSL

package beal_matveev_beal where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

require beal_conjecture from git
  "https://github.com/DavidFox998/beal-conjecture" @ "main"

@[default_target]
lean_lib «BealMatveevBeal» where
  globs := #[.submodules `Beal.Matveev]
