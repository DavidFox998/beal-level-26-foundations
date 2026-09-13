/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
/-
  Re-export. Theorems live in the root module `MatveevLLL` so
  `Beal/Matveev/MatveevThm14General.lean` can import them. Lake's
  LEAN_PATH puts the relocated kernel's `Beal/` prefix first, so a
  sibling `import Beal.Matveev.MatveevLLL` does not resolve.
-/
import MatveevLLL
