/-
Copyright (c) 2026 David Fox. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Fox
-/
import BealMatveevBealV25B0Search.Forward

/-!
# Full 10^6 search: conditional Lean interface and external evidence

The exact-integer checkpoint in `certs/gap3_full10e6_checkpoints.json` has an
independent external verifier. Neither a JSON hash nor the verifier's success
is a Lean term of `gap3_B_le_B0_no_solution`. This module does NOT inhabit
that proposition or the general Beal theorem.
-/

namespace BealMatveevBeal.BealMatveevBealV25B0Search.Full10e6

/-- The actual pinned Matveev numerals, not a bound on every solution. -/
structure MatveevBoundCert : Prop where
  matveevC1 : BealMatveevBealV25B0Search.C1_floor = 143186215390
  bakerB0 : BealMatveevBealV25B0Search.B0_nat = 1000000

theorem matveev_bound_cert : MatveevBoundCert :=
  ⟨BealMatveevBealV25B0Search.C1_floor_eq,
    BealMatveevBealV25B0Search.B0_nat_eq⟩

/-- Level-26 and small-search evidence. The numerical component is still an
explicit hypothesis: displayed numbers do not construct a Néron model. -/
structure Level26EliminationCert : Prop where
  level26 : Forward.Level26SearchData
  below1000 : ∀ B < 1000, ∀ A : ℕ,
    A ^ 4 + B ^ 4 ≠ (B + 3) ^ 13

/-- A future kernel-checkable certificate must construct this proof field.
The external checkpoint file alone is not an inhabitant. -/
structure Full10e6KernelCert : Prop where
  noSolution : BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution

/-- The full-search projection is conditional on a genuine Lean proof term. -/
theorem B0_10e6_search_forward (cert : Full10e6KernelCert) :
    BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution :=
  cert.noSolution

/-- Requested forward ordering. Despite its historical name, this is NOT an
unconditional inhabited-search result: `cert` is an explicit input. -/
theorem beal_10e6_inhabited_forward
    (bound : MatveevBoundCert)
    (level26 : Level26EliminationCert)
    (cert : Full10e6KernelCert) :
    MatveevBoundCert ∧ Level26EliminationCert ∧
      BealMatveevBealV25B0Search.gap3_B_le_B0_no_solution :=
  ⟨bound, level26, B0_10e6_search_forward cert⟩

#print axioms matveev_bound_cert
#print axioms B0_10e6_search_forward
#print axioms beal_10e6_inhabited_forward

end BealMatveevBeal.BealMatveevBealV25B0Search.Full10e6