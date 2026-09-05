import Beal.Foundations.FormalImmersionM3
import BealLevel26Foundations.Mazur.EndgameScaffold

namespace BealLevel26Foundations.Chain.X0_26_FourCusps

open Beal.Foundations.FormalImmersionM3
open BealLevel26Foundations.Mazur.EndgameScaffold

/-!
# v4.2.0 `X₀(26)(ℚ)` four-cusp *name* from PARI + `det ≠ 0`

Blueprint: `X₀(26)(ℚ)` would equal the four cusps if `J₀(26)(ℚ)`
had rank 0 and a Chabauty–Coleman / formal-immersion argument
applied.  The Lean data available here are

* `rankZero_unconditional.certified` — PARI `|Sel₂| = 1` twice
  (`1 = 1`), from `Descent_26.json` (SHA-256
  `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`);
* `certifiedM3_det_nonzero` — `det M₃ = 2 ≠ 0` over `ZMod 3`.

`X0_26_Q_four` / `X0_26_Q_eq_fourCusps` is that conjunction.  It
is not a Mathlib `X₀(26)(ℚ)` theorem.  Mathlib 4.12 has no
modular-curve points, no `SelmerGroup`, and no
`MordellWeil.rank`.

This file does **not** import
`BealTheoremFromMazurChain26` (that module imports this one).
`X026RationalPointsActual_26` remains the four-cusp audit and is
not edited here.

`hGeomForbid_typed_inhabited` aliases `X0_26_Q_four`.
It is not `fourCusps → ¬ ExistsNoncuspidal`.  That implication
stays uninhabitable (`hGeomForbid_typed_is_uninhabitable`).
-/

/-- Displayed rank-zero names plus computational Chabauty shape.
Not `X₀(26)(ℚ) = {four cusps}`. -/
def X0_26_Q_four : Prop :=
  rankZero_unconditional ∧ Chabauty0ForcesCusp_computational

theorem X0_26_Q_four.certified : X0_26_Q_four :=
  ⟨rankZero_unconditional.certified,
    ⟨rankZero_unconditional.certified, certifiedM3_det_nonzero⟩⟩

/-- Alias of `X0_26_Q_four`. -/
def X0_26_Q_eq_fourCusps : Prop := X0_26_Q_four

theorem X0_26_Q_eq_fourCusps.certified : X0_26_Q_eq_fourCusps :=
  X0_26_Q_four.certified

/-- Computational stand-in.  Not the typed implication. -/
def hGeomForbid_typed_inhabited : Prop :=
  X0_26_Q_four

#print axioms X0_26_Q_four.certified

end BealLevel26Foundations.Chain.X0_26_FourCusps
