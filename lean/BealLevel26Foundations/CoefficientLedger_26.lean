import Mathlib.Tactic

namespace BealLevel26Foundations.CoefficientLedger26

/-!
# The normalized level-26 coefficient ledger

These are the 101 coefficients `a₀,…,a₁₀₀` archived in
`sagemath/level_26_ledger.json` for the LMFDB eigenlines `26a1` and `26b1`.
The repository audit pins that source file by SHA-256.  This module promotes
the same arrays into Lean without assigning them a geometric interpretation.
-/

def qExp_26a1 : List Int :=
  [0, 1, -1, 1, 1, -3, -1, -1, -1, -2, 3, 6, 1, 1, 1, -3, 1, -3, 2, 2,
    -3, -1, -6, 0, -1, 4, -1, -5, -1, 6, 3, -4, -1, 6, 3, 3, -2, -7, -2,
    1, 3, 0, 1, -1, 6, 6, 0, 3, 1, -6, -4, -3, 1, 0, 5, -18, 1, 2, -6,
    -6, -3, 8, 4, 2, 1, -3, -6, 14, -3, 0, -3, -3, 2, 2, 7, 4, 2, -6,
    -1, 8, -3, 1, 0, 12, -1, 9, 1, 6, -6, -6, -6, -1, 0, -4, -3, -6,
    -1, -10, 6, -12, 4]

def qExp_26b1 : List Int :=
  [0, 1, 1, -3, 1, -1, -3, 1, 1, 6, -1, -2, -3, -1, 1, 3, 1, -3, 6, 6,
    -1, -3, -2, -4, -3, -4, -1, -9, 1, 2, 3, 4, 1, 6, -3, -1, 6, 3, 6,
    3, -1, 0, -3, -5, -2, -6, -4, 13, -3, -6, -4, 9, -1, 12, -9, 2, 1,
    -18, 2, -10, 3, -8, 4, 6, 1, 1, 6, -2, -3, 12, -1, -5, 6, -10, 3,
    12, 6, -2, 3, -4, -1, 9, 0, 0, -3, 3, -5, -6, -2, 6, -6, -1, -4,
    -12, 13, -6, -3, 14, -6, -12, -4]

theorem qExp_26a1_length : qExp_26a1.length = 101 := by decide
theorem qExp_26b1_length : qExp_26b1.length = 101 := by decide

theorem ledger_a2 :
    qExp_26a1[2]? = some (-1) ∧ qExp_26b1[2]? = some 1 := by
  decide

/-- The in-kernel ledger is byte-for-byte the displayed pair of arrays. -/
theorem ledger_byteForByte :
    qExp_26a1 =
      [0, 1, -1, 1, 1, -3, -1, -1, -1, -2, 3, 6, 1, 1, 1, -3, 1, -3, 2,
        2, -3, -1, -6, 0, -1, 4, -1, -5, -1, 6, 3, -4, -1, 6, 3, 3, -2,
        -7, -2, 1, 3, 0, 1, -1, 6, 6, 0, 3, 1, -6, -4, -3, 1, 0, 5, -18,
        1, 2, -6, -6, -3, 8, 4, 2, 1, -3, -6, 14, -3, 0, -3, -3, 2, 2,
        7, 4, 2, -6, -1, 8, -3, 1, 0, 12, -1, 9, 1, 6, -6, -6, -6, -1,
        0, -4, -3, -6, -1, -10, 6, -12, 4] ∧
    qExp_26b1 =
      [0, 1, 1, -3, 1, -1, -3, 1, 1, 6, -1, -2, -3, -1, 1, 3, 1, -3, 6,
        6, -1, -3, -2, -4, -3, -4, -1, -9, 1, 2, 3, 4, 1, 6, -3, -1, 6,
        3, 6, 3, -1, 0, -3, -5, -2, -6, -4, 13, -3, -6, -4, 9, -1, 12,
        -9, 2, 1, -18, 2, -10, 3, -8, 4, 6, 1, 1, 6, -2, -3, 12, -1, -5,
        6, -10, 3, 12, 6, -2, 3, -4, -1, 9, 0, 0, -3, 3, -5, -6, -2, 6,
        -6, -1, -4, -12, 13, -6, -3, 14, -6, -12, -4] := by
  exact ⟨rfl, rfl⟩

#print axioms ledger_byteForByte

end BealLevel26Foundations.CoefficientLedger26