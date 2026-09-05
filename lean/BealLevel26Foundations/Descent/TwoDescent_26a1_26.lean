import BealLevel26Foundations.Descent.EllipticCurve_26a1_26b1_26
import BealLevel26Foundations.Certs.LMFDBCert_26
import Mathlib.Tactic

namespace BealLevel26Foundations.Descent.TwoDescent26

open BealLevel26Foundations.Descent.EC26
open BealLevel26Foundations.Certs.LMFDBCert26

/-!
# v4.1.0 displayed 2-descent / Selmer-bound names

Blueprint: a genuine 2-descent would compute `E(ℚ)/2E(ℚ)` from
2-coverings `C_d : d w² = f(x)`.  For `26a1` the full 2-torsion is
not rational, so 2-isogeny descent is unavailable.

This file does not compute homogeneous spaces.  Mathlib 4.12 has no
`SelmerGroup` and no two-descent.  Not a Selmer group.  Not a
two-descent.

`TwoCoverings_26a1_finitePackage` / `TwoCoverings_26b1_finitePackage`
are the displayed LMFDB rows from `LMFDBCert_26`, not 2-coverings.

`SelmerBound_26a1` / `SelmerBound_26b1` are the displayed torsion
orders `3` and `7` (`Z/3Z`, `Z/7Z`).  They are not `|Sel₂|`.  Even
under rank `0` and `Sha[2] = 0`, `|E(ℚ)/2E(ℚ)| = 2ʳ · |E(ℚ)[2]|`,
and `E(ℚ) ≅ ℤ/3ℤ` has trivial 2-torsion.

The frozen v1.4.0 ledger SHA-256
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`
is unchanged.
-/

/-- Displayed LMFDB `26.a1` row.  Not a two-descent covering. -/
def TwoCoverings_26a1_finitePackage : Prop := LMFDB_26a1_rankZero

/-- Displayed LMFDB `26.b1` row.  Not a two-descent covering. -/
def TwoCoverings_26b1_finitePackage : Prop := LMFDB_26b1_rankZero

/-- Displayed LMFDB torsion order for `26a1` (`Z/3Z`).  Not a Selmer
group and not `|Sel₂|`.  Mathlib 4.12 has no `SelmerGroup`. -/
def SelmerBound_26a1 : ℕ := 3

/-- Displayed LMFDB torsion order for `26b1` (`Z/7Z`).  Not a Selmer
group and not `|Sel₂|`. -/
def SelmerBound_26b1 : ℕ := 7

theorem SelmerBound_26a1_certified : SelmerBound_26a1 = 3 := rfl
theorem SelmerBound_26b1_certified : SelmerBound_26b1 = 7 := rfl

theorem TwoCoverings_26a1_is_displayed_LMFDB :
    TwoCoverings_26a1_finitePackage = LMFDB_26a1_rankZero :=
  rfl

theorem TwoCoverings_26b1_is_displayed_LMFDB :
    TwoCoverings_26b1_finitePackage = LMFDB_26b1_rankZero :=
  rfl

/-- Named boundary: Mathlib has no `SelmerGroup`, no two-descent. -/
theorem SelmerBound_26a1_matches_displayed_torsion_string :
    lmfdb26a1.torsion = "Z/3Z" ∧ SelmerBound_26a1 = 3 :=
  ⟨rfl, rfl⟩

theorem SelmerBound_26b1_matches_displayed_torsion_string :
    lmfdb26b1.torsion = "Z/7Z" ∧ SelmerBound_26b1 = 7 :=
  ⟨rfl, rfl⟩

theorem SelmerBound_26a1_on_certified_conductor :
    EC_26a1_conductor = 26 ∧ SelmerBound_26a1 = 3 :=
  ⟨rfl, rfl⟩

theorem SelmerBound_26b1_on_certified_conductor :
    EC_26b1_conductor = 26 ∧ SelmerBound_26b1 = 7 :=
  ⟨rfl, rfl⟩

#print axioms SelmerBound_26a1_certified
#print axioms SelmerBound_26b1_certified

end BealLevel26Foundations.Descent.TwoDescent26
