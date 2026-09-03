import BealLevel26Foundations.CoefficientLedger_26
import BealLevel26Foundations.M3_Explicit
import BealLevel26Foundations.AbelJacobiDifferential

namespace BealLevel26Foundations.Mazur.QExpansionCotangentReal26

open BealLevel26Foundations.CoefficientLedger26
open BealLevel26Foundations.M3Explicit
open BealLevel26Foundations.AbelJacobiDifferential

/-!
# Real q-expansion coefficient calculation at level 26

The kernel checks the normalized `a₁,a₂` coefficients, the coefficient matrix,
the basis change, and their product `M₃`. The formal-coordinate calculation below does not construct the geometric
Picard/Abel--Jacobi map. The identification of an independently supplied actual
cotangent differential with this coefficient calculation remains explicit.
-/

def qExpansionCoefficientMatrix26 :
    Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  C3

theorem qExpansionCoefficientMatrix26_eq :
    qExpansionCoefficientMatrix26 = !![1, 1; 2, 1] :=
  C3_eq

def qExpansionCotangentMatrix26 :
    Matrix (Fin 2) (Fin 2) (ZMod 3) :=
  P * qExpansionCoefficientMatrix26

theorem qExpansionCotangentMatrix26_eq_M3 :
    qExpansionCotangentMatrix26 = ledgerM3 := by
  rfl

theorem qExpansionCotangentMatrix26_explicit :
    qExpansionCotangentMatrix26 = !![1, 1; 0, 2] := by
  exact ledgerM3_eq

/-- Narrow remaining geometric statement: the actual Abel--Jacobi
differential, represented in the chosen cotangent bases, agrees with the
matrix computed from q-expansion coefficients. -/
def PicardAbelJacobiIdentification_26
    (actual_dAJ_at_infinity : Matrix (Fin 2) (Fin 2) (ZMod 3)) : Prop :=
  actual_dAJ_at_infinity = qExpansionCotangentMatrix26

theorem qExpansion_cotangent_compatibility_of_picard_bridge
    {actual_dAJ_at_infinity : Matrix (Fin 2) (Fin 2) (ZMod 3)}
    (hPicard :
      PicardAbelJacobiIdentification_26 actual_dAJ_at_infinity) :
    actual_dAJ_at_infinity = ledgerM3 := by
  rw [hPicard]
  exact qExpansionCotangentMatrix26_eq_M3

theorem qExpansion_compatibility_of_picard_bridge
    {actual_dAJ_at_infinity : Matrix (Fin 2) (Fin 2) (ZMod 3)}
    (hPicard :
      PicardAbelJacobiIdentification_26 actual_dAJ_at_infinity) :
    actual_dAJ_at_infinity = ledgerM3 :=
  qExpansion_cotangent_compatibility_of_picard_bridge hPicard

#print axioms qExpansionCoefficientMatrix26_eq
#print axioms qExpansionCotangentMatrix26_explicit
#print axioms qExpansion_cotangent_compatibility_of_picard_bridge

end BealLevel26Foundations.Mazur.QExpansionCotangentReal26