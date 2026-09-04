import BealLevel26Foundations.Real.FreyWeierstrass
import BealLevel26Foundations.Real.Conductor_26_Unconditional
import BealLevel26Foundations.Real.LevelLowering_26
import BealLevel26Foundations.Frey.FreyConductorUnconditional_26
import BealLevel26Foundations.Frey.Conductor_26_Unconditional
import BealLevel26Foundations.Mazur.Genus_26_Real
import BealLevel26Foundations.Mazur.QExpansionCotangent_Real_26
import BealLevel26Foundations.Jacobian.J0_26_DecompActual
import BealLevel26Foundations.Jacobian.PicardAbelJacobiIdentification_26

namespace BealLevel26Foundations.Real

/-!
# Real arithmetic extension

v2.0.0 gathers the integral Frey Weierstrass model, the odd-prime valuation
input `vₚ(c₄)=0` and `vₚ(Δ)>0`, executable level-26 genus arithmetic, and
the q-expansion matrix calculation. v3.0.0 adds the typed
`LevelLowering_26` certificate: residual prime, weight two, and the
exact-divide relation `M * p = N` with `vₚ(N) = 1`. v4.0.1 adds the Jacobian skeleton: the finite `s₁,s₂` model and certified
`26a × 26b` distinction, plus the standalone Picard `Prop`. It does not
claim a Mathlib Jacobian, Ribet transport, Tate/Kodaira conductor
classification, modular-curve Riemann--Hurwitz, or a discharged
Picard/Abel--Jacobi comparison.
-/

end BealLevel26Foundations.Real