import BealLevel26Foundations.Real.FreyWeierstrass
import BealLevel26Foundations.Real.Conductor_26_Unconditional
import BealLevel26Foundations.Real.LevelLowering_26
import BealLevel26Foundations.Frey.FreyConductorUnconditional_26
import BealLevel26Foundations.Frey.Conductor_26_Unconditional
import BealLevel26Foundations.Mazur.Genus_26_Real
import BealLevel26Foundations.Mazur.QExpansionCotangent_Real_26
import BealLevel26Foundations.Jacobian.J0_26_DecompActual
import BealLevel26Foundations.Jacobian.PicardAbelJacobiIdentification_26
import BealLevel26Foundations.Jacobian.TwoSelmer_vs_SUnits_26
import BealLevel26Foundations.Jacobian.FormalImmersionActual_26
import BealLevel26Foundations.Jacobian.J0_26_Q_RankZeroActual_26
import BealLevel26Foundations.Mazur.X026RationalPointsActual_26
import BealLevel26Foundations.Ribet.RibetLoweringActual_26
import BealLevel26Foundations.Ribet.NoFreyPointActual_26
import BealLevel26Foundations.Ribet.HIdentifyActual_26
import BealLevel26Foundations.Mazur.HGeomForbidActual_26

namespace BealLevel26Foundations.Real

/-!
# Real arithmetic extension

v2.0.0 gathers the integral Frey Weierstrass model, the odd-prime valuation
input `vₚ(c₄)=0` and `vₚ(Δ)>0`, executable level-26 genus arithmetic, and
the q-expansion matrix calculation. v3.0.0 adds the typed
`LevelLowering_26` certificate: residual prime, weight two, and the
exact-divide relation `M * p = N` with `vₚ(N) = 1`. v4.0.1 adds the Jacobian skeleton: the finite `s₁,s₂` model and certified
`26a × 26b` distinction, plus the standalone Picard `Prop`. v4.0.2
audits the eight S-unit indices against genuine cohomological 2-Selmer
and packages Sage `certified_mwrank = 0` for `26a` and `26b`. v4.0.3
inhabits `FormalImmersionAtTwo26` by q-expansion cotangent injectivity.
It does not claim a Mathlib Jacobian, Ribet transport, Tate/Kodaira
conductor classification, modular-curve Riemann--Hurwitz, a discharged
Picard/Abel--Jacobi comparison, a genuine 2-Selmer identification, a
scheme-theoretic formal immersion, or a Mathlib `X₀(26)(ℚ)` theorem.
v4.0.4 inhabits `X0_26_RationalPoints26` by the displayed four-cusp
finite package. v4.0.5 recorded displayed Ribet existence; v4.0.6
splits that existence (`ExistsFreyWitness`, a Frey model with
`loweredLevel = 26`) from the four-cusp list and inhabits
`J0_26_Q_RankZero26` as the product of two Sage-certified
rank-zero factors. v4.0.7-hIdentify-j packs a Frey `j`-ratio as
an elliptic displayed point (`hIdentify`); the four-cusp list
`[1, 2, 13, 26]` stays as cusps. v4.0.8 records that typed
`hGeomForbid` (`fourCusps → ¬ ExistsNoncuspidal`) is
uninhabitable: constructor inequality does not negate an
elliptic `j`. v4.0.9 retypes four cusps as
`fourCuspsForallCuspPoints` over cusp-labeled points; that
forall does not range over `ellipticJ`, so typed `hGeomForbid`
stays uninhabitable. That is not genuine `Sel₂`, not a Mathlib
`X₀(26)` point, and not an unconditional `BealTheorem`.
-/

end BealLevel26Foundations.Real