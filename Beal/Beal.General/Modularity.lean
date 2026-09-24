import Beal.«Beal.General».Conductor
import Beal.«Beal.General».TwoPower

/-!
No general modularity-to-`commonPrime` theorem is declared here. The
general Frey invariant identities and low-local obstruction now exist,
but neither supplies the six general forward fields or eliminates 2^k.

OPEN PROOF OBLIGATIONS (not axioms, theorems, or certificates):

* TateGeneral TODO: general Tate uniformization, high-valuation
  minimal models, Néron/inertia data and an actual conductor formula.
* MazurX0_l TODO: residual irreducibility and Borel exclusion for all
  relevant odd primes ℓ, not only the specialized X₀(13) setting.
* RibetGeneral TODO: modularity and justified level lowering from
  the general conductor, not only the specialized 928→32 step.
* KrausGeneral TODO: actual elimination at the resulting general
  levels; the 32a1 eigenform and a29=-10 comparison are specialized.
* KolyvaginGeneral TODO: the needed L-value, Selmer and rank inputs
  under their correct hypotheses, not only the 32a1 data.
* TwoPowerGeneral TODO: construct the unsupplied `(4,4,n)` requirement
  where applicable and handle all other 2^k exponent signatures.
* Construct the six *general* forward fields and a proved bridge to
  `BealTheoremData.commonPrime`. Neither
  `RequiresTateMazurRibetForwardData` nor the specialized
  `Conditional32BridgeData`/`HasNewformAtLevel32` does this.

Absence of these proofs does not establish formal non-entailment.
There is deliberately no asserted `commonPrime` theorem, no
String/Bool substitute, and no proposed release certificate.
-/

namespace Beal.General

#check freyWeierstrassGeneral
#check frey_low_minimal_Q2
#check frey_c4_v2_of_coprime
#check branch_separate
#check RequiredNoPrimitive44n
#check two_power_needs_darmon_merel

end Beal.General