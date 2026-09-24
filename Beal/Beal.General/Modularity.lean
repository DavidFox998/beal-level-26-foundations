import Beal.«Beal.General».Conductor
import Beal.«Beal.General».TwoPower

/-!
No general modularity-to-`commonPrime` theorem is declared here. The
general Frey invariant identities and low-local obstruction now exist,
but neither supplies the six general forward fields or eliminates 2^k.

OPEN PROOF OBLIGATIONS (not axioms, theorems, or certificates):

* General Tate uniformization and local Néron/inertia data, including
  a proved conductor for the general Frey model.
* General residual irreducibility/Borel exclusion for relevant odd
  primes ℓ, with valid modularity and level lowering at the resulting
  levels. The specialized X₀(13), 29, 928→32 and 32a1 computations
  do not quantify over ℓ and arbitrary solutions.
* A valid general replacement for the specialized 32a1 L-value,
  Selmer and Kolyvagin hypotheses where they are actually needed.
* An elimination for the separate pure 2^k exponent branch.
* Proofs of the six general analogues of the
  `RequiresTateMazurRibetForwardData` fields and the necessary bridge
  to `BealTheoremData.commonPrime`. The specialized
  `Conditional32BridgeData`/`HasNewformAtLevel32` is not that bridge.

Absence of these proofs does not establish formal non-entailment.
There is deliberately no asserted `commonPrime` theorem, no
String/Bool substitute, and no proposed release certificate.
-/

namespace Beal.General

#check freyWeierstrassGeneral
#check frey_low_minimal_Q2
#check frey_c4_v2_of_coprime
#check branch_separate

end Beal.General