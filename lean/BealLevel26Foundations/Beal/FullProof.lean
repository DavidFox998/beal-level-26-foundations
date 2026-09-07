import BealLevel26Foundations.Beal.FullProof.TrueConductor
import BealLevel26Foundations.Beal.FullProof.ModularityRibet
import BealLevel26Foundations.Beal.FullProof.GeometryBridge
import BealLevel26Foundations.Beal.FullProof.ModularImpliesNewform
import BealLevel26Foundations.Beal.FullProof.BealForallProof

/-!
# FullProof track (v8.1.0)

Aggregator for Track B.  Does **not** inhabit
`Beal.BealForall.beal_forall_from_Is13Case_sketch`
(the unguarded type is false; the positive-bases
theorem is conditional on the missing newform arrow).
Step 5 proves the *arithmetic* of
`ModularImpliesLevel2Newform` (Ribet quotient 2,
TW family, `R ≃ T`, displayed `S₂(Γ₀(2))=0`) and
keeps the Mathlib arrow as a Prop.
Not imported by the 24-module none chain.
-/
