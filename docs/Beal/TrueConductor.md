# v7.2.0 TrueConductor typed scaffold

`lean/BealLevel26Foundations/Beal/FullProof/TrueConductor.lean`

Step 1 toward inhabiting `beal_forall_from_Is13Case_sketch`
(Tate + true gcd, every prime).  The sketch itself stays
uninhabited.  No `sorry`.  No `False.elim`.

| Name | Status |
|---|---|
| `PrimitiveBealTriple` | packed primitive Beal equation `2 < m,n,p`, `gcd=1` |
| `freyCurveOf` | mixed-exponent Frey model `Y² = X(X − Aᵐ)(X + Bⁿ)` |
| `frey_Delta_of_equation` | `Δ = 16 (Aᵐ)² (Bⁿ)² (Cᵖ)²` by `ring`, not an `rfl` token |
| `frey_c4_formula` | `c₄ = 16 ((Aᵐ)² + Aᵐ Bⁿ + (Bⁿ)²)` by `ring` |
| `pairwise_coprime` | true gcd step: primitive equation ⇒ pairwise coprime |
| `odd_prime_not_dvd_c4` | odd `q ∣ ABC` does not divide `c₄` |
| `odd_prime_c4_val_zero_Delta_val_pos` | `v_q(c₄)=0` and `v_q(Δ)>0` |
| `frey_minimal_model_at_odd_prime` | uninhabited empty-Type witness |
| `frey_conductor_exponent_one_odd` | uninhabited |
| `frey_conductor_two` | uninhabited (not the displayed `2*13` token) |
| `frey_global_conductor` | uninhabited `N = 2 · rad(ABC)` |
| `FreyTwoAdicExponentOneCertificate` | supplier, matching `FreyConductorData_26` |
| `FreyTwoAdicConductorCertificate` | supplier |
| `beal_forall_from_Is13Case_sketch_stays_uninhabited` | lock: the quantified Beal statement is not this file's theorem |

The v7.1.0 `frey_beal_forall_none_formula` none chain is
untouched.  This module is a separate FullProof lake root.
