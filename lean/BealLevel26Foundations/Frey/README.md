# lean/BealLevel26Foundations/Frey/

Frey-conductor *data* and the v2 odd-prime valuation input. **Current
as of** `v4.0.4-x026-rational-points` / `v2.0.0-frey`.

| File | What it is | What it is not |
|---|---|---|
| `FreyConductorData_26.lean` | Supplied conductor fields for scaffold theorems | Not Tate's algorithm |
| `FreyConductorUnconditional_26.lean` | Re-export of the valuation input | Not `frey_conductor_data` |
| `Conductor_26_Unconditional.lean` | `vₚ(c₄)=0` and `vₚ(Δ)>0` from `p ∤ c₄`, `p ∣ Δ`, `Δ ≠ 0` | Not Kodaira type `I_n` or `N = 2^e rad(ABC)` |

`TateKodairaBoundary26` is an explicit named boundary. These files must
not mention `frey_conductor_data` or `tate_step2_odd_prime_external`.
The Weierstrass model itself is
[`../Real/FreyWeierstrass.lean`](../Real/FreyWeierstrass.lean).
