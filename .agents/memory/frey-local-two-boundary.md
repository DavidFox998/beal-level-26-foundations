---
name: Frey local-at-two boundary
description: Why the shared factor of 16 does not yield a uniform minimal model or conductor exponent.
---

For the displayed integral Frey model with positive coprime U and V, the common factor of 16 in the invariants does not authorize a universal change of variables by scale 2. If the unique even factor among U, V, and U+V has two-adic valuation below 4, the discriminant valuation is below 12; scratch Lean proofs exclude any rational change with positive two-adic scale valuation leading to another globally integral Weierstrass model. At valuation 4 or above, integral scale-2 changes can exist in each parity pattern, but coefficient congruences must be checked separately.

**Why:** The discriminant scales by the twelfth power, not the fourth power. Scratch checks established both the low-valuation obstruction and explicit high-valuation integral changes. Neither result constructs a local Néron minimal model or determines its conductor exponent.

**How to apply:** Separate odd/odd, even/odd, and odd/even cases; use the low-valuation obstruction only with its stated global-integral coordinate-change scope. Treat high valuations and the full Q₂/Z₂ minimal-model and conductor questions as open until a local proof is formalized. Do not turn examples outside a Beal solution surface into an arbitrary-exponent elimination.