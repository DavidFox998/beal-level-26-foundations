---
name: Frey local-at-two boundary
description: Why the shared factor of 16 does not yield a uniform minimal model or conductor exponent.
---

For the displayed integral Frey model with positive coprime U and V, the common factor of 16 in the invariants does not authorize a universal change of variables by scale 2. If the unique even factor among U, V, and U+V has two-adic valuation below 4, the discriminant valuation is below 12; scratch Lean proofs exclude changes with positive two-adic scale valuation leading to another integral Weierstrass model over either the rationals/integers or Q₂/Z₂. At valuation 4 or above, integral scale-2 changes can exist in each parity pattern, but coefficient congruences must be checked separately.

**Why:** The discriminant scales by the twelfth power, not the fourth power. Scratch checks established the low-valuation obstruction over Q₂/Z₂ and explicit high-valuation integral changes. They do not settle the high-valuation local minimal models or determine a Néron conductor exponent.

**How to apply:** Separate odd/odd, even/odd, and odd/even cases. The low-valuation Q₂/Z₂ result is checked only in external scratch, not promoted to project source. Treat high-valuation minimal models and all conductor questions as open. Do not turn examples outside a Beal solution surface into an arbitrary-exponent elimination.