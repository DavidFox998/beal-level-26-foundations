---
name: Concrete p-adic valuations
description: A Lean proof-performance trap when checking concrete p-adic valuations.
---

Direct numeral normalization on concrete `padicValNat` goals can run for more than a minute without producing an answer, even when the arithmetic value is small. Prefer factoring out the prime power and establishing that the remaining positive factor is not divisible by the prime; then use the valuation multiplication and zero-of-not-divisible results.

**Why:** A direct tactic probe on small local-at-two values timed out without output, whereas an analytic factorization checked promptly. This is a proof-search/performance caution, not a mathematical obstruction.

**How to apply:** When a concrete valuation goal appears to hang, avoid increasing timeouts or unfolding the evaluator. Move ordinary numeral arithmetic outside the valuation and prove the factor's coprimality separately.