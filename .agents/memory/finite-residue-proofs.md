---
name: Finite residue proofs
description: How to keep kernel-checked modular obstructions tractable in the full Lean library.
---

For a finite-ring obstruction, separate the mutually exclusive input congruence families before using exhaustive `decide`. Prove each smaller finite implication, then combine them with ordinary Lean reasoning. Do not treat a quick scratch success for one large enumeration as evidence that the same proof will elaborate promptly in the full module.

**Why:** A monolithic decision over several unconstrained residue coordinates passed in isolation but exceeded the full-module direct-check time budget. Splitting by the input residue families made the same kernel-checked argument practical without weakening its statement.

**How to apply:** When continuing local congruence work at higher powers of two, minimize free residue variables in each finite lemma and verify the assembled file, not just the isolated finite calculation. Keep the lift from Q₂ to Z₂ separate from the finite-ring check.