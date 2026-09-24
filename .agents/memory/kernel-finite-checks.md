---
name: Kernel finite checks
description: Resource constraints when turning a large modular sieve into kernel-checked Lean declarations
---

Finite modular-mask soundness checks can be proved with ordinary `by decide`
and retain only the standard axioms. Checking one 500-value modular interval
also succeeds. Combining many interval checks inside one large theorem is a
different resource problem: a 100-group check approached the container's
memory ceiling, while even ten groups did not finish within five minutes.

**Why:** A successful external enumeration, a sound family of modular masks,
and a successful sample Lean reduction do not together certify every
interval. Kernel reduction still has to finish for the whole covered range.

**How to apply:** Split large finite checks into separately compiled,
importable proof declarations, measure both runtime and memory, and only
replace an explicit certificate boundary after the complete inclusive range
builds and its printed axioms have been inspected. Never use a checkpoint
digest as the missing mathematical proof.