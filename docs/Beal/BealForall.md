# v4.49.0 Beal forall sketch from the 13-case

`lean/BealLevel26Foundations/Beal/BealForall.lean`

`beal_forall_from_Is13Case_sketch` is the Beal statement

`∀ A B C m n p, 2 < m,n,p → A^m+B^n=C^p → gcd(A,B,C) > 1`.

Valid type.  Uninhabited.

| Name | Status |
|---|---|
| `Is13CaseForcesFalseSketchViaLevel2` | `∀ w, Is13Case w → False` on bases; uninhabited; needs Tate + Ribet |
| `Is13CaseForcesGcdGt1Sketch` (this file) | `13 ∣ A*B*C → gcd > 1` on bases; uninhabited |
| `Is13CaseForcesGcdGt1Sketch` (Forall) | packed `w.gcd > 1`; uninhabited |
| `beal_forall_from_Is13Case_sketch` | `∀ A B C m n p` Beal; uninhabited; needs Tate + Ribet + GcdGt1 and levels `2p` for other primes |
| `beal_forall_from_Is13Case_composition` | the two 13-case sketches imply Beal; uninhabited (they do not) |

Real `X₀(26)(ℚ)` has `26a1` (Δ `-17576`) and `26b1`
(Δ `-1664`).  The 13-case contradiction is level 2, no
newform.  Still not `∀ A B C` in the kernel.

### v4.50.0 why GcdGt1 is uninhabited

`Is13Case_prime_dvd` (**none**): prime 13 divides one
factor of `A*B*C`.  `Is13Case_gcd_counterexample` is
`⟨13, 2, 1⟩` with `gcd = 1`.  So
`∀ w, Is13Case w → w.gcd > 1` is false on bases.
`not_Is13CaseForcesGcdGt1Sketch` records that (**none**,
`Nat.lt_irrefl`).  The packed Forall twin stays
uninhabited (`gcd = 1` by `primitive`).
