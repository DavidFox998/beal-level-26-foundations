# Integer-form / binary-log LLL no-go (not a v25 mint)

Lean: [`PAdicLLL_ZeroAxiom.lean`](../../PAdicLLL_ZeroAxiom.lean)
(root module; `Beal/Matveev/PAdicLLL_ZeroAxiom.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.PAdicLLL_ZeroAxiom`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `v24-v24x-final-padic-lll-nogo`. Nat/Int only: no
`Real.log`. This file does **not** fork Mathlib and does **not** mint
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.

## Proposed 0-axiom close (rejected)

- scaled binary log `Nat.log 2 n * scale / 1000` in place of
  `scale * Real.log n`;
- the `ℤ`-linear form `u · a + v · C1_floor` with
  `a = log_nat_approx (B+3) C1_floor`;
- a short-vector witness `|u a + v C1| < C1/2` on a gap-3
  solution, then an LLL lower bound `≥ B0`.

That form always vanishes at `(C1_floor, -a)`, with both
coordinates in the claimed box whenever `B ≤ C1_floor`. The
witness does **not** use `A⁴+B⁴=(B+3)¹³`, so it cannot cut
`B ≤ B0`. Separately, `Nat.sqrt C1_floor < B0_nat`, so a
Minkowski *upper* bound from `det = C1_floor` is also smaller
than `B0`. For `det = C1_floor^2` one has
`Nat.sqrt det = C1_floor > B0`, still an upper bound on a short
vector (the opposite of a cutoff).

`#print axioms` on the Nat/Int lemmas is **not** `[]` in
general: `nat_int_form_has_kernel` is `[propext, Quot.sound]`;
the packaged nogo also uses `Classical.choice` via Mathlib
`Nat.sqrt`. Numeral equalities `C1_floor_eq` / `B0_nat_eq`
are axiom-free.

## What stays `def Prop`

- `LLL_reduces_bound_to_B0_zero_axiom`
- `beal_gap3_4_4_13_unconditional_zero_axiom`
- `baker_bound_B0_1e6` / `hGen` / `hLLL`

`matveev_gap3_lower` is the integer-gap Matveev lower bound on
solutions with `B ≤ B0`, not `¬∃ A`. v25 is not minted.
