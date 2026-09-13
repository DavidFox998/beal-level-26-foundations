# MatveevLLL — elementary continued-fraction lemmas (not Baker B0)

Lean: [`MatveevLLL.lean`](../../MatveevLLL.lean)
(root module; `Beal/Matveev/MatveevLLL.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.MatveevLLL`.
Concept DOI `10.5281/zenodo.22379293`. C1_floor stays `143186215390`.

## What is proved (0 sorry)

On a gap-3 solution $A^4+B^4=(B+3)^{13}$ with $B>0$:

- `B0_nat = 1000000` (`rfl` to Level 26 `baker_B0`).
- Displayed Bugeaud scaling `LLL_C_nat = 10^30` and basis
  `e1 = (1, 0)`, `e2 = (floor(C log A), floor(C log(B+3)))` as
  definitions only. Mathlib 4.12 has no LLL theorem that turns
  this lattice into `B ≤ 10^6`.
- `|log(B+3)/log A − 4/13| = |Λ|/(13 log A) ≤ (B^4/A^4)/(13 log A)`.
- `B^4/A^4 < 1/((B+3)^9 − 1)`.
- The error is `< 1/(2 · 13^2)`, so Legendre's theorem gives
  `four_thirteenths_is_convergent`: `4/13` is a convergent of the
  log ratio. This is **expected** (`A^4 ≈ (B+3)^{13}`), not a
  contradiction.
- `integer_gap_lt_ratio`: `1/(B+3)^{13} < B^4/A^4`. The integer-gap
  theorem `matveev_thm14_n2_explicit_of_nat` is at most this gap,
  so it never contradicts `|Λ| ≤ B^4/A^4` and never forces `B ≤ 10^6`.
- `abs_Lambda_tight_sandwich`: `B^4/(B+3)^{13} ≤ |Λ| ≤ B^4/A^4`
  via `log(1+u) ≥ u/(1+u)`. Same order (ratio of sides is
  `(B+3)^{13}/A^4 = 1 + B^4/A^4`). Still no cutoff.

Axioms: `[propext, Classical.choice, Quot.sound]` only.

## What stays a def Prop

- `baker_bound_gap3_from_ratio` — “solution and `|Λ| ≤ B^4/A^4` ⇒ `B ≤ B0_nat`”.
- `bugeaud_LLL_reduction_proof` — same Prop; **not** a theorem.
- `baker_davenport_reduction` — same Prop; Mathlib 4.12 has no
  Baker–Davenport / Bugeaud LLL theorem.
- Level 26 `baker_bound_gap3` — `∀ B > 10^6, ¬∃ A`.

`baker_bound_gap3_of_from_ratio` shows that inhabiting the
implication form inhabits Level 26 `baker_bound_gap3` (the proved
`|Λ| ≤ B^4/A^4` is already available). That is the v25 close, and
it is still open.

Unrestricted `matveev_theorem_1_4_gap3_target` stays a `def Prop`.
No `matveev_gap3_lower_unrestricted` theorem. No minted
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional` tag.
