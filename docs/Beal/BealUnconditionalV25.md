# BealUnconditionalV25 — `hGen` + `hLLL` no-go (not a minted v25 tag)

Lean: [`BealUnconditionalV25.lean`](../../BealUnconditionalV25.lean)
(root module; `Beal/Matveev/BealUnconditionalV25.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealUnconditionalV25`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `b71eb73` (axiom-relative `baker_bound_gap3_true`).
The minted tag
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`
would require a Mathlib-only close of kernel `baker_bound_gap3`
via `hGen` (Matveev 2000 Thm 1.4 n=2) and `hLLL` (Bugeaud/LLL
reduction). Neither is a theorem in Mathlib 4.12. This module
records that the displayed methods still fail on `B ≥ B0`.
0 sorry. Axioms `[propext, Classical.choice, Quot.sound]` only
(no Darmon–Merel axiom).

## What is proved (0 sorry)

- `hGen_exp_lt_ratio` / `C1_floor_hGen_loses`: every `C1 ≥ 1`,
  including `C1_floor`, has
  `exp(−C1 log A log(B+3)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `hLLL_method_fails`: no scaling `C > 0` yields a Baker–Davenport
  witness `r > 17 + C/B0`.
- `Lambda3_eq_Lambda`: a dummy third logarithm does not change `Λ`.
- `no_uniform_c_cubic_in_N` / `coeffCount3_zero_ten_ten_ten = 1331`.
- `baker_bound_gap3_unconditional_nogo`: on `B ≥ B0` the log and
  LLL methods lose, the remaining solution is coprime with
  residual ≠ 32 and `A > B0`, and Darmon–Merel `(4,4,13)` would
  be refuted. That statement, FLT 13, and Ribet-to-32 stay
  `def Prop`.

## What stays a def Prop

- `hGen` — Matveev 2000 Thm 1.4 n=2, displayed `C1_floor` exponential.
- `hLLL` — `bugeaud_LLL_reduction_proof` (ratio ⇒ `B ≤ B0`).
- `baker_bound_gap3_of_hGen_hLLL` — the composition that would mint
  unconditional v25.
- `baker_bound_gap3` — named theorem stays uninhabited.
- `darmon_merel_44_13_no_coprime` / `fermat_last_theorem_thirteen` /
  `ribet_level_lowering_to_32`.

This module does **not** contain `axiom darmon_merel_4413_axiom`.
The axiom-relative inhabitant is [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag.
