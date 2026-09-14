# BealGenuineV25 — Darmon–Merel (4,4,13) + 3-adic vacuous-close no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGenuineV25.lean`](../../BealGenuineV25.lean)
(root module; `Beal/Matveev/BealGenuineV25.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGenuineV25`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `f1cb039` (`v24-v24x-final-FLT13-nogo`).
3-adic descent already rules out `3 ∣ B`. Every remaining
solution is coprime. If Darmon–Merel signature `(4,4,13)` were
a theorem there would be no gap-3 solutions at all, and
`baker_bound_gap3` would hold vacuously. It is not a theorem
in Mathlib 4.12 (nor FLT 13, nor Ribet-to-32). A putative
solution with `B ≥ B0` would refute Darmon–Merel `(4,4,13)`.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `no_sol_when_three_dvd_B_of_f1cb039` / `coprime_of_remaining_sol`
  re-export the 3-adic descent.
- `no_gap3_of_darmon_merel_4413`: Darmon–Merel `(4,4,13)` ⇒
  no gap-3 solutions (3-adic branch + coprime branch).
- `baker_bound_gap3_of_no_gap3` / `baker_bound_gap3_of_darmon_merel_4413`:
  the vacuous implication. Does **not** inhabit Darmon–Merel.
- `baker_bound_gap3_darmon_merel_4413_3adic_nogo`: on `B ≥ B0`,
  `¬ 3 ∣ B`, coprime, residual ≠ 32, `A > B0`, `13 ∤ 8`,
  `13 ∣ 26`, and `darmon_merel_44_13_no_coprime → False`.

## What stays a def Prop

- `baker_bound_gap3` — unconditional `B ≤ 10⁶`.
- `darmon_merel_44_13_no_coprime` / `darmon_merel_signature_44p`.
- `fermat_last_theorem_thirteen`.
- `ribet_level_lowering_to_32` / `ribet_level_lowering`.

See also [`BealFLT13.md`](BealFLT13.md).

Not a minted v25 tag.
