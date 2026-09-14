# BealTrueV25 — axiom-relative `baker_bound_gap3` (not a Mathlib-only v25 mint)

Lean: [`BealTrueV25.lean`](../../BealTrueV25.lean)
(root module; `Beal/Matveev/BealTrueV25.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealTrueV25`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `2b4ee3b` (`v24-v24x-final-genuine-v25-nogo`).
`BealGenuineV25` already proves that Darmon–Merel signature
`(4,4,13)` plus 3-adic descent implies the kernel
`baker_bound_gap3` vacuously. Mathlib 4.12 does not prove that
signature, so this module takes it as

`axiom darmon_merel_4413_axiom : darmon_merel_44_13_no_coprime`

and inhabits `theorem baker_bound_gap3_true : baker_bound_gap3`.
The theorem is named `baker_bound_gap3_true`; the kernel Prop
stays a `def`. 0 sorry.

This is **not** the minted unconditional tag
`v25.0.0-Beal-44-13-Level-26-Baker-B0-Unconditional-foundations`.
That mint still waits on `hGen` and `hLLL`. The inhabitant
depends on `darmon_merel_4413_axiom` in addition to
`[propext, Classical.choice, Quot.sound]`.

## What is proved (0 sorry)

- `axiom darmon_merel_4413_axiom` — Darmon–Merel `(4,4,13)`:
  coprime solutions of `x⁴ + y⁴ = z¹³` have a vanishing factor.
  Not in Mathlib 4.12.
- `no_sol_when_three_dvd_B` — re-export of the `f1cb039` 3-adic
  descent. Axioms `[propext, Classical.choice, Quot.sound]` only
  (no Darmon–Merel axiom).
- `coprime_of_remaining` — remaining solutions have `gcd(A,B) = 1`.
- `no_gap3_of_axiom` — no gap-3 solutions at all, relative to
  the axiom (3-adic branch + coprime branch + `ex falso`).
- `baker_bound_gap3_true` — kernel `baker_bound_gap3`:
  no gap-3 solutions with `B > 10⁶`. Vacuous.
- `baker_bound_gap3_le_B0` — stronger vacuous form:
  `A⁴ + B⁴ = (B+3)¹³ → B ≤ B0_nat`.

`#print axioms baker_bound_gap3_true` is
`[propext, Classical.choice, Quot.sound, BealMatveevBeal.BealTrueV25.darmon_merel_4413_axiom]`.

## What stays a def Prop

- `baker_bound_gap3` — the kernel Prop alias. Do **not** name a
  theorem `baker_bound_gap3`.
- `darmon_merel_44_13_no_coprime` — assumed by the axiom, not
  proved as a theorem.
- `fermat_last_theorem_thirteen`.
- `ribet_level_lowering_to_32` / `ribet_level_lowering`.

GenuineV25 / FLT13 / 44p do **not** contain this axiom.

See also [`BealGenuineV25.md`](BealGenuineV25.md) and
[`BealBakerBoundGap3.md`](BealBakerBoundGap3.md).
