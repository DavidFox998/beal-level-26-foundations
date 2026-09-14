# BealFLT13 — FLT 13 / Darmon–Merel 44p / 3-adic descent no-go (not a `B ≤ 10⁶` close)

Lean: [`BealFLT13.lean`](../../BealFLT13.lean)
(root module; `Beal/Matveev/BealFLT13.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealFLT13`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `515d761` (`v24-v24x-final-Darmon-Merel-44p-nogo`).
Tagged `v24-v24x-final-FLT13-nogo` at `f1cb039`.
`3 ∣ A` is **not** automatic on gap-3: if `B ≡ 2 mod 3` then
`A⁴ ≡ 1 mod 3`. When `3 ∣ B` one does have `3 ∣ A`, and a
three-step 3-adic descent is contradictory: writing
`A = 3 A₁`, `B = 3 B₁`, `C = 3 C₁` with `C₁ = B₁+1` yields
`A₁⁴+B₁⁴ = 3⁹ C₁¹³`, then after two more steps
`27 X = C₁¹³` while `27 ∣ B₁` forces `C₁ ≡ 1 mod 3`, so
`3 ∤ C₁`. Thus there are **no** gap-3 solutions with `3 ∣ B`.
On a solution one therefore has `3 ∤ B` and `gcd(A,B) = 1`,
which is exactly Darmon–Merel's coprime hypothesis. That
theorem, and FLT at exponent 13 (for the thirteenth-power
subcase), are not in Mathlib 4.12. The displayed residual
is still not 32, and `A > B0`.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `three_dvd_both_of_three_dvd_sum_fourth`: fourth powers
  mod 3 are 0 or 1, so `3 ∣ a⁴+b⁴` forces `3 ∣ a` and `3 ∣ b`.
- `no_sol_when_three_dvd_B` / `three_not_dvd_B_of_sol`.
- `coprime_of_sol`: every gap-3 solution is coprime.
- `baker_bound_gap3_flt13_darmon_merel_nogo`: on `B ≥ B0`,
  `¬ 3 ∣ B`, coprime, residual ≠ 32, `A > B0`, `13 ∤ 8`,
  `13 ∣ 26`.

## What stays a def Prop

- `baker_bound_gap3` — unconditional `B ≤ 10⁶`.
- `darmon_merel_44_13_no_coprime` / `darmon_merel_signature_44p`.
- `fermat_last_theorem_thirteen`.
- `ribet_level_lowering_to_32` / `ribet_level_lowering`.

See also [`BealDarmonMerel44p.md`](BealDarmonMerel44p.md),
[`BealGenuineV25.md`](BealGenuineV25.md), and
[`BealTrueV25.md`](BealTrueV25.md).

Not a minted v25 tag.
