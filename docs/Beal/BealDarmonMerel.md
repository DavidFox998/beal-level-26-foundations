# BealDarmonMerel — Darmon–Merel / Ribet residual-level no-go (not a `B ≤ 10⁶` close)

Lean: [`BealDarmonMerel.lean`](../../BealDarmonMerel.lean)
(root module; `Beal/Matveev/BealDarmonMerel.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealDarmonMerel`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `752f7af` (`v24-v24x-final-Mihailescu-Zsigmondy-nogo`).
Darmon–Merel for `x⁴ + y⁴ = zⁿ` (`n ≥ 4`) needs `gcd(x,y) = 1`.
On gap-3, `3 ∣ B` forces `3 ∣ A`, so `gcd(A,B) ≠ 1` and the
coprime hypothesis fails. When `3 ∤ B` one does have
`gcd(A,B) = 1`, but Darmon–Merel is not in Mathlib 4.12, and
the displayed Frey curve still does not give uniform level 32:
`13 ∣ 26` so primes in `C` lower, while `13 ∤ 8` so a prime
`p ∤ 6` in `A` with `13 ∤ v_p(A)` survives and divides
`residualLevelEstimate`, which therefore does not divide 32.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `three_dvd_A_of_three_dvd_B` / `gcd_A_B_ne_one_of_three_dvd_B`.
- `darmon_merel_hypothesis_fails_when_three_dvd_B`.
- `frey_C_ribet_lowered` (`13 ∣ 26 v_p(C)`).
- `frey_A_prime_survives_when_three_not_dvd_B`.
- `kraus_uniform_residual_level_32_nogo`: an unlowered prime
  in `A` divides the residual estimate, which does not divide 32.
- `baker_bound_gap3_darmon_merel_nogo`: on `B ≥ B0`,
  `3 ∣ B → ¬ Coprime A B`, `A > B0`, `13 ∤ 8`, `13 ∣ 26`.

## What stays a def Prop

- `baker_bound_gap3` — unconditional `B ≤ 10⁶`.
- `darmon_merel_x4_y4_zp_no_coprime_solutions` /
  `darmon_merel_signature_44p` — not in Mathlib 4.12.
- `kraus_uniform_residual_level` / `ribet_level_lowering`.

See also [`BealCatalanZsig.md`](BealCatalanZsig.md),
[`BealKraus.md`](BealKraus.md),
[`BealDarmonMerel44p.md`](BealDarmonMerel44p.md),
[`BealFLT13.md`](BealFLT13.md),
[`BealGenuineV25.md`](BealGenuineV25.md),
[`BealTrueV25.md`](BealTrueV25.md), and
[`BealUnconditionalV25.md`](BealUnconditionalV25.md).

Not a minted v25 tag.
