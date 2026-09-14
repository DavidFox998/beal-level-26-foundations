# BealCatalanZsig — Catalan / Zsigmondy no-go (not a `B ≤ 10⁶` close)

Lean: [`BealCatalanZsig.lean`](../../BealCatalanZsig.lean)
(root module; `Beal/Matveev/BealCatalanZsig.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealCatalanZsig`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `1a6e6a1` (`v24-v24x-final-Gaussian-Thue-nogo`).
Gap-3 is `C¹³ − B⁴ = A⁴` with `C = B+3`, not Catalan
`X^p − Y^q = 1`. On `B > 0` one has `C¹³ − B⁴ > 1`.
If `3 ∤ B` then `gcd(A,B) = 1`, so a prime dividing `B` does
not divide `A` and cannot force `13 ∣ v_p(A)`. A common
Gaussian divisor of `α` and `ᾱ` still only divides `2A²`
and `2B²`. Even assuming a thirteenth-power factorization,
the argument form still needs `C1 < 5 / log 13 < 2`.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `gap3_not_catalan_shape` / `A_pow_four_eq_sub`.
- `B_even_of_sol`.
- `gcd_A_B_eq_one_of_not_three_dvd_B` /
  `gaussian_coprime_when_three_not_dvd_B`.
- `zsigmondy_prime_in_B_not_dvd_A` /
  `zsigmondy_does_not_force_thirteen_divides_vpA`.
- `padicValNat_freyDiscNat_at_B` / `frey_B_not_ribet_lowered`.
- `gaussian_gcd_divides_two`.
- `baker_bound_gap3_mihailescu_zsigmondy_nogo`: any `C1 ≥ 2`
  (including `C1_floor`, `242`, `2`) has
  `exp(−C1 log C log 13)² < B⁴ / C¹³` on `B ≥ B0`.

## What stays a def Prop

- `baker_bound_gap3` — unconditional `B ≤ 10⁶`.
- `gaussian_associate_thirteenth_power`.
- `zsigmondy_gaussian_primitive_divisor` — existence of a
  primitive prime divisor in `ℤ[i]`. Not in Mathlib 4.12.
- `mihailescu_catalan` — Catalan / Mihăilescu. Not in Mathlib 4.12.
- Darmon–Merel / Ribet / Kraus residual-level.

See also [`BealKrausZsig.md`](BealKrausZsig.md).

Not a minted v25 tag.
