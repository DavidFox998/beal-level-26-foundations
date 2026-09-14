# BealKrausZsig — Gaussian / Zsigmondy / Thue no-go (not a `B ≤ 10⁶` close)

Lean: [`BealKrausZsig.lean`](../../BealKrausZsig.lean)
(root module; `Beal/Matveev/BealKrausZsig.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealKrausZsig`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `b6b426a` (`v24-v24x-final-Kraus-nogo`).
On a gap-3 solution, `A⁴ + B⁴ = N(A² + i B²) = (B+3)¹³` in
`ℤ[i]`. If unique factorization produced
`A² + i B² = ε (u+iv)¹³` with `u² + v² = C = B+3`, the
argument form would satisfy `|sin(13θ)| = B² / C^{13/2}`,
equivalently after squaring `B⁴ / C¹³`.

A Matveev-style lower bound `exp(−C1 log C log 13)` beats
that upper bound only for `C1 < 5 / log 13 < 2`. Every
constant we actually have — `C1_floor`, the jet `242`, even
`C1 = 2` — is too large, so the squared exponential is
strictly smaller than `B⁴ / C¹³` on `B ≥ B0`. This is a
different cutoff from the two-log comparison (which needed
`C1 < 1` versus `B⁴/A⁴`); `C1 = 1` would win *if* it applied
here, but `C1 ≥ 2` loses.

Zsigmondy primitive divisors and Mihăilescu / Catalan are
not in Mathlib 4.12. The Gaussian thirteenth-power
factorization is not proved: a common divisor of `α` and
`ᾱ` divides `2A²` and `2B²`, which is not coprimeness.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `log_thirteen_gt_five_div_two` / `five_div_log_thirteen_lt_two`.
- `gaussianAlpha_norm` / `gaussianAlpha_norm_of_sol`.
- `gaussianAlpha_add_star` / `gaussianAlpha_sub_star` /
  `gaussian_common_dvd`.
- `baker_bound_gap3_gaussian_nogo` /
  `baker_bound_gap3_z_i_nogo`: any `C1 ≥ 2` has
  `exp(−C1 log C log 13)² < B⁴ / C¹³` on `B ≥ B0`.
- `C1_floor_gaussian_nogo` / `two_forty_two_gaussian_nogo` /
  `two_gaussian_nogo`.
- Re-export: `13 ∣ 26` / `13 ∤ 8`.

## What stays a def Prop

- `baker_bound_gap3` — unconditional `B ≤ 10⁶`.
- `gaussian_associate_thirteenth_power` — UFD factorization
  `A² + i B² = ε (u+iv)¹³`.
- `zsigmondy_gaussian_primitive_divisor` — primitive prime
  divisors of `αⁿ − βⁿ` in `ℤ[i]`.
- `mihailescu_catalan` — Catalan / Mihăilescu. Gap-3 is
  `C¹³ − B⁴ = A⁴`, not Catalan shape.
- Darmon–Merel / Ribet / Kraus residual-level (re-exported).

See also [`BealKraus.md`](BealKraus.md),
[`BealCatalanZsig.md`](BealCatalanZsig.md), and
[`BealDarmonMerel.md`](BealDarmonMerel.md).

Not a minted v25 tag.
