# BealKraus — displayed Frey / Kraus no-go (not a `B ≤ 10⁶` close)

Lean: [`BealKraus.lean`](../../BealKraus.lean)
(root module; `Beal/Matveev/BealKraus.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealKraus`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `62383af` (`v24-v24x-final-logs-nogo`).
The displayed model `y² = x(x − A⁴)(x + B⁴)` has Weierstrass
discriminant `16 A⁸ B⁸ (A⁴+B⁴)²`, hence
`16 A⁸ B⁸ (B+3)²⁶` on a gap-3 solution.

Ribet at `p = 13` would remove primes `ℓ` with `13 ∣ v_ℓ(Δ)`.
Here `v_C(Δ) = 26 v_C(C)` when `C` is coprime to `2AB`, and
`13 ∣ 26`, so `C = B+3` **is** a lowering candidate — the
residual level is **not** forced to grow with `C`. A naive
`N_p ≥ C/2` claim is the wrong shape for Kraus/Ribet.

By contrast `v_A(Δ) = 8 v_A(A)` and `13 ∤ 8`, so a prime
`p ∤ 6` dividing `A` is removed only if `13 ∣ v_p(A)`. That
is the opposite of Fermat, where every prime in `ABC` has
`p ∣ v_ℓ(Δ)`. This curve does not produce a uniform
level-`32` newform check. Mathlib 4.12 has no Ribet,
Darmon–Merel, or Kraus newform table.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `gcd_B_C_dvd_three`: `gcd(B, B+3) ∣ 3`.
- `A_odd_of_sol`: `A` is odd on a gap-3 solution.
- `prime_dvd_A_B_eq_three` / `prime_dvd_A_C_eq_three`: a common
  prime of `A` and `B` or of `A` and `B+3` is `3`.
- `freyWeierstrass_Δ` / `freyDiscNat_of_sol`.
- `not_thirteen_dvd_eight` / `thirteen_dvd_twenty_six`.
- `padicValNat_freyDiscNat_at_A`: `v_p(Δ) = 8 v_p(A)` for
  `p ≠ 2` not dividing `B(B+3)`.
- `padicValNat_freyDiscNat_at_C`: `v_p(Δ) = 26 v_p(C)` for
  `p ≠ 2` not dividing `AB`.
- `frey_A_not_ribet_lowered` / `frey_C_ribet_lowered_candidate`.
- `baker_bound_gap3_kraus_nogo`: on a solution with `B ≥ B0`,
  a prime `p ∤ 6` dividing `A` with `13 ∤ v_p(A)` is not
  lowered, and `A > B0`.

## What stays a def Prop

- `baker_bound_gap3` — unconditional `B ≤ 10⁶`.
- `darmon_merel_signature_44p` — Darmon–Merel `(4,4,n)` for
  `n ≥ 4`. Not in Mathlib 4.12.
- `kraus_uniform_residual_level` — residual level `≤ 64` for
  every gap-3 Frey curve.
- `ribet_level_lowering` — Ribet as a modularity theorem.
- `wuestholz_product_theorem_exp` / `baker_davenport_reduction`.

See also [`BealKrausZsig.md`](BealKrausZsig.md) for the
Gaussian / Thue argument-form no-go.

Not a minted v25 tag.
