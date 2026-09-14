# BealDarmonMerel44p — Darmon–Merel signature (4,4,p) / Ribet-to-32 no-go (not a `B ≤ 10⁶` close)

Lean: [`BealDarmonMerel44p.lean`](../../BealDarmonMerel44p.lean)
(root module; `Beal/Matveev/BealDarmonMerel44p.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealDarmonMerel44p`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `406931f` (`v24-v24x-final-Darmon-Merel-nogo`).
Darmon–Merel for signature `(4,4,n)` needs `gcd(x,y) = 1`.
On gap-3, `3 ∣ B` forces `3 ∣ A`, so that hypothesis fails.
When `3 ∤ B` one has `gcd(A,B) = 1`, but Darmon–Merel is not
in Mathlib 4.12. The displayed residual `32 rad(AB)` equals 32
only if `rad(AB) = 1`, hence `A = B = 1` (13th powers). On a
solution with `B > 0`, `B` is even so the residual is not 32.
If every `v_p(n)` is a multiple of 13 then `n` is a 13th power,
and `A = a¹³`, `B = b¹³` rewrites the equation as Fermat
exponent 13, which is not in Mathlib 4.12. `A > B0` and
`13 ∤ 8`.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `residualLevelEstimate_ne_thirty_two_of_sol`.
- `uniform_level_32_requires_A_B_pth_powers`.
- `exists_thirteenth_root_of_thirteen_dvd_padic`.
- `fermat_shape_of_A_B_pth_powers`.
- `baker_bound_gap3_darmon_merel_44p_nogo`: on `B ≥ B0`,
  `3 ∣ B → ¬ Coprime`, residual ≠ 32, `A > B0`, `13 ∤ 8`,
  `13 ∣ 26`.

## What stays a def Prop

- `baker_bound_gap3` — unconditional `B ≤ 10⁶`.
- `darmon_merel_signature_44p`.
- `ribet_level_lowering_to_32` — displayed residual `= 32`
  for every gap-3 solution. Not the Néron conductor.
- `fermat_last_theorem_thirteen`.
- `ribet_level_lowering` / `kraus_uniform_residual_level`.

See also [`BealDarmonMerel.md`](BealDarmonMerel.md) and
[`BealFLT13.md`](BealFLT13.md).

Not a minted v25 tag.
