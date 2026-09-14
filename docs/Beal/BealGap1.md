# BealGap1 — gap-1 `A⁴ + B⁴ = (B+1)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap1.lean`](../../BealGap1.lean)
(root module; `Beal/Matveev/BealGap1.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap1`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `563e8e3` (`v24-v24x-final-unconditional-nogo`).
Gap-1 is `C = B+1`, so `gcd(B,C) = 1`. Any solution is coprime from
the start. Unlike gap-3 (`f1cb039`), `3 ∣ B` does **not** force a
3-adic contradiction: `C ≡ 1 mod 3` and `A⁴ ≡ 1` is possible, so
`3 ∤ A`. The remaining equation is pure Darmon–Merel signature
`(4,4,13)` for every `B > 0`. `(A,B) = (1,0)` is a genuine
solution with `B = 0 ≤ B0`. 0 sorry. No new axiom.

## What is proved (0 sorry)

- `gap1_one_zero` — `(1,0)` solves `1⁴ + 0⁴ = 1¹³`.
- `gcd_B_C_eq_one` / `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap1`
  — `gcd(B,B+1) = 1`; a common prime of `A` and `B` would divide
  `C`, so every solution is coprime.
- `B_even_of_sol_gap1` / `A_odd_of_sol_gap1` — if `B` is odd then
  `C` is even, `16 ∣ C¹³`, while fourth powers mod 16 are `0` or
  `1` and the sum is `1` or `2`. So `B` is even and `A` is odd.
- `A_gt_B_of_sol` — `2 B⁴ < (B+1)¹³` for `B > 0`, so `A > B`.
- `not_three_dvd_A_of_three_dvd_B` / `A_pow_four_mod3_eq_one_of_three_dvd_B`
  — `3 ∣ B` forces `A⁴ ≡ 1 mod 3` and `3 ∤ A`. This is the
  **opposite** of gap-3. Do **not** prove `no_sol_when_three_dvd_B`
  for gap-1: mod 3 does not kill `3 ∣ B`.
- `A_pow_four_mod5_eq_one_of_five_dvd_B` — `5 ∣ B` likewise forces
  `A⁴ ≡ 1 mod 5`; no elementary 5-adic kill.
- `hGen_exp_lt_ratio_gap1` / `C1_floor_hGen_loses_gap1` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+1)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap1` — `|4⌊C log A⌋ − 13⌊C log(B+1)⌋ − C Λ| < 17`
  for every real `C` (`B+1`, not `B+3`).
- `hLLL_method_fails_gap1` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap1` / `coeffCount3_zero_ten_ten_ten_gap1 = 1331`
  / `no_uniform_c_easy_half_gap1` — `(1/2)·1·1 < 242`; Philippon
  is not in Mathlib 4.12.
- `baker_bound_gap1_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; remaining solutions are coprime with `A > B0`,
  `B` even, `A` odd; `3 ∣ B` is compatible and forces `3 ∤ A`;
  Darmon–Merel `(4,4,13)` would be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_pos_gap1_of_axiom` / `baker_bound_gap1_true` — axiom-relative
  vacuous close for `B > 0`, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `(1,0)` remains a solution. Not named `baker_bound_gap1`.

## What stays a def Prop

- `baker_bound_gap1` — named theorem stays uninhabited.
- `hGen_gap1` / `hLLL_gap1` / `baker_bound_gap1_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap1`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag. Next: gap-2 `C = B+2` in [`BealGap2.md`](BealGap2.md).
