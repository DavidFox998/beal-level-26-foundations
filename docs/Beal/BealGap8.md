# BealGap8 — gap-8 `A⁴ + B⁴ = (B+8)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap8.lean`](../../BealGap8.lean)
(root module; `Beal/Matveev/BealGap8.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap8`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `4e30497` (`v24-v24x-final-gap7-nogo`).
Gap-8 is `C = B+8`, so `gcd(B,C) ∣ 8`. Parity is gap-2/4/6, not
gap-1/5/7: **`A` is even** (odd `A` makes the left side `1` or
`2` mod 16 while even `C` is `0` and odd `C` is odd, never `2`).
**Even `B` dies** after nine divisions by `2`, leaving
`A₉⁴ + B₉⁴ = 8 (64 B₉ + 1)¹³` with residue `8` mod 16
(not gap-2's `2`/`10`, gap-4's `4`/`12`, or gap-6's `6`/`14`).
So **`B` is odd**. `(1,0)` is **not** a solution (`1 ≠ 8¹³`).
Like gap-2 `7a1c53b` and gap-5 `59d8a4a`, **`3 ∣ B` kills
residue** (`C ≡ 2 mod 3`, `C¹³ ≡ 2`, while `A⁴ ∈ {0,1}`).
**`5 ∣ B` kills residue** (`C ≡ 3 mod 5`, `C¹³ ≡ 3`, not in
`{0,1}`). **`7 ∣ B` is compatible** (`C ≡ 1 mod 7`, `A⁴ ≡ 1`).
Remaining solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 8`, but
`B` is odd) and pure Darmon–Merel signature `(4,4,13)`.
0 sorry. No new axiom.

Do **not** prove `B_even_of_sol_gap8` / `A_odd_of_sol_gap8` —
those are the odd-gap parities and are false here. Do **not**
prove `no_sol_when_seven_dvd_B` for gap-8 (`C ≡ 1 mod 7`).

## What is proved (0 sorry)

- `not_gap8_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 8¹³`.
- `gcd_B_C_eq_gcd_eight` / `gcd_B_C_dvd_eight` — `gcd(B,B+8) = gcd(B,8) ∣ 8`.
- `A_even_of_sol_gap8` — odd `A` dies as LHS `1` or `2` mod 16.
- `no_sol_when_even_B` / `B_odd_of_sol_gap8` — nine `/2` leave
  residue `8`, never a sum of fourth powers `{0,1,2}`.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap8` — a common prime
  of `A` and `B` would divide `C` hence divide `8`, so `p=2`,
  but `B` is odd.
- `A_gt_B_of_sol` — `2 B⁴ < (B+8)¹³`, so `A > B` for `B > 0`.
- `no_sol_when_three_dvd_B_gap8` — `3 ∣ B` ⇒ `C ≡ 2 mod 3` ⇒
  `C¹³ ≡ 2`, while `A⁴ ∈ {0,1}`. Same idea as gap-2 / gap-5.
- `no_sol_when_five_dvd_B_gap8` — `5 ∣ B` ⇒ `C ≡ 3 mod 5` ⇒
  `C¹³ ≡ 3`, while `A⁴ ∈ {0,1}`. New for gap-8.
- `A_pow_four_mod7_eq_one_of_seven_dvd_B` /
  `not_seven_dvd_A_of_seven_dvd_B` — `7 ∣ B` ⇒ `C ≡ 1` ⇒
  `A⁴ ≡ 1`, so `7 ∤ A`.
- `coprime_of_remaining_gap8` — after `3 ∤ B` and `5 ∤ B` the
  remaining branch is still coprime (in fact every solution is).
- `hGen_exp_lt_ratio_gap8` / `C1_floor_hGen_loses_gap8` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+8)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap8` — `|4⌊C log A⌋ − 13⌊C log(B+8)⌋ − C Λ| < 17`
  for every real `C` (`B+8`).
- `hLLL_method_fails_gap8` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap8` / `coeffCount3_zero_ten_ten_ten_gap8 = 1331`
  / `no_uniform_c_easy_half_gap8` — `(1/2)·1·1 < 242`; Philippon
  is not in Mathlib 4.12.
- `baker_bound_gap8_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; remaining solutions are coprime with `A > B0`,
  `B` odd, `A` even; `3 ∣ B` and `5 ∣ B` are impossible;
  `7 ∣ B` forces `7 ∤ A`; Darmon–Merel `(4,4,13)` would be
  refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap8_of_axiom` / `baker_bound_gap8_true` /
  `baker_bound_gap8_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-8 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as even. Not named `baker_bound_gap8`.

## What stays a def Prop

- `baker_bound_gap8` — named theorem stays uninhabited.
- `hGen_gap8` / `hLLL_gap8` / `baker_bound_gap8_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap8`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag. Successor: [`BealGap9.md`](BealGap9.md)
`C = B+9`, `B` even, `3 ∣ B` dies by 3-descent, `5 ∣ B` dies as
`C ≡ 4`.
