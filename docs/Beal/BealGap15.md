# BealGap15 — gap-15 `A⁴ + B⁴ = (B+15)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap15.lean`](../../BealGap15.lean)
(root module; `Beal/Matveev/BealGap15.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap15`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `d382439` (`v24-v24x-final-gap14-nogo`).
Gap-15 is `C = B+15`, so `gcd(B,C) ∣ 15 = 3·5`. Parity is
gap-1/5/7/9/11/13, not gap-2/4/6/8/10/12/14: **`B` is even**
and **`A` is odd**. Odd `B` makes `C` even, so `C¹³ ≡ 0` mod 16
while `A⁴ + B⁴ ≡ 1` or `2`. `(1,0)` is **not** a solution
(`1 ≠ 15¹³`). **`3 ∣ B` kills by 3-descent** (`15 ≡ 0 mod 3`):
`A=3A₁ B=3B₁ C=3(B₁+5)` gives `A₁⁴+B₁⁴=3⁹ C₁¹³` (`3⁹ = 19683`);
fourth powers mod 3 are `{0,1}` and sum `0` only `0+0`, so
further `/3` leave `27 X = (B₁+5)¹³` while `B₁+5 ≡ 2 mod 3`
(like gap-3 `563e8e3`, gap-6 `8425abd`, gap-12 `eeff2cd`).
**`5 ∣ B` kills by 5-descent** (`15 ≡ 0 mod 5`):
`A=5A₁ B=5B₁ C=5(B₁+3)` gives `A₁⁴+B₁⁴=5⁹ C₁¹³`
(`5⁹ = 1953125`); further `/5` leave `125 X = (B₁+3)¹³` while
`B₁+3 ≡ 3 mod 5` (like gap-5 `59d8a4a` / gap-10, keeping
`B₁+3` throughout). **`7 ∣ B` is compatible** (`C ≡ 1 mod 7`,
`A⁴ ≡ 1`). Remaining solutions are coprime
(`p ∣ A,B` ⇒ `p ∣ 15`, but `3 ∤ B` and `5 ∤ B`) and pure
Darmon–Merel signature `(4,4,13)`, including the `7 ∣ B`
branch. 0 sorry. No new axiom.

Do **not** prove `B_odd_of_sol_gap15` / `A_even_of_sol_gap15`
/ `no_sol_when_even_B` — those are the even-gap parities and
are false here. Do **not** prove `no_sol_when_seven_dvd_B`.

## What is proved (0 sorry)

- `not_gap15_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 15¹³`.
- `gcd_B_C_eq_gcd_fifteen` / `gcd_B_C_dvd_fifteen` /
  `gcd_B_C_dvd_fifteen_gap15` — `gcd(B,B+15) = gcd(B,15) ∣ 15`.
- `B_even_of_sol_gap15` — odd `B` dies mod 16 (`C` even ⇒ RHS `0`,
  LHS `1` or `2`).
- `A_odd_of_sol_gap15` — even `A` would make the left side even
  while even `B` makes `C` odd.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap15` /
  `gcd_A_B_eq_one_of_remaining_gap15` — a common prime of `A`
  and `B` would divide `C` hence divide `15`, so `p=3` or `p=5`;
  both die by the descents below.
- `A_gt_B_of_sol` — `2 B⁴ < (B+15)¹³`, so `A > B` for `B > 0`.
- `three_dvd_B_forces_three_dvd_A_gap15` — `3 ∣ B` ⇒ `C ≡ 0` ⇒
  `A⁴ ≡ 0` ⇒ `3 ∣ A`.
- `no_sol_when_three_dvd_B_gap15` — 3-descent last step
  `27 X = (B₁+5)¹³` with `B₁+5 ≡ 2`.
- `five_dvd_B_forces_five_dvd_A_gap15` — `5 ∣ B` ⇒ `C ≡ 0` ⇒
  `A⁴ ≡ 0` ⇒ `5 ∣ A`.
- `no_sol_when_five_dvd_B_gap15` — 5-descent last step
  `125 X = (B₁+3)¹³` with `B₁+3 ≡ 3`.
- `seven_dvd_B_compat_gap15` / `A_pow_four_mod7_eq_one_of_seven_dvd_B`
  — `C ≡ 1`, so `A⁴ ≡ 1`. `not_seven_dvd_A_of_seven_dvd_B`
  follows from coprimeness.
- `hGen_exp_lt_ratio_gap15` / `C1_floor_hGen_loses_gap15` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+15)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap15` — `|4⌊C log A⌋ − 13⌊C log(B+15)⌋ − C Λ| < 17`
  for every real `C` (`B+15`).
- `hLLL_method_fails_gap15` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap15` / `coeffCount3_zero_ten_ten_ten_gap15 = 1331`
  / `no_uniform_c_easy_half_gap15` — `(1/2)·1·1 < 242`.
- `baker_bound_gap15_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; `B` is even and `A` is odd; `3 ∣ B` and
  `5 ∣ B` are impossible; `7 ∣ B` is compatible; remaining
  solutions are coprime and Darmon–Merel `(4,4,13)` would be
  refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap15_of_axiom` / `baker_bound_gap15_true` /
  `baker_bound_gap15_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-15 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as `3 ∣ 0`. Not named `baker_bound_gap15`.

## What stays a def Prop

- `baker_bound_gap15` — named theorem stays uninhabited.
- `hGen_gap15` / `hLLL_gap15` / `baker_bound_gap15_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap15`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Successor infrastructure for generic `k` is
[`BealGapK.md`](BealGapK.md) (`v24-v24x-final-gapK-generic-nogo`).
Gap-15 itself is unchanged.

Not a minted unconditional v25 tag.
