# BealGap7 — gap-7 `A⁴ + B⁴ = (B+7)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap7.lean`](../../BealGap7.lean)
(root module; `Beal/Matveev/BealGap7.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap7`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `8425abd` (`v24-v24x-final-gap6-nogo`).
Gap-7 is `C = B+7`, so `gcd(B,C) ∣ 7`. Parity is gap-1/5, not
gap-2/4/6: **`B` is even** (odd `B` makes `C` even, so
`C¹³ ≡ 0` mod 16 while `A⁴ + B⁴ ≡ 1` or `2`). **`A` is odd**.
`(1,0)` is **not** a solution (`1 ≠ 7¹³`). Like gap-1 / gap-4,
**`3 ∣ B` does not kill** (`C ≡ 1 mod 3`, `A⁴ ≡ 1` possible).
**`5 ∣ B` kills residue** (`C ≡ 2 mod 5`, `C¹³ ≡ 2`, while
`A⁴ ∈ {0,1}`). **`7 ∣ B` is a 7-descent**:
`A=7A₁ B=7B₁ C=7(B₁+1)` gives `A₁⁴+B₁⁴=7⁹ C₁¹³`,
fourth powers mod 7 are `{0,1,2,4}` and sum `0` only as `0+0`,
and after two more steps `343 X = C₁¹³` while `C₁=B₁+1 ≡ 1`.
Remaining solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 7`, but
`7 ∤ B`) and pure Darmon–Merel signature `(4,4,13)`.
0 sorry. No new axiom.

Do **not** prove `B_odd_of_sol_gap7` / `A_even_of_sol_gap7` —
those are the even-gap parities and are false here. Do **not**
prove `no_sol_when_three_dvd_B` for gap-7 (`C ≡ 1 mod 3`).

## What is proved (0 sorry)

- `not_gap7_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 7¹³`.
- `gcd_B_C_eq_gcd_seven` / `gcd_B_C_dvd_seven` — `gcd(B,B+7) = gcd(B,7) ∣ 7`.
- `B_even_of_sol_gap7` / `A_odd_of_sol_gap7` —
  odd `B` dies as `C` even, `C¹³ ≡ 0` mod 16, LHS `1` or `2`.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap7` — a common prime
  of `A` and `B` would divide `C` hence divide `7`, so `p=7`,
  but `7 ∤ B`.
- `A_gt_B_of_sol` — `2 B⁴ < (B+7)¹³`, so `A > B` for `B > 0`.
- `A_pow_four_mod3_eq_one_of_three_dvd_B` /
  `not_three_dvd_A_of_three_dvd_B` — `3 ∣ B` ⇒ `C ≡ 1` ⇒
  `A⁴ ≡ 1`, so `3 ∤ A`. Same as gap-1 / gap-4.
- `no_sol_when_five_dvd_B_gap7` — `5 ∣ B` ⇒ `C ≡ 2 mod 5` ⇒
  `C¹³ ≡ 2`, while `A⁴ ∈ {0,1}`.
- `seven_dvd_B_forces_seven_dvd_A_gap7` /
  `no_sol_when_seven_dvd_B_gap7` — `7 ∣ B` ⇒ `7 ∣ A`, then
  7-descent dies as `343 X = (B₁+1)¹³` with `B₁+1 ≡ 1 mod 7`.
- `coprime_of_remaining_gap7` — after `5 ∤ B` and `7 ∤ B` the
  remaining branch is still coprime (in fact every solution is).
- `hGen_exp_lt_ratio_gap7` / `C1_floor_hGen_loses_gap7` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+7)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap7` — `|4⌊C log A⌋ − 13⌊C log(B+7)⌋ − C Λ| < 17`
  for every real `C` (`B+7`).
- `hLLL_method_fails_gap7` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap7` / `coeffCount3_zero_ten_ten_ten_gap7 = 1331`
  / `no_uniform_c_easy_half_gap7` — `(1/2)·1·1 < 242`; Philippon
  is not in Mathlib 4.12.
- `baker_bound_gap7_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; remaining solutions are coprime with `A > B0`,
  `B` even, `A` odd; `5 ∣ B` and `7 ∣ B` are impossible;
  `3 ∣ B` forces `3 ∤ A`; Darmon–Merel `(4,4,13)` would be
  refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap7_of_axiom` / `baker_bound_gap7_true` /
  `baker_bound_gap7_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-7 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as `7 ∣ 0`. Not named `baker_bound_gap7`.

## What stays a def Prop

- `baker_bound_gap7` — named theorem stays uninhabited.
- `hGen_gap7` / `hLLL_gap7` / `baker_bound_gap7_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap7`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag. Successor: [`BealGap8.md`](BealGap8.md)
`C = B+8`, `B` odd, even `B` dies after nine `/2` as residue `8`.
