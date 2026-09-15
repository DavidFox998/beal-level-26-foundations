# BealGap14 — gap-14 `A⁴ + B⁴ = (B+14)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap14.lean`](../../BealGap14.lean)
(root module; `Beal/Matveev/BealGap14.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap14`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `97e4841` (`v24-v24x-final-gap13-nogo`).
Gap-14 is `C = B+14`, so `gcd(B,C) ∣ 14`. Parity is gap-2/4/6/8/10/12,
not gap-1/5/7/9/11/13: **`B` is odd** and **`A` is even**. Even `B`
is **not** an infinite `A₁⁴+B₁⁴=512 C₁¹³` forever (the gap-12
lesson): three divisions by `2` leave `A₃⁴+B₃⁴=2(4B₃+7)¹³`, whose
residue is `6` or `14` mod 16, never a sum of fourth powers `{0,1,2}`.
`(1,0)` is **not** a solution (`1 ≠ 14¹³`). Odd `B` forces
`gcd(B,C) ∣ 7`. **`3 ∣ B` kills residue** (`C ≡ 2 mod 3`, `C¹³ ≡ 2`,
not in `{0,1}`; `14 ≢ 0 mod 3`, so this is **not** a 3-descent).
**`5 ∣ B` kills residue** (`C ≡ 4 mod 5`, `C¹³ ≡ 4`, not in `{0,1}`;
`14 ≢ 0 mod 5`, so this is **not** a 5-descent). **`7 ∣ B` kills by
7-descent**: `A=7A₁ B=7B₁ C=7(B₁+2)` gives `A₁⁴+B₁⁴=7⁹ C₁¹³`
(`7⁹ = 40353607`); fourth powers mod 7 are `{0,1,2,4}` and sum `0`
only `0+0`, so three further `/7` leave `343 X = (B₁+2)¹³` while
`B₁+2 ≡ 2 mod 7`. Remaining solutions are coprime
(`p ∣ A,B` ⇒ `p ∣ 14`, but `B` is odd so `p ≠ 2`, and `7 ∤ B`)
and pure Darmon–Merel signature `(4,4,13)`. 0 sorry. No new axiom.

Do **not** prove `B_even_of_sol_gap14` / `A_odd_of_sol_gap14` —
those are the odd-gap parities and are false here.

## What is proved (0 sorry)

- `not_gap14_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 14¹³`.
- `gcd_B_C_eq_gcd_fourteen` / `gcd_B_C_dvd_fourteen` /
  `gcd_B_C_dvd_fourteen_gap14` — `gcd(B,B+14) = gcd(B,14) ∣ 14`.
- `gcd_B_C_dvd_seven_of_odd_gap14` — odd `B` forces `gcd ∣ 7`.
- `A_even_of_sol_gap14` — odd `A` dies mod 16 (even `B` makes
  RHS `0` and LHS `1`; odd `B` makes LHS `2` and would force
  odd `C ≡ 2` mod 16).
- `no_sol_when_even_B` — three `/2` leave `2(4B₃+7)¹³` residue
  `6` or `14`.
- `B_odd_of_sol_gap14` — even `B` is impossible.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap14` — a common prime
  of `A` and `B` would divide `C` hence divide `14`, so `p=2` or
  `p=7`; `B` odd kills `2`, and `7 ∤ B` by the descent below.
- `A_gt_B_of_sol` — `2 B⁴ < (B+14)¹³`, so `A > B` for `B > 0`.
- `no_sol_when_three_dvd_B_gap14` — `C ≡ 2 mod 3`, `C¹³ ≡ 2` not in `{0,1}`.
- `no_sol_when_five_dvd_B_gap14` — `C ≡ 4 mod 5`, `C¹³ ≡ 4` not in `{0,1}`.
- `seven_dvd_B_forces_seven_dvd_A_gap14` — `7 ∣ B` ⇒ `C ≡ 0` ⇒
  `A⁴ ≡ 0` ⇒ `7 ∣ A`.
- `no_sol_when_seven_dvd_B_gap14` — 7-descent last step
  `343 X = (B₁+2)¹³` with `B₁+2 ≡ 2`.
- `hGen_exp_lt_ratio_gap14` / `C1_floor_hGen_loses_gap14` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+14)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap14` — `|4⌊C log A⌋ − 13⌊C log(B+14)⌋ − C Λ| < 17`
  for every real `C` (`B+14`).
- `hLLL_method_fails_gap14` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap14` / `coeffCount3_zero_ten_ten_ten_gap14 = 1331`
  / `no_uniform_c_easy_half_gap14` — `(1/2)·1·1 < 242`.
- `baker_bound_gap14_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; `B` is odd and `A` is even; `3 ∣ B`, `5 ∣ B`,
  and `7 ∣ B` are impossible; remaining solutions are coprime and
  Darmon–Merel `(4,4,13)` would be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap14_of_axiom` / `baker_bound_gap14_true` /
  `baker_bound_gap14_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-14 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as even. Not named `baker_bound_gap14`.

## What stays a def Prop

- `baker_bound_gap14` — named theorem stays uninhabited.
- `hGen_gap14` / `hLLL_gap14` / `baker_bound_gap14_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap14`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag.
