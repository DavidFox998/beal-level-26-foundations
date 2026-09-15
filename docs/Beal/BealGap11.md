# BealGap11 — gap-11 `A⁴ + B⁴ = (B+11)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap11.lean`](../../BealGap11.lean)
(root module; `Beal/Matveev/BealGap11.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap11`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `d72316b` (`v24-v24x-final-gap10-nogo`).
Gap-11 is `C = B+11`, so `gcd(B,C) ∣ 11`. Parity is gap-1/5/7/9,
not gap-2/4/6/8/10: **`B` is even** (odd `B` makes `C` even, so
`C¹³ ≡ 0` mod 16 while `A⁴ + B⁴ ≡ 1` or `2`). **`A` is odd**.
`(1,0)` is **not** a solution (`1 ≠ 11¹³`). Unlike gap-9,
**`3 ∣ B` is a residue kill**, not a 3-descent: `11 ≡ 2 mod 3`
so `C ≡ 2`, `C¹³ ≡ 2`, while `A⁴ ∈ {0,1}` (same as gap-2
`7a1c53b` / gap-5 `59d8a4a` / gap-8 `bf43afc`). **`11 ∣ B`
kills by 11-descent**: `A=11A₁ B=11B₁ C=11(B₁+1)` gives
`A₁⁴+B₁⁴=11⁹ C₁¹³` (`11⁹ = 2357947691`); fourth powers mod 11
are `{0,1,3,4,5,9}` and sum `0` only `0+0`, so three further
`/11` leave `1331 X = (B₁+1)¹³` while `B₁+1 ≡ 1 mod 11`.
**`5 ∣ B` is compatible** (`C ≡ 1 mod 5`, `A⁴ ≡ 1`).
**`7 ∣ B` is compatible** (`C ≡ 4 mod 7`, `A⁴ ≡ 4`; `3⁴ = 81 ≡ 4`).
Remaining solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 11`, but
`11 ∤ B`) and pure Darmon–Merel signature `(4,4,13)`. 0 sorry.
No new axiom.

Do **not** prove `B_odd_of_sol_gap11` / `A_even_of_sol_gap11` —
those are the even-gap parities and are false here. Do **not**
prove `no_sol_when_five_dvd_B` / `no_sol_when_seven_dvd_B` for
gap-11 (`C ≡ 1 mod 5` and `C ≡ 4 mod 7`).

## What is proved (0 sorry)

- `not_gap11_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 11¹³`.
- `gcd_B_C_eq_gcd_eleven` / `gcd_B_C_dvd_eleven` — `gcd(B,B+11) = gcd(B,11) ∣ 11`.
- `B_even_of_sol_gap11` — odd `B` dies as `C` even, `C¹³ ≡ 0` mod 16,
  while LHS is `1` or `2`.
- `A_odd_of_sol_gap11` — even `A` would make LHS even, but `C` is odd.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap11` — a common prime
  of `A` and `B` would divide `C` hence divide `11`, so `p=11`,
  but `11 ∤ B` by the descent below.
- `A_gt_B_of_sol` — `2 B⁴ < (B+11)¹³`, so `A > B` for `B > 0`.
- `no_sol_when_three_dvd_B_gap11` — `C ≡ 2 mod 3`, `C¹³ ≡ 2` not in `{0,1}`.
- `eleven_dvd_B_forces_eleven_dvd_A_gap11` — `11 ∣ B` ⇒ `C ≡ 0` ⇒
  `A⁴ ≡ 0` ⇒ `11 ∣ A`.
- `no_sol_when_eleven_dvd_B_gap11` — 11-descent last step
  `1331 X = (B₁+1)¹³` with `B₁+1 ≡ 1`.
- `A_pow_four_mod5_eq_one_of_five_dvd_B` — `5 ∣ B` compatible, `A⁴ ≡ 1`.
- `A_pow_four_mod7_eq_four_of_seven_dvd_B` — `7 ∣ B` compatible, `A⁴ ≡ 4`.
- `hGen_exp_lt_ratio_gap11` / `C1_floor_hGen_loses_gap11` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+11)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap11` — `|4⌊C log A⌋ − 13⌊C log(B+11)⌋ − C Λ| < 17`
  for every real `C` (`B+11`).
- `hLLL_method_fails_gap11` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap11` / `coeffCount3_zero_ten_ten_ten_gap11 = 1331`
  / `no_uniform_c_easy_half_gap11` — `(1/2)·1·1 < 242`.
- `baker_bound_gap11_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; `B` is even and `A` is odd; `3 ∣ B` and `11 ∣ B`
  are impossible; `5 ∣ B` / `7 ∣ B` are compatible; remaining
  solutions are coprime and Darmon–Merel `(4,4,13)` would be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap11_of_axiom` / `baker_bound_gap11_true` /
  `baker_bound_gap11_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-11 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as `3 ∣ 0`. Not named `baker_bound_gap11`.

## What stays a def Prop

- `baker_bound_gap11` — named theorem stays uninhabited.
- `hGen_gap11` / `hLLL_gap11` / `baker_bound_gap11_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap11`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag. Successor: [`BealGap12.md`](BealGap12.md)
(`v24-v24x-final-gap12-nogo`).
