# BealGap13 — gap-13 `A⁴ + B⁴ = (B+13)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap13.lean`](../../BealGap13.lean)
(root module; `Beal/Matveev/BealGap13.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap13`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `eeff2cd` (`v24-v24x-final-gap12-nogo`).
Gap-13 is `C = B+13`, so `gcd(B,C) ∣ 13`. Parity is gap-1/5/7/9/11,
not gap-2/4/6/8/10/12: **`B` is even** (odd `B` makes `C` even, so
`C¹³ ≡ 0` mod 16 while `A⁴ + B⁴ ≡ 1` or `2`). **`A` is odd**.
`(1,0)` is **not** a solution (`1 ≠ 13¹³`). **`3 ∣ B` is compatible**
(`C ≡ 1 mod 3`, `A⁴ ≡ 1`; `3 ∤ 13` so the coprime branch still
holds). **`5 ∣ B` kills residue** (`C ≡ 3 mod 5`, `C¹³ ≡ 3`, not
in `{0,1}`). **`7 ∣ B` kills residue** (`C ≡ 6 mod 7`, `C¹³ ≡ 6`,
not in `{0,1,2,4}`). **`11 ∣ B` kills residue** (`C ≡ 2 mod 11`,
`C¹³ ≡ 8` via `a¹³ ≡ a³` mod 11, not in `{0,1,3,4,5,9}`; this is
**not** the gap-11 11-descent). **`13 ∣ B` kills by 13-descent**:
`A=13A₁ B=13B₁ C=13(B₁+1)` gives `A₁⁴+B₁⁴=13⁹ C₁¹³`
(`13⁹ = 10604499373`); fourth powers mod 13 are `{0,1,3,9}` and
sum `0` only `0+0`, so three further `/13` leave
`2197 X = (B₁+1)¹³` while `B₁+1 ≡ 1 mod 13`. Remaining solutions
are coprime (`p ∣ A,B` ⇒ `p ∣ 13`, but `13 ∤ B`) and pure
Darmon–Merel signature `(4,4,13)`. 0 sorry. No new axiom.

Do **not** prove `B_odd_of_sol_gap13` / `A_even_of_sol_gap13` —
those are the even-gap parities and are false here. Do **not**
prove `no_sol_when_three_dvd_B` for gap-13 (`C ≡ 1 mod 3`).

## What is proved (0 sorry)

- `not_gap13_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 13¹³`.
- `gcd_B_C_eq_gcd_thirteen` / `gcd_B_C_dvd_thirteen` /
  `gcd_B_C_dvd_thirteen_gap13` — `gcd(B,B+13) = gcd(B,13) ∣ 13`.
- `B_even_of_sol_gap13` — odd `B` dies as `C` even, `C¹³ ≡ 0` mod 16,
  while LHS is `1` or `2`.
- `A_odd_of_sol_gap13` — even `A` would make LHS even, but `C` is odd.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap13` — a common prime
  of `A` and `B` would divide `C` hence divide `13`, so `p=13`,
  but `13 ∤ B` by the descent below.
- `A_gt_B_of_sol` — `2 B⁴ < (B+13)¹³`, so `A > B` for `B > 0`.
- `three_dvd_B_compat_gap13` /
  `A_pow_four_mod3_eq_one_of_three_dvd_B` — `3 ∣ B` compatible,
  `A⁴ ≡ 1`. Do **not** prove a three-kill here.
- `no_sol_when_five_dvd_B_gap13` — `C ≡ 3 mod 5`, `C¹³ ≡ 3` not in `{0,1}`.
- `no_sol_when_seven_dvd_B_gap13` — `C ≡ 6 mod 7`, `C¹³ ≡ 6` not in `{0,1,2,4}`.
- `no_sol_when_eleven_dvd_B_gap13` — `C ≡ 2 mod 11`, `C¹³ ≡ 8` not in
  `{0,1,3,4,5,9}`.
- `thirteen_dvd_B_forces_thirteen_dvd_A_gap13` — `13 ∣ B` ⇒ `C ≡ 0` ⇒
  `A⁴ ≡ 0` ⇒ `13 ∣ A`.
- `no_sol_when_thirteen_dvd_B_gap13` — 13-descent last step
  `2197 X = (B₁+1)¹³` with `B₁+1 ≡ 1`.
- `hGen_exp_lt_ratio_gap13` / `C1_floor_hGen_loses_gap13` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+13)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap13` — `|4⌊C log A⌋ − 13⌊C log(B+13)⌋ − C Λ| < 17`
  for every real `C` (`B+13`).
- `hLLL_method_fails_gap13` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap13` / `coeffCount3_zero_ten_ten_ten_gap13 = 1331`
  / `no_uniform_c_easy_half_gap13` — `(1/2)·1·1 < 242`.
- `baker_bound_gap13_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; `B` is even and `A` is odd; `5 ∣ B`, `7 ∣ B`,
  `11 ∣ B`, and `13 ∣ B` are impossible; `3 ∣ B` is compatible;
  remaining solutions are coprime and Darmon–Merel `(4,4,13)` would
  be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap13_of_axiom` / `baker_bound_gap13_true` /
  `baker_bound_gap13_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-13 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as `13 ∣ 0`. Not named `baker_bound_gap13`.

## What stays a def Prop

- `baker_bound_gap13` — named theorem stays uninhabited.
- `hGen_gap13` / `hLLL_gap13` / `baker_bound_gap13_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap13`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag. Successor: [`BealGap14.md`](BealGap14.md)
(`v24-v24x-final-gap14-nogo`).
