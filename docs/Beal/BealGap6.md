# BealGap6 — gap-6 `A⁴ + B⁴ = (B+6)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap6.lean`](../../BealGap6.lean)
(root module; `Beal/Matveev/BealGap6.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap6`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `59d8a4a` (`v24-v24x-final-gap5-nogo`).
Gap-6 is `C = B+6`, so `gcd(B,C) ∣ 6`. Parity is gap-2/4, not
gap-1/5: **`A` is even** (odd `A` makes the left side `1` or `2`
mod 16 while even `C` is `0` and odd `C` is odd, never `2`).
Even `B` dies after three divisions by `2`, leaving
`A₃⁴ + B₃⁴ = 2 (4 B₃ + 3)¹³` with residue **`6` or `14`** mod 16
(not gap-2’s `2` or `10`). So **`B` is odd**. `(1,0)` is **not**
a solution (`1 ≠ 6¹³`). Like gap-3 `f1cb039`, **`3 ∣ B` is a
3-descent**: `A=3A₁ B=3B₁ C=3(B₁+2)` gives `A₁⁴+B₁⁴=3⁹ C₁¹³`,
and after two more steps `27 X = C₁¹³` while `C₁=B₁+2 ≡ 2 mod 3`.
**`5 ∣ B` does not kill** (`C ≡ 1 mod 5`, `A⁴ ≡ 1` possible).
Remaining solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 6`, but `B`
is odd and `3 ∤ B`) and pure Darmon–Merel signature `(4,4,13)`.
0 sorry. No new axiom.

Do **not** prove `B_even_of_sol_gap6` / `A_odd_of_sol_gap6` —
those are the gap-1/5 parities and are false here. Do **not**
prove `no_sol_when_five_dvd_B` for gap-6 (`C ≡ 1 mod 5`).

## What is proved (0 sorry)

- `not_gap6_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 6¹³`.
- `gcd_B_C_eq_gcd_six` / `gcd_B_C_dvd_six` — `gcd(B,B+6) = gcd(B,6) ∣ 6`.
- `A_even_of_sol_gap6` / `no_sol_when_even_B` / `B_odd_of_sol_gap6` —
  odd `A` dies mod 16; even `B` dies as `2·odd ≡ 6` or `14` mod 16.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap6` — a common prime
  of `A` and `B` would divide `C` hence divide `6`, so `p=2` or `3`,
  but `B` is odd and `3 ∤ B`.
- `A_gt_B_of_sol` — `2 B⁴ < (B+6)¹³`, so `A > B` for `B > 0`.
- `three_dvd_B_forces_three_dvd_A_gap6` /
  `no_sol_when_three_dvd_B_gap6` — `3 ∣ B` ⇒ `3 ∣ A`, then
  3-descent dies as `27 X = (B₁+2)¹³` with `B₁+2 ≡ 2 mod 3`.
  Same idea as `f1cb039` / gap-3, opposite of gap-1 / gap-4.
- `A_pow_four_mod5_eq_one_of_five_dvd_B` /
  `not_five_dvd_A_of_five_dvd_B` — `5 ∣ B` ⇒ `C ≡ 1 mod 5` ⇒
  `A⁴ ≡ 1`, so `5 ∤ A`. Do **not** prove a five-kill here.
- `coprime_of_remaining_gap6` — after `3 ∤ B` the remaining
  branch is still coprime (in fact every solution is).
- `hGen_exp_lt_ratio_gap6` / `C1_floor_hGen_loses_gap6` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+6)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap6` — `|4⌊C log A⌋ − 13⌊C log(B+6)⌋ − C Λ| < 17`
  for every real `C` (`B+6`).
- `hLLL_method_fails_gap6` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap6` / `coeffCount3_zero_ten_ten_ten_gap6 = 1331`
  / `no_uniform_c_easy_half_gap6` — `(1/2)·1·1 < 242`; Philippon
  is not in Mathlib 4.12.
- `baker_bound_gap6_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; remaining solutions are coprime with `A > B0`,
  `B` odd, `A` even; `3 ∣ B` is impossible; Darmon–Merel `(4,4,13)`
  would be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap6_of_axiom` / `baker_bound_gap6_true` /
  `baker_bound_gap6_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-6 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as even. Not named `baker_bound_gap6`.

## What stays a def Prop

- `baker_bound_gap6` — named theorem stays uninhabited.
- `hGen_gap6` / `hLLL_gap6` / `baker_bound_gap6_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap6`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag. Next: gap-7 `C = B+7` would flip parity again (`k` odd ⇒ `B` even) and `7∣B` is a new prime.
