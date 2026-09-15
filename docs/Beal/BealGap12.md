# BealGap12 — gap-12 `A⁴ + B⁴ = (B+12)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap12.lean`](../../BealGap12.lean)
(root module; `Beal/Matveev/BealGap12.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap12`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `5d28874` (`v24-v24x-final-gap11-nogo`).
Gap-12 is `C = B+12`, so `gcd(B,C) ∣ 12`. Parity is gap-2/4/6/8,
not gap-1/5/7/9/11: **`A` is even** (odd `A` makes the left side
`1` or `2` mod 16 while even `C` is `0` and odd `C` is odd, never
`2`). Even `B` dies after six divisions by `2`, leaving
`A₆⁴ + B₆⁴ = 4 (16 B₆ + 3)¹³` with residue **`12`** mod 16
(like gap-4 `5388a60`, not gap-10 leftover `B≡2∨4`). So **`B`
is odd**. `(1,0)` is **not** a solution (`1 ≠ 12¹³`). Like
gap-3 `f1cb039` and gap-6 `8425abd`, **`3 ∣ B` is a 3-descent**:
`A=3A₁ B=3B₁ C=3(B₁+4)` gives `A₁⁴+B₁⁴=3⁹ C₁¹³` (`3⁹ = 19683`),
and after two more steps `27 X = C₁¹³` while `C₁=B₁+4 ≡ 1 mod 3`.
**`5 ∣ B` kills residue** (`C ≡ 2 mod 5`, `C¹³ ≡ 2`, not in
`{0,1}`; same as gap-2 / gap-8 / gap-9). **`7 ∣ B` kills
residue** (`C ≡ 5 mod 7`, `C¹³ ≡ 5`, not in `{0,1,2,4}`; new
versus gap-10 `C≡3`). Remaining solutions are coprime
(`p ∣ A,B` ⇒ `p ∣ 12`, but `B` is odd and `3 ∤ B`) and pure
Darmon–Merel signature `(4,4,13)`. 0 sorry. No new axiom.

Do **not** prove `B_even_of_sol_gap12` / `A_odd_of_sol_gap12` —
those are the gap-1/5/7/9/11 parities and are false here.

## What is proved (0 sorry)

- `not_gap12_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 12¹³`.
- `gcd_B_C_eq_gcd_twelve` / `gcd_B_C_dvd_twelve` /
  `gcd_B_C_dvd_twelve_gap12` — `gcd(B,B+12) = gcd(B,12) ∣ 12`.
- `A_even_of_sol_gap12` / `no_sol_when_even_B` / `B_odd_of_sol_gap12` —
  odd `A` dies mod 16; even `B` dies after six `/2` as
  `4 (16 B₆ + 3)¹³ ≡ 12` mod 16.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap12` — a common prime
  of `A` and `B` would divide `C` hence divide `12`, so `p=2` or `3`,
  but `B` is odd and `3 ∤ B`.
- `A_gt_B_of_sol` — `2 B⁴ < (B+12)¹³`, so `A > B` for `B > 0`.
- `three_dvd_B_forces_three_dvd_A_gap12` /
  `no_sol_when_three_dvd_B_gap12` — `3 ∣ B` ⇒ `3 ∣ A`, then
  3-descent dies as `27 X = (B₁+4)¹³` with `B₁+4 ≡ 1 mod 3`.
  Same idea as `f1cb039` / gap-3 / gap-6, opposite of gap-1 / gap-4.
- `no_sol_when_five_dvd_B_gap12` — `C ≡ 2 mod 5`, `C¹³ ≡ 2` not in `{0,1}`.
- `no_sol_when_seven_dvd_B_gap12` — `C ≡ 5 mod 7`, `C¹³ ≡ 5` not in `{0,1,2,4}`.
- `coprime_of_remaining_gap12` — after `3 ∤ B`, `5 ∤ B`, `7 ∤ B`
  the remaining branch is still coprime (in fact every solution is).
- `hGen_exp_lt_ratio_gap12` / `C1_floor_hGen_loses_gap12` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+12)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap12` — `|4⌊C log A⌋ − 13⌊C log(B+12)⌋ − C Λ| < 17`
  for every real `C` (`B+12`).
- `hLLL_method_fails_gap12` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap12` / `coeffCount3_zero_ten_ten_ten_gap12 = 1331`
  / `no_uniform_c_easy_half_gap12` — `(1/2)·1·1 < 242`; Philippon
  is not in Mathlib 4.12.
- `baker_bound_gap12_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; remaining solutions are coprime with `A > B0`,
  `B` odd, `A` even; `3 ∣ B`, `5 ∣ B`, and `7 ∣ B` are impossible;
  Darmon–Merel `(4,4,13)` would be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap12_of_axiom` / `baker_bound_gap12_true` /
  `baker_bound_gap12_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-12 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as even. Not named `baker_bound_gap12`.

## What stays a def Prop

- `baker_bound_gap12` — named theorem stays uninhabited.
- `hGen_gap12` / `hLLL_gap12` / `baker_bound_gap12_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap12`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag.
