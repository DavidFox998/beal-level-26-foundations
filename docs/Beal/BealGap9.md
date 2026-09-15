# BealGap9 — gap-9 `A⁴ + B⁴ = (B+9)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap9.lean`](../../BealGap9.lean)
(root module; `Beal/Matveev/BealGap9.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap9`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `bf43afc` (`v24-v24x-final-gap8-nogo`).
Gap-9 is `C = B+9`, so `gcd(B,C) ∣ 9`. Parity is gap-1/5/7, not
gap-2/4/6/8: **`B` is even** (odd `B` makes `C` even, so
`C¹³ ≡ 0` mod 16 while `A⁴ + B⁴ ≡ 1` or `2`). **`A` is odd**.
`(1,0)` is **not** a solution (`1 ≠ 9¹³`). Like gap-3
`f1cb039` and gap-6 `8425abd`, **`3 ∣ B` is a 3-descent**:
`A=3A₁ B=3B₁ C=3(B₁+3)` gives `A₁⁴+B₁⁴=3⁹ C₁¹³`, then
`C₁=B₁+3` picks up another `3`, and after further divisions
`9 X = (3 B₃+1)¹³` while `3 B₃+1 ≡ 1 mod 3`. **`5 ∣ B` kills
residue** (`C ≡ 4 mod 5`, `C¹³ ≡ 4`, not in `{0,1}`; same as
gap-4 `5388a60`). **`7 ∣ B` is compatible** (`C ≡ 2 mod 7`,
`A⁴ ≡ 2` is in `{0,1,2,4}`). Remaining solutions are coprime
(`p ∣ A,B` ⇒ `p ∣ 9`, but `3 ∤ B`) and pure Darmon–Merel
signature `(4,4,13)`. 0 sorry. No new axiom.

Do **not** prove `B_odd_of_sol_gap9` / `A_even_of_sol_gap9` —
those are the even-gap parities and are false here. Do **not**
prove `no_sol_when_seven_dvd_B` for gap-9 (`C ≡ 2 mod 7`).

## What is proved (0 sorry)

- `not_gap9_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 9¹³`.
- `gcd_B_C_eq_gcd_nine` / `gcd_B_C_dvd_nine` — `gcd(B,B+9) = gcd(B,9) ∣ 9`.
- `B_even_of_sol_gap9` — odd `B` dies as `C` even, `C¹³ ≡ 0` mod 16,
  while LHS is `1` or `2`.
- `A_odd_of_sol_gap9` — even `A` would make LHS even, but `C` is odd.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap9` — a common prime
  of `A` and `B` would divide `C` hence divide `9`, so `p=3`,
  but `3 ∤ B` by the descent below.
- `A_gt_B_of_sol` — `2 B⁴ < (B+9)¹³`, so `A > B` for `B > 0`.
- `three_dvd_B_forces_three_dvd_A_gap9` — `3 ∣ B` ⇒ `C ≡ 0` ⇒
  `A⁴ ≡ 0` ⇒ `3 ∣ A`.
- `no_sol_when_three_dvd_B_gap9` — 3-descent: after
  `A₁⁴+B₁⁴=3⁹ C₁¹³` with `C₁=B₁+3`, a further `3` on `C₁`
  and four more divisions leave `9 X = (3 B₃+1)¹³` with
  `3 B₃+1 ≡ 1`. Same idea as `f1cb039` / gap-6, longer
  because `C₁ ≡ 0`.
- `no_sol_when_five_dvd_B_gap9` — `5 ∣ B` ⇒ `C ≡ 4 mod 5` ⇒
  `C¹³ ≡ 4`, while `A⁴ ∈ {0,1}`. Same as gap-4.
- `A_pow_four_mod7_eq_two_of_seven_dvd_B` /
  `not_seven_dvd_A_of_seven_dvd_B` — `7 ∣ B` ⇒ `C ≡ 2` ⇒
  `A⁴ ≡ 2`, so `7 ∤ A`.
- `coprime_of_remaining_gap9` — after `3 ∤ B` and `5 ∤ B` the
  remaining branch is still coprime (in fact every solution is).
- `hGen_exp_lt_ratio_gap9` / `C1_floor_hGen_loses_gap9` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+9)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap9` — `|4⌊C log A⌋ − 13⌊C log(B+9)⌋ − C Λ| < 17`
  for every real `C` (`B+9`).
- `hLLL_method_fails_gap9` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap9` / `coeffCount3_zero_ten_ten_ten_gap9 = 1331`
  / `no_uniform_c_easy_half_gap9` — `(1/2)·1·1 < 242`; Philippon
  is not in Mathlib 4.12.
- `baker_bound_gap9_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; remaining solutions are coprime with `A > B0`,
  `B` even, `A` odd; `3 ∣ B` and `5 ∣ B` are impossible;
  `7 ∣ B` forces `A⁴ ≡ 2`; Darmon–Merel `(4,4,13)` would be
  refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap9_of_axiom` / `baker_bound_gap9_true` /
  `baker_bound_gap9_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-9 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as `3 ∣ 0`. Not named `baker_bound_gap9`.

## What stays a def Prop

- `baker_bound_gap9` — named theorem stays uninhabited.
- `hGen_gap9` / `hLLL_gap9` / `baker_bound_gap9_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap9`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag. Successor: [`BealGap10.md`](BealGap10.md)
(`v24-v24x-final-gap10-nogo`).
