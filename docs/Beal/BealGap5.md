# BealGap5 — gap-5 `A⁴ + B⁴ = (B+5)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap5.lean`](../../BealGap5.lean)
(root module; `Beal/Matveev/BealGap5.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap5`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `5388a60` (`v24-v24x-final-gap4-nogo`).
Gap-5 is `C = B+5`, so `gcd(B,C) ∣ 5`. Parity is gap-1, not
gap-2/4: odd `B` makes `C` even, so `C¹³ ≡ 0` mod 16 while
`A⁴ + B⁴ ≡ 1` or `2`. Thus **`B` is even and `A` is odd**.
`(1,0)` is **not** a solution (`1 ≠ 5¹³`). Like gap-2 / gap-3,
**`3 ∣ B` is a contradiction**: `C ≡ 2 mod 3`, `C¹³ ≡ 2`, while
`A⁴ ∈ {0,1}`. **`5 ∣ B` also kills**, but not by residue 4
(that was gap-4): `C ≡ 0`, so `A⁴ ≡ 0`, hence `5 ∣ A`, and a
5-descent dies after three extra divisions as
`125 (A₄⁴ + B₄⁴) = (125 B₄ + 1)¹³` with the right side `≡ 1`
mod 5. Remaining solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 5`,
but `5 ∤ B`) and pure Darmon–Merel signature `(4,4,13)`.
0 sorry. No new axiom.

Do **not** prove `B_odd_of_sol_gap5` / `A_even_of_sol_gap5` —
those are the gap-2/4 parities and are false here. Do **not**
prove `no_sol_when_even_B` for gap-5. Do **not** leave `5 ∣ B`
as “gcd ≥ 5 so Darmon–Merel does not apply”: after the descent
there are **no** solutions with `5 ∣ B`.

## What is proved (0 sorry)

- `not_gap5_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 5¹³`.
- `gcd_B_C_eq_gcd_five` / `gcd_B_C_dvd_five` — `gcd(B,B+5) = gcd(B,5) ∣ 5`.
- `B_even_of_sol_gap5` / `A_odd_of_sol_gap5` — odd `B` makes `C`
  even, so `16 ∣ C¹³`, while the sum of fourth powers is `1` or
  `2` mod 16. Even `B` and even `A` would make the left side even
  and the right side odd.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap5` — a common prime
  of `A` and `B` would divide `C` hence divide `5`, but `5 ∤ B`.
- `A_gt_B_of_sol` — `2 B⁴ < (B+5)¹³`, so `A > B` for `B > 0`.
- `no_sol_when_three_dvd_B_gap5` — `3 ∣ B` ⇒ `C ≡ 2 mod 3` ⇒
  `C¹³ ≡ 2`, while `A⁴ ∈ {0,1}`. Same as gap-2 / `f1cb039`,
  opposite of gap-1 / gap-4.
- `five_dvd_B_forces_five_dvd_A_gap5` / `no_sol_when_five_dvd_B_gap5`
  — `5 ∣ B` ⇒ `C ≡ 0` ⇒ `A⁴ ≡ 0` ⇒ `5 ∣ A`, then three extra
  divisions by `5` leave a right side `≡ 1` mod 5.
- `coprime_of_remaining_gap5` — after `3 ∤ B` and `5 ∤ B` the
  remaining branch is still coprime (in fact every solution is).
- `hGen_exp_lt_ratio_gap5` / `C1_floor_hGen_loses_gap5` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+5)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap5` — `|4⌊C log A⌋ − 13⌊C log(B+5)⌋ − C Λ| < 17`
  for every real `C` (`B+5`, not `B+4` / `B+3` / `B+2` / `B+1`).
- `hLLL_method_fails_gap5` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap5` / `coeffCount3_zero_ten_ten_ten_gap5 = 1331`
  / `no_uniform_c_easy_half_gap5` — `(1/2)·1·1 < 242`; Philippon
  is not in Mathlib 4.12.
- `baker_bound_gap5_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; remaining solutions are coprime with `A > B0`,
  `B` even, `A` odd; `3 ∣ B` and `5 ∣ B` are impossible;
  Darmon–Merel `(4,4,13)` would be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap5_of_axiom` / `baker_bound_gap5_true` /
  `baker_bound_gap5_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-5 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  `B = 0` dies as `5 ∣ 0`. Not named `baker_bound_gap5`.

## What stays a def Prop

- `baker_bound_gap5` — named theorem stays uninhabited.
- `hGen_gap5` / `hLLL_gap5` / `baker_bound_gap5_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap5`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag.
