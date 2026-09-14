# BealGap4 — gap-4 `A⁴ + B⁴ = (B+4)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap4.lean`](../../BealGap4.lean)
(root module; `Beal/Matveev/BealGap4.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap4`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `7a1c53b` (`v24-v24x-final-gap2-nogo`).
Gap-4 is `C = B+4`, so `gcd(B,C) ∣ 4`. Like gap-2, **`B` even is
impossible**: six divisions by `2` leave
`A₆⁴ + B₆⁴ = 4 (16 B₆ + 1)¹³`, and `4 · odd ≡ 4` or `12` mod 16,
never a sum of fourth powers `{0,1,2}`. So `B` is odd and `A` is
even. `(1,0)` is **not** a solution (`1 ≠ 4¹³`). Unlike gap-2 /
gap-3, `3 ∣ B` does **not** kill: `C ≡ 1 mod 3`, `A⁴ ≡ 1` is
possible (same as gap-1 `271f03e`). New for gap-4: **`5 ∣ B`
does kill**, `C ≡ 4 mod 5`, `C¹³ ≡ 4`, while `A⁴ ∈ {0,1}`.
Remaining solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 4`, but `B`
is odd) and pure Darmon–Merel signature `(4,4,13)`. 0 sorry.
No new axiom.

Do **not** prove `B_even_of_sol_gap4` / `A_odd_of_sol_gap4` —
those are the gap-1 parities and are false here. Do **not**
prove `no_sol_when_three_dvd_B` for gap-4 (`C ≡ 1 mod 3`).

## What is proved (0 sorry)

- `not_gap4_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 4¹³`.
- `gcd_B_C_eq_gcd_four` / `gcd_B_C_dvd_four` — `gcd(B,B+4) = gcd(B,4) ∣ 4`.
- `A_even_of_sol_gap4` / `no_sol_when_even_B` / `B_odd_of_sol_gap4` —
  if `A` is odd then the sum of fourth powers is `1` or `2` mod 16,
  while even `C` is `0` and odd `C` is odd, never `2`. Even `B`
  then forces a 2-descent that dies as `4 · odd` mod 16.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap4` — a common prime
  of `A` and `B` would divide `C` hence divide `4`, but `B` is odd.
- `A_gt_B_of_sol` — `2 B⁴ < (B+4)¹³`, so `A > B` for `B > 0`.
- `A_pow_four_mod3_eq_one_of_three_dvd_B` /
  `not_three_dvd_A_of_three_dvd_B` — `3 ∣ B` ⇒ `C ≡ 1 mod 3` ⇒
  `A⁴ ≡ 1`, so `3 ∤ A`. Same as gap-1, opposite of gap-2 / gap-3.
- `no_sol_when_five_dvd_B_gap4` — `5 ∣ B` ⇒ `C ≡ 4 mod 5` ⇒
  `C¹³ ≡ 4`, while `A⁴ + B⁴ ≡ 0` or `1`. New for gap-4.
- `coprime_of_remaining_gap4` — after `5 ∤ B` the remaining
  branch is still coprime (in fact every solution is).
- `hGen_exp_lt_ratio_gap4` / `C1_floor_hGen_loses_gap4` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+4)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap4` — `|4⌊C log A⌋ − 13⌊C log(B+4)⌋ − C Λ| < 17`
  for every real `C` (`B+4`, not `B+3` / `B+2` / `B+1`).
- `hLLL_method_fails_gap4` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap4` / `coeffCount3_zero_ten_ten_ten_gap4 = 1331`
  / `no_uniform_c_easy_half_gap4` — `(1/2)·1·1 < 242`; Philippon
  is not in Mathlib 4.12.
- `baker_bound_gap4_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; remaining solutions are coprime with `A > B0`,
  `B` odd, `A` even; `5 ∣ B` is impossible; `3 ∣ B` forces `3 ∤ A`;
  Darmon–Merel `(4,4,13)` would be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap4_of_axiom` / `baker_bound_gap4_true` /
  `baker_bound_gap4_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-4 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  Not named `baker_bound_gap4`.

## What stays a def Prop

- `baker_bound_gap4` — named theorem stays uninhabited.
- `hGen_gap4` / `hLLL_gap4` / `baker_bound_gap4_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap4`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag.
