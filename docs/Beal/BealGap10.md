# BealGap10 — gap-10 `A⁴ + B⁴ = (B+10)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap10.lean`](../../BealGap10.lean)
(root module; `Beal/Matveev/BealGap10.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap10`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `8b5543e` (`v24-v24x-final-gap9-nogo`).
Gap-10 is `C = B+10`, so `gcd(B,C) ∣ 10`. Parity is gap-2/4/6/8,
not gap-1/5/7/9: **`A` is even**. Odd `A` makes the left side
`1` or `2` mod 16 while even `C` is `0` and odd `C` is odd,
never `2`. **Even `B` is not fully dead.** Three `/2` leave
last-step `A₃⁴ + B₃⁴ = 2 (4 B₃ + 5)¹³`. Even `B₃` dies as
residue `10` mod 16; last-step `5 ∣ B₃` dies by 5-descent
(`125 X = 2 (500 B₄ + 1)¹³ ≡ 2`); last-step `B ≡ 1,3 mod 5`
die (`RHS ≡ 3,4`, `LHS ∈ {1,2}`). Remaining last-step is
both-odd 5-free `B₃ ≡ 2 ∨ 4`. Do **not** prove
`B_odd_of_sol_gap10` / `no_sol_when_even_B`.

Original Gaussian `Re(⟨d,e⟩¹³) = ±(d²+e²−10)²` has leftover
bands (`e ≥ 5d`, `d ≥ 10e`, two-four, three-seven, …) as
polynomial identities. Middle cone `d ≤ 100` is enumerated
(`native_decide`); composites with primitive `u ≤ 100` scale
(`k⁹ ≥ 512`). Uniform `|Q| ≥ 0.01` on `[0.1,5]` is **false**
near the six `tan((2j+1)π/26)` rays and is not used.
`re13_gt_of_middle_cone` takes an extra `hfin` hypothesis;
tan-ray primitives `d ≥ 101` remain.

`(1,0)` is **not** a solution (`1 ≠ 10¹³`). **`3 ∣ B` is
compatible** (`C ≡ 1 mod 3`, `A⁴ ≡ 1`). Do **not** prove
`no_sol_when_three_dvd_B`. **`5 ∣ B` kills by original
5-descent** (`C₁ = B₁+2`, last step `125 X = (125 B₄ + 2)¹³ ≡ 2`
mod 5). **`7 ∣ B` kills residue** (`C ≡ 3 mod 7`, `C¹³ ≡ 3`
not in `{0,1,2,4}`). Odd-`B` remaining solutions are coprime
(`p ∣ A,B` ⇒ `p ∣ 10`, but `B` is odd and `5 ∤ B`) and pure
Darmon–Merel signature `(4,4,13)`. 0 sorry. No new axiom.

## What is proved (0 sorry)

- `not_gap10_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 10¹³`.
- `gcd_B_C_eq_gcd_ten` / `gcd_B_C_dvd_ten` — `gcd(B,B+10) = gcd(B,10) ∣ 10`.
- `A_even_of_sol_gap10` — odd `A` dies mod 16.
- `re13` / `rhs10` / `re13_ne_zero_of_int_ne_zero` — `P(u,v)` has
  no nonzero integer zeros (rational-root / gcd).
- `re13_gt_of_five_mul` / `re13_gt_of_ten_mul` and leftover-band
  identities; `re13_gt_of_middle_cone` with `hfin`.
- `no_sol_when_five_dvd_last` — last-step 5-descent.
- `no_sol_last_when_even_B3` / `no_sol_last_when_B_mod5_eq_one` /
  `no_sol_last_when_B_mod5_eq_three`.
- `even_B_three_div2_last` / `even_B_last_step_remaining` —
  even original `B` reduces to last-step both-odd 5-free `B₃ ≡ 2 ∨ 4`.
- `five_dvd_B_forces_five_dvd_A_gap10` / `no_sol_when_five_dvd_B_gap10`
  — original 5-descent, `C₁ = B₁+2`.
- `A_pow_four_mod3_eq_one_of_three_dvd_B` — `3 ∣ B` compatible.
- `no_sol_when_seven_dvd_B_gap10` — `C ≡ 3 mod 7`.
- `gcd_A_B_eq_one_of_odd_B` / `coprime_of_sol_gap10` — on odd `B`.
- `A_gt_B_of_sol` — `2 B⁴ < (B+10)¹³`, so `A > B` for `B > 0`.
- `hGen_exp_lt_ratio_gap10` / `C1_floor_hGen_loses_gap10` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+10)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap10` — `|4⌊C log A⌋ − 13⌊C log(B+10)⌋ − C Λ| < 17`
  for every real `C` (`B+10`).
- `hLLL_method_fails_gap10` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap10` / `coeffCount3_zero_ten_ten_ten_gap10 = 1331`
  / `no_uniform_c_easy_half_gap10` — `(1/2)·1·1 < 242`.
- `baker_bound_gap10_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; `A` is even; `5 ∣ B` and `7 ∣ B` are impossible;
  odd `B` is coprime and Darmon–Merel `(4,4,13)` would be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap10_of_odd_B_of_axiom` / `no_gap10_of_axiom` /
  `baker_bound_gap10_true` — axiom-relative vacuous close for
  **odd-`B`** gap-10 pairs, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  Even `B` is not claimed. Not named `baker_bound_gap10`.

## What stays a def Prop

- `baker_bound_gap10` — named theorem stays uninhabited.
- `hGen_gap10` / `hLLL_gap10` / `baker_bound_gap10_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).
- Last-step both-odd 5-free `B ≡ 2 ∨ 4` (not a `def Prop`; simply
  not killed).

Not a minted unconditional v25 tag.
