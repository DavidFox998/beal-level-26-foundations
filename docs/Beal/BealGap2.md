# BealGap2 — gap-2 `A⁴ + B⁴ = (B+2)¹³` no-go (not a `B ≤ 10⁶` close)

Lean: [`BealGap2.lean`](../../BealGap2.lean)
(root module; `Beal/Matveev/BealGap2.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGap2`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `271f03e` (`v24-v24x-final-gap1-nogo`).
Gap-2 is `C = B+2`, so `gcd(B,C) ∣ 2`. Unlike gap-1, **`B` even is
impossible**: three divisions by `2` leave
`A₃⁴ + B₃⁴ = 2 (4 B₃ + 1)¹³`, whose residue is `2` or `10` mod 16
and cannot match a sum of fourth powers together with the parity
of `B₃`. So `B` is odd and `A` is even. `(1,0)` is **not** a
solution (`1 ≠ 2¹³`). Like gap-3 (`f1cb039`), `3 ∣ B` is a
contradiction: `C ≡ 2 mod 3`, `C¹³ ≡ 2`, while `A⁴ + B⁴ ≡ A⁴ ∈ {0,1}`.
Remaining solutions are coprime (`p ∣ A,B` ⇒ `p ∣ 2`, but `B` is
odd) and pure Darmon–Merel signature `(4,4,13)`. 0 sorry. No new axiom.

Do **not** prove `B_even_of_sol_gap2` / `A_odd_of_sol_gap2` — those
are the gap-1 parities and are false here.

## What is proved (0 sorry)

- `not_gap2_one_zero` — `(1,0)` does **not** solve `1⁴ + 0⁴ = 2¹³`.
- `gcd_B_C_eq_gcd_two` / `gcd_B_C_dvd_two` — `gcd(B,B+2) = gcd(B,2) ∣ 2`.
- `A_even_of_sol_gap2` / `no_sol_when_even_B` / `B_odd_of_sol_gap2` —
  if `A` is odd then the sum of fourth powers is `1` or `2` mod 16,
  while even `C` is `0` and odd `C` is odd, never `2`. Even `B`
  then forces a 2-descent that dies mod 16.
- `gcd_A_B_eq_one_of_sol` / `coprime_of_sol_gap2` — a common prime
  of `A` and `B` would divide `C` hence divide `2`, but `B` is odd.
- `A_gt_B_of_sol` — `2 B⁴ < (B+2)¹³`, so `A > B` for `B > 0`.
- `no_sol_when_three_dvd_B_gap2` — `3 ∣ B` ⇒ `C ≡ 2 mod 3` ⇒
  `C¹³ ≡ 2`, while `A⁴ + B⁴ ≡ 0` or `1`. Same idea as `f1cb039`.
- `coprime_of_remaining_gap2` — after `3 ∤ B` the remaining
  branch is still coprime (in fact every solution is).
- `hGen_exp_lt_ratio_gap2` / `C1_floor_hGen_loses_gap2` — every
  `C1 ≥ 1`, including `C1_floor`, has
  `exp(−C1 log A log(B+2)) < B⁴/A⁴` on a solution with `B ≥ B0`.
- `floor_form_approx_of_C_gap2` — `|4⌊C log A⌋ − 13⌊C log(B+2)⌋ − C Λ| < 17`
  for every real `C` (`B+2`, not `B+3` / `B+1`).
- `hLLL_method_fails_gap2` — no scaling `C > 0` yields a
  Baker–Davenport witness `r > 17 + C/B0`.
- `no_uniform_c_cubic_in_N_gap2` / `coeffCount3_zero_ten_ten_ten_gap2 = 1331`
  / `no_uniform_c_easy_half_gap2` — `(1/2)·1·1 < 242`; Philippon
  is not in Mathlib 4.12.
- `baker_bound_gap2_unconditional_nogo` — on `B ≥ B0` the log and
  LLL methods lose; remaining solutions are coprime with `A > B0`,
  `B` odd, `A` even; `3 ∣ B` is impossible; Darmon–Merel `(4,4,13)`
  would be refuted.
  `#print axioms` is `[propext, Classical.choice, Quot.sound]` only.
- `no_gap2_of_axiom` / `baker_bound_gap2_true` /
  `baker_bound_gap2_true_of_axiom` — axiom-relative vacuous close
  for **every** gap-2 pair, reusing
  `BealTrueV25.darmon_merel_4413_axiom` (no second axiom).
  Not named `baker_bound_gap2`.

## What stays a def Prop

- `baker_bound_gap2` — named theorem stays uninhabited.
- `hGen_gap2` / `hLLL_gap2` / `baker_bound_gap2_of_hGen_hLLL`.
- `darmon_merel_44_13_no_coprime` (alias of the TrueV25 Prop).

This module does **not** contain `axiom darmon_merel_4413_axiom_gap2`.
The axiom-relative inhabitant reuses [`BealTrueV25.md`](BealTrueV25.md).

Not a minted unconditional v25 tag.
