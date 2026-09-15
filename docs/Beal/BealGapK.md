# BealGapK — generic `A⁴ + B⁴ = (B+k)¹³` infrastructure (not a `∀k` close)

Lean: [`BealGapK.lean`](../../BealGapK.lean)
(root module; `Beal/Matveev/BealGapK.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.BealGapK`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `0af0b77` (`v24-v24x-final-gap15-nogo`).
Generic infrastructure for `C = B+k`. This does **not** inhabit
`∀ k A B, ¬ is_gapK_sol`: gap-1 has `(1,0)`, and every fourth-power
gap `k = m⁴` gives `A = m¹³`, `B = 0`. Even `k` does **not** force
`B` odd (gap-10 leftover even `B`). Even `B` does **not** always die
as three `/2` residue `6` or `14`. `p ∣ k` last-step `p³ X = C₁¹³`
contradicts only when `v_p(k) = 1`. Residue kills need the displayed
congruence. Existing axiom closes are recovered for
`k ∈ {2,3,4,5,6,7,8,9,11,12,13,14,15}` and odd-`B` gap-10.
`BealGap1`–`BealGap15` stay in the tree. 0 sorry. No new axiom.

Do **not** prove `B_odd_of_sol_gapK` / `no_gapK_of_axiom` as
`∀k ¬sol`. Do **not** inhabit `hGen_gapK` / `hLLL_gapK` /
`baker_bound_gapK`.

## What is proved (0 sorry)

- `gap1_one_zero` — `(1,0)` solves `k = 1`.
- `fourth_power_gap_at_zero` — `k = m⁴`, `A = m¹³`, `B = 0`.
- `gcd_B_C_eq_gcd_k` / `gcd_B_C_dvd_k` — `gcd(B,B+k) = gcd(B,k) ∣ k`.
- `B_even_of_sol_of_odd_k` / `A_odd_of_sol_of_odd_k` — odd `k`
  dies mod 16 on odd `B` (LHS `1` or `2`, RHS `0`).
- `A_even_of_sol_of_even_k` — even `k` forces `A` even by
  2-parity (not a uniform three-`/2` residue argument).
- `p_dvd_k_forces_p_dvd_A_gapK` — any prime `p ∣ k` and `p ∣ B`
  forces `p ∣ A` via `Prime.dvd_of_dvd_pow` on `A⁴`.
- `no_sol_when_p_dvd_k_{three,five,seven,eleven,thirteen}_gapK`
  — `v_p(k) = 1` last `p³ X = C₁¹³` with `C₁ ≡ k/p ≢ 0`.
- Residue kills with hypotheses: `3 ∣ B` and `k ≡ 2 mod 3`;
  `5 ∣ B` and `k ≡ 2,3,4 mod 5`; `7 ∣ B` and `k ≡ 3,5,6 mod 7`.
- `gcd_A_B_eq_one_of_remaining_gapK` — if no prime of `k` divides
  `B`, then `gcd(A,B) = 1`.
- `no_positive_coprime_gapK_of_axiom` — positive coprime solutions
  die relative to `darmon_merel_4413_axiom`.
- Recover `no_gapN_of_axiom` for `N = 2..9,11..15` and odd-`B`
  gap-10.
- Logs / LLL lose on every `k ≥ 1` solution with `B ≥ B0`,
  including `C1_floor`.
- `baker_bound_gapK` / `hGen_gapK` / `hLLL_gapK` stay `def Prop`.

`#print axioms baker_bound_gapK_unconditional_nogo` is
`[propext, Classical.choice, Quot.sound]` only.
