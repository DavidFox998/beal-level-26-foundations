# v9.3.0 Baker-conditional gap-3 forall

`lean/BealLevel26Foundations/Beal/FullProof/BealGap3BakerUpperBound.lean`

`baker_B0 = 10^6` is a displayed Nat.

`baker_bound_gap3` stays the uninhabited
Baker / Bugeaud linear-forms-in-logs Prop:
exists `B0 = 10^6` such that every `B > B0`
has no `A` with `A^4 + B^4 = (B+3)^13`.
Bugeaud linear forms are external, not in
Mathlib 4.12.  `sorry` is not used.

Inhabited:

- `baker_conditional_gap3_full`:
  `baker_bound_gap3 → ∀ B, ¬∃ A`.
  `B ≤ B0` by the residue cover extended
  to `10^6`:
  - `B % 16 ≠ 14` via `beal_gap3_mod16_elim_not14`
    (15/16, including `[196, 1500003]`)
  - `B ≡ 14` via fourth-power tests at
    `q = 53, 29, 109` expanded by
    `17, 5, 7, 11, 13, 19, 23, 31, 37`
    (kernel census of the 62500 values
    `14, 30, …, 999998`)
  - `B > B0` by the Baker premise
- Allowed axioms
  `[propext, Quot.sound, Classical.choice]`

Keeps the three Zsig Props (needs Baker,
not Zsig), `frey_tate_conductor` Prop,
`conductor_86` Prop, `B14_honest` Prop.
Tate `tate_2adic_exponent_le5` /
`tate_odd_exponent_le_one` /
`tate_conductor_bound_rhs` stay.
Not BCDT.  Not an unconditional Beal `∀`.
