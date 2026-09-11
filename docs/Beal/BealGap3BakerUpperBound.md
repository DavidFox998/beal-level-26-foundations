# v9.0.0 Baker / Bugeaud effective bound (uninhabited)

`lean/BealLevel26Foundations/Beal/FullProof/BealGap3BakerUpperBound.lean`

Keeps the v8.86.0 empty-axiom residue cover:

- `B <= 2M` and `B % 16 != 14` via fourth powers mod 16
- 352 named `B == 14` rows via q = 53 / 29 / 109
  (`beal_..._B14_full`, empty axioms)

`baker_B0 = 10^6` is a displayed Nat.

`baker_bound_gap3` is the missing Baker / Bugeaud
linear-forms-in-logs statement:

exists `B0 = 10^6` such that every `B > B0` has no
`A` with `A^4 + B^4 = (B+3)^13`.

It is an **uninhabited Prop**.  Mathlib 4.12 has no
Baker theory.  `sorry` is not used (verify-scaffold
forbids it).  This is the honest hole.

`exists_zsig_q_gt_2M_dvd_C13_sub_B4` stays a Prop:
needs Baker, not Zsig.  The 5983 census is B <= 2M
density, not a >2M bound.

`conductor_86`, `B14_honest`, Density/Step kraus,
and Chain `ExistsNewformLevel2` (`0 != 0`) stay Props.
`frey_conductor_general` is unchanged (`|Delta| = 2^4 N0`,
`N0` divides `(ABC)^26 * 13`; not Tate).
Survivor `63982 = 2 * 31991` still shows
`N` does not divide `2^5 * 3 * 13`.
Not BCDT.
