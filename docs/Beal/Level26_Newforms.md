# v8.68.0-kraus-elim-53-443 displayed a53 miss

`lean/BealLevel26Foundations/Beal/FullProof/Level26_Newforms.lean`
and `RibetMazur.lean`

Locked ledger prefixes of length 100:
`newform_26_a_qexp_100` / `newform_26_b_qexp_100`
are `List.take 100` of `qExp_26a1` / `qExp_26b1`.
Index 53 is in range.  Index 443 is not
(`[443]? = none`).  Ledger values:
`a₅₃(26a1)=0`, `a₅₃(26b1)=12`.  The sketch
values 6 and -2 are false.

`hasSmallZsigWitness_1500003` is inhabited by
`decide` on `ZMod 443` / numeral `443*443`
(same hit as Step56 row `(1500003,1500006)`).
Not `True`.  Not `native_decide`.

`displayed_two_misses_a53_26a1` is
`2 ≢ 0 [MOD 13]`.  The integer 2 is a
displayed placeholder, not computed
`a₅₃(E_{196})`.
`level26_a_eliminated_by_53_of_witness` is
`hasSmallZsigWitness 196 →` that miss.
`level26_b_eliminated_by_443_of_witness` is
`hasSmallZsigWitness 1500003 →` no `a₄₄₃`
in the locked 100-prefix.

Those are **not** Kraus matching and do
**not** inhabit `level26_a_eliminated_by_53`
or `level26_b_eliminated_by_443` (those
stay the same uninhabited `∀` as
`kraus_elimination_q_13_level_26`).

Does **not** import `RibetMazur` (cycle).
Does **not** import
`Mathlib.NumberTheory.ModularForms.Basic`.
Not imported by the 24-module none chain.

`kraus_elimination_q_13_level_26` stays
uninhabited.
`ExistsNewformLevel2` stays `0 != 0`.
`beal_from_ribet` still takes
`ModularImpliesLevel2Newform`.
No new Beal forall.
Not Full Mathlib forall.
