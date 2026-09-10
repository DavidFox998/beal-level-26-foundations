# v8.68.1-frey-ap-53-443 computed Frey traces

`lean/BealLevel26Foundations/Beal/FullProof/Level26_Newforms.lean`
and `RibetMazur.lean`

`newform_26_a_qexp_100` / `newform_26_b_qexp_100`
are `List.take 500` of `qExp_26a1_500` /
`qExp_26b1_500`.  Those 500-lists extend the
SHA-locked 101-coeff JSON from the certified
Weierstrass models `[1,0,1,-5,-8]` and
`[1,-1,1,-3,3]`.  The SHA of
`sagemath/level_26_ledger.json` is unchanged.
Index 53 and 443 are both in range.
Ledger values: `a₅₃(26a1)=0`, `a₅₃(26b1)=12`,
`a₄₄₃(26a1)=21`, `a₄₄₃(26b1)=-39`.  The sketch
values 6 and -2 for `a₅₃` are still false.

`a53_E_196` is the point-count trace of the
displayed model
`E_{196}: y² = x(x − 196⁴)(x + 199⁴)`
mod 53, proved `= -2` by `decide`.
That misses both locked `a₅₃` values at
`ℓ = 13`.  The placeholder integer 2 is
not used.

`a443_E_1500003` is the point-count trace of
`E_{1500003}: y² = x(x − 1500003⁴)(x + 1500006⁴)`
mod 443, proved `= 24` by `decide`.
That misses both locked `a₄₄₃` values at
`ℓ = 13`.

`hasSmallZsigWitness_1500003` is inhabited by
`decide` on `ZMod 443` / numeral `443*443`
(same hit as Step56 row `(1500003,1500006)`).
Not `True`.  Not `native_decide`.

`level26_a_eliminated_by_53_of_witness` is
`hasSmallZsigWitness 196 →` the computed
`a₅₃(E_{196})` miss against both forms.
`level26_b_eliminated_by_443_of_witness` is
`hasSmallZsigWitness 1500003 →` the computed
`a₄₄₃(E_{1500003})` miss against both forms.

Those are **not** Kraus matching and do
**not** inhabit `level26_a_eliminated_by_53`
or `level26_b_eliminated_by_443` (those
stay the same uninhabited `∀` as
`kraus_elimination_q_13_level_26`).
The displayed Weierstrass model is not a
theorem that the Beal Frey curve equals it.

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
