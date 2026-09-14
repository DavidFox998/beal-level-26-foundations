# v20.0.0 Bugeaud LLL formal skeleton

`lean/BealLevel26Foundations/Beal/FullProof/BealBugeaudLLLFormal.lean`

Integer LLL lattice matching the v17 PARI qflll cert:

- `bugeaud_K = 10^20` (`bugeaud_K_eq` by decide, no axioms)
- `bugeaud_lattice = K * (4 log B0, 9 log B0, 13 log(B0+3))`
  using Mathlib `Real.log`
- `bugeaud_lattice_int` is the rounded integer last row
  (`bugeaud_lattice_int_holds` by decide, no axioms)
- `bugeaud_LLL_basis` is the three v17 qflll rows
  (`bugeaud_LLL_basis_holds` by decide, **no axioms**)
- `bugeaud_LLL_basis_eq_v17` matches
  `baker_reduction_certificate_displayed.drop 3 |>.take 3` by `rfl`
- `bugeaud_B0_raw = 104382751019310000000`
- `bugeaud_B0_reduced = 1000000`
- `bugeaud_reduction_formal` stays an uninhabited **def Prop**

`baker_bound_gap3` stays a **def Prop**.
Mathlib 4.12 has no LLL reduction theorem.
The foundations complement `MatveevLLL.lean` proves the elementary
continued-fraction lemmas (`4/13` is a convergent of
`log(B+3)/log A`; integer gap `< B⁴/A⁴`) and keeps
`bugeaud_LLL_reduction_proof` as an uninhabited `def Prop`.
`MatveevBugeaud.lean` proves the displayed `C=10^{30}` lattice
cannot inhabit that Prop: usable Baker–Davenport satisfies
`(r−17)/C < |Λ|`.
Being a convergent does not force `B ≤ 10⁶`. Not v25.
Does not use sorry.
