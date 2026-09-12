# v20.0.0 Matveev inequality skeleton

`lean/BealLevel26Foundations/Beal/FullProof/BealMatveevInequality.lean`

Names the linear form with Mathlib `Real.log`:

- `matveev_log_form A B = 4 log A - 13 log(B+3)`
- `matveev_log_form_eq` by `rfl`
- `matveev_lower_bound_scale = matveev_C1_floor = 143186215390`
  (`matveev_lower_bound_scale_pos` by decide, no axioms)
- `matveev_lower_bound` stays an uninhabited **def Prop**
  (`|Λ| > exp(-C1_floor * 30^{n+3})`)
- Tate c4 scale 16 reused (`matveev_inequality_c4_height`)
- `matveev_inequality_constants : List Int`;
  `matveev_inequality_constants_hold` by decide (**no axioms**)

`baker_bound_gap3` stays a **def Prop**.
`baker_bound_gap3_of_matveev_inequality` is the named
implication (not inhabited). Mathlib 4.12 has no
Matveev 2000 Thm 1.4. Does not use sorry.
