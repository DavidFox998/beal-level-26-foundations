# WuestholzProduct — full-order product packaging (not Philippon)

Lean: [`WuestholzProduct.lean`](../../WuestholzProduct.lean)
(root module; `Beal/Matveev/WuestholzProduct.lean` is the LEAN_PATH stub).
Namespace: `BealMatveevBeal.WuestholzProduct`.
Concept DOI `10.5281/zenodo.22379293`.
`C1_floor = 143186215390` (`rfl`). `B0_nat = 1000000` (`rfl`).

Successor of `1353501` (`v24-v24x-final-Wuestholz-no-uniform-c`).
Mathlib 4.12 has no Philippon zero estimate. The uniform product
theorem (`T ≥ C1 D` ⇒ `X` is a coset of a proper subgroup) is
**not** a theorem here.

## What is proved (0 sorry)

Axioms `[propext, Classical.choice, Quot.sound]` only.

- `wuestholz_product_theorem_exp_Ga_base`: on `𝐆_a`, multiplicity
  `≤` degree (dimension-1 base).
- `wuestholz_product_theorem_exp_of_full_order_reexport`:
  `T ≥ coeffCount` ⇒ `P = 0 ∨` dependence.
- `wuestholz_product_theorem_exp_or_small_T`:
  `T < coeffCount ∨ P = 0 ∨` dependence.
- `wuestholz_product_theorem_exp_one_ten_ten`: displayed degrees
  `L = 1`, `N1 = N2 = 10` give `T < 242 ∨ P = 0 ∨` dependence.
- `wuestholz_product_theorem_exp_of_jet_dim`: same inhabitant as
  `wuestholz_subgroup_theorem_of_jet_dim` (`1353501`); requires
  the jet dimension to already be `≤ c L K`.
- `no_uniform_c_for_product_theorem`: induction on `N1,N2` cannot
  produce a uniform threshold of shape `c L K`.

## What stays a def Prop

- `wuestholz_product_theorem_exp` — uniform exponential product
  along `W` below full jet order (Philippon).
- `wuestholz_subgroup_theorem` — uniform `T ≥ c L K`.
- `baker_davenport_reduction` / `bugeaud_LLL_reduction_proof`.

The proved LLL method-failure (`bugeaud_LLL_method_fails`) lives
in `MatveevBugeaud.lean`. The log-method no-go
(`baker_bound_gap3_nogo_logs`) lives in
[`BealMatveevThreeLogs.md`](BealMatveevThreeLogs.md).
The displayed Frey / Kraus no-go (`baker_bound_gap3_kraus_nogo`)
lives in [`BealKraus.md`](BealKraus.md).
Not a minted v25 tag.
