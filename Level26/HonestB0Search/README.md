# HonestB0Search (foundations v29)

Lake targets `HonestB0Search` and `Level26` compile only this
folder. They do not enter `Level26/BealLevel26Foundations`
and do not join `.submodules Beal.Matveev`.

v29 final Tate slice (this branch):

* Tate / Néron final: `Tate_Frey_Conductor_29_Neron_final.lean`
  — theorems `Tate_algorithm_at_29` /
  `Frey_Neron_conductor` / `Frey_conductor_29_is_Neron`
  re-export `Tate_algorithm_at_2_and_29`. Displayed
  `N_E = 928` is the numeral `2⁵ · 29`, not Mathlib
  Néron. Lean 4.12: explicit types, `open Nat Finset
  Classical`, `decide` not `native_decide`. Parent defs
  stay. See `docs/Tate_Neron_29_v29.md`.

v28 algebraic slices:

* Tate / Néron: `Tate_Frey_Conductor_29_Neron_inhabited.lean`
  — `928 = 2⁵ · 29`. See `docs/Tate_Neron_29_v28.md`.
* Mazur cusps: `Mazur_X0_13_Cusps_Equals_Rationals_inhabited.lean`
  — genus `0`, cusp Finset `card = 2`.
  `X₀(13)(ℚ) = {2 cusps}` is literature-false.
  See `docs/Mazur_Cusps_v28.md`.
* Ribet no-newforms: `Ribet_No_Newforms_At_32_inhabited.lean`
  — `928/29=32`, Sturm `8`, matching Finset `card = 0`.
  Sage `new_subspace().dimension()=0` is not a theorem.
  See `docs/Ribet_No_Newforms_32_v28.md`.
* Kolyvagin Fintype: `Kolyvagin_Fintype_Subsingleton_inhabited.lean`
  — `Nonempty (Fintype α) → Fintype α`, `|Sel₂|=1`,
  `3·7=21`, `¬ IsRankZero`. `MW_rank_zero_fintype` stays
  `def Prop`. See `docs/Kolyvagin_Fintype_Subsingleton_v28.md`.
