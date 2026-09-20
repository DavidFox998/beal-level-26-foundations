# HonestB0Search (foundations v29)

Lake targets `HonestB0Search` and `Level26` compile only this
folder. They do not enter `Level26/BealLevel26Foundations`
and do not join `.submodules Beal.Matveev`.

v29 final algebraic slices:

* Tate / Néron final: `Tate_Frey_Conductor_29_Neron_final.lean`
  — theorems `Tate_algorithm_at_29` /
  `Frey_Neron_conductor` / `Frey_conductor_29_is_Neron`
  re-export `Tate_algorithm_at_2_and_29`. Displayed
  `N_E = 928` is the numeral `2⁵ · 29`, not Mathlib
  Néron. Lean 4.12: explicit types, `open Nat Finset
  Classical`, `decide` not `native_decide`. Parent defs
  stay. See `docs/Tate_Neron_29_v29.md`.
* Mazur / no-isogeny final: `Mazur_X0_13_No_Isogeny_final.lean`
  — `2184`, `48<2184`, `13=2²+3²`, `288/48=6`, cusp
  Finset `{0,1}` card `2`. Honest: genus `0` ⇒ infinite;
  `{2 cusps}=X₀(13)(ℚ)` is literature-false. Parent defs
  stay. See `docs/Mazur_Cusps_v29.md`.
* Ribet / 928→32 final: `Ribet_Level_Lowering_29_to_32_final.lean`
  — `928/29=32`, `32·29=928`, `29∤32`, `2⁴=16`, `16∣32`,
  dim `1` / `0`, Sturm `48` / `8`, matching `∅` card `0`.
  Honest: LMFDB new dim `1` (`32a1`); Sage
  `new_subspace().dimension()=0` is not a theorem. Parent
  defs stay. See `docs/Ribet_No_Newforms_32_v29.md`.
* Kolyvagin / rank-0 final: `Kolyvagin_MW_Rank0_26a1_26b1_final.lean`
  — `|Sel₂|=1`, `3·7=21`, `L/Ω=1/3` `1/7`, `¬ IsRankZero`,
  `Nonempty (Fintype) → Finite`, Unit card `1`. Honest:
  Subsingleton is false on torsion `3`/`7`; parent
  `MW_rank_zero_fintype` stays `def Prop`. See
  `docs/Kolyvagin_Rank0_v29.md`.

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
