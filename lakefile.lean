import Lake
open Lake DSL

package beal_matveev_beal where
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4" @ "v4.12.0"

/-- Relocated v24.4.0 package (DOI 10.5281/zenodo.22732209, db7a556).
    Modules are `BealLevel26Foundations.Beal.FullProof.*`.
    `BealConjecture.Level26.BealLevel26Foundations.*` are local wrappers. -/
require beal_level_26_foundations from git
  "https://github.com/DavidFox998/beal-conjecture" @ "main"
  / "Level26/BealLevel26Foundations"

/-- Re-export wrappers so the requested import path resolves. -/
lean_lib BealConjecture where
  globs := #[.submodules `BealConjecture]

@[default_target]
lean_lib «BealMatveevBeal» where
  globs := #[.submodules `Beal.Matveev, .one `MatveevThm14Proof, .one `MatveevLLL,
    .one `MatveevInterpolation, .one `MatveevBugeaud, .one `WuestholzSubgroup,
    .one `WuestholzProduct, .one `MatveevThreeLogs, .one `BealKraus, .one `BealKrausZsig,
    .one `BealCatalanZsig, .one `BealDarmonMerel, .one `BealDarmonMerel44p,
    .one `BealFLT13, .one `BealGenuineV25, .one `BealTrueV25,
    .one `BealUnconditionalV25, .one `BealGap1, .one `BealGap2, .one `BealGap4,
    .one `BealGap5, .one `BealGap6, .one `BealGap7, .one `BealGap8,
    .one `BealGap9, .one `BealGap10, .one `BealGap11, .one `BealGap12,     .one `BealGap13,
    .one `BealGap14, .one `BealGap15, .one `BealGapK,
    .one `EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6,
    .one `BugeaudLaurent, .one `PAdicLLL, .one `PAdicLLL_ZeroAxiom]

/-- Rank-3 v25 *shape* wrappers. Not the default target: keeps
    `lake build BealMatveevBeal` independent of this file. Does
    not mint v25. -/
lean_lib «BealMatveevBealV25Rank3» where
  globs := #[.one `BealMatveevBealV25Rank3]

/-- Gap-3 `B ≤ B0` search slice. Not the default target. Does
    not mint v25. Does not claim the full million-B search.
    `Gap3B0Million` is the foldl wiring for 10k shards of 100;
    those shards are not `native_decide`'d.
    `LLLTargetB8_C1_lower_bound` is `C1' ≤ 8` impossible on a
    solution via `|Λ| ≤ 2/B⁹`; `¬ LLL_reduces_C1_to_lt_nine`
    stays `def Prop`. `DarmonMerelFrey4413` is the displayed
    Frey curve for signature `(4,4,13)`; level-32 table stays
    `def Prop`. `Level32Table` is LMFDB `32a1` q-exp by
    `𝔽_p` point counts; `level_32_no_newform` stays `def Prop`.
    `Level928Table` is the `29 ∣ ABC` split and displayed residual
    `928`; the 77-row table stays `def Prop`. `Ribet29C_Lowering`
    is `29 ∣ C` plus the `l=7` residue `(2,3)`; Ribet stays
    `def Prop`. `Ribet29C_Residue16` is `l=11` on residue
    `(1,6)`; that class is mixed at `11` and stays `def Prop`.
    `Ribet29C_Residue16_L23` is `l=23` on the same class; mixed
    (`a₂₃=0` matches, not `−6`) and stays `def Prop`.
    `MazurIrreducibility13` inhabits `v₂₉(j)≤−26` on `29 ∣ C`;
    Mazur/Ribet/image stay `def Prop`. `Inertia29Unramified`
    inhabits `v₂₉(c₄)=0` and Tate numerics; Kodaira/Ribet inertia
    stay `def Prop`. `SerreImage13` inhabits `32a1` `j=1728`;
    CM image / Serre open image stay `def Prop`.
    `MazurIrreducibilityFull` / `TateGalois` / `SerreImageFull`
    name the four Mathlib gaps as `def Prop` and re-export the
    `9030063` numerics. -/
lean_lib «BealMatveevBealV25B0Search» where
  globs := #[.one `BealMatveevBealV25B0Search, .one `LLLTargetB8, .one `Gap3B0Million,
    .one `LLLTargetB8_C1_lower_bound, .one `DarmonMerelFrey4413, .one `Level32Table,
    .one `Level928Table, .one `Ribet29C_Lowering, .one `Ribet29C_Residue16,
    .one `Ribet29C_Residue16_L23, .one `MazurIrreducibility13,
    .one `Inertia29Unramified, .one `SerreImage13,
    .one `MazurIrreducibilityFull, .one `TateGalois, .one `SerreImageFull]
