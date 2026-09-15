# Beal/Matveev/

LEAN_PATH stubs. Lake puts the relocated kernel's `Beal/` prefix
first, so sibling `import Beal.Matveev.*` does not resolve to this
tree. Theorems live in the matching **root** modules:

| Stub | Root module |
|---|---|
| `MatveevThm14General.lean` | (this file is the package entry; not a stub) |
| `MatveevThm14Proof.lean` | `MatveevThm14Proof.lean` |
| `MatveevLLL.lean` | `MatveevLLL.lean` |
| `MatveevInterpolation.lean` | `MatveevInterpolation.lean` |
| `MatveevBugeaud.lean` | `MatveevBugeaud.lean` |
| `WuestholzSubgroup.lean` | `WuestholzSubgroup.lean` |
| `WuestholzProduct.lean` | `WuestholzProduct.lean` |
| `MatveevThreeLogs.lean` | `MatveevThreeLogs.lean` |
| `BealKraus.lean` | `BealKraus.lean` |
| `BealKrausZsig.lean` | `BealKrausZsig.lean` |
| `BealCatalanZsig.lean` | `BealCatalanZsig.lean` |
| `BealDarmonMerel.lean` | `BealDarmonMerel.lean` |
| `BealDarmonMerel44p.lean` | `BealDarmonMerel44p.lean` |
| `BealFLT13.lean` | `BealFLT13.lean` |
| `BealGenuineV25.lean` | `BealGenuineV25.lean` |
| `BealTrueV25.lean` | `BealTrueV25.lean` |
| `BealUnconditionalV25.lean` | `BealUnconditionalV25.lean` |
| `BealGap1.lean` | `BealGap1.lean` |
| `BealGap2.lean` | `BealGap2.lean` |
| `BealGap4.lean` | `BealGap4.lean` |
| `BealGap5.lean` | `BealGap5.lean` |
| `BealGap6.lean` | `BealGap6.lean` |
| `BealGap7.lean` | `BealGap7.lean` |
| `BealGap8.lean` | `BealGap8.lean` |
| `BealGap9.lean` | `BealGap9.lean` |
| `BealGap10.lean` | `BealGap10.lean` |
| `BealGap11.lean` | `BealGap11.lean` |
| `BealGap12.lean` | `BealGap12.lean` |
| `BealGap13.lean` | `BealGap13.lean` |
| `BealGap14.lean` | `BealGap14.lean` |
| `BealGap15.lean` | `BealGap15.lean` |
| `BealGapK.lean` | `BealGapK.lean` |
| `EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.lean` | `EffectiveLevelLoweringPAdicLinearForms_A4_B4_C13_B0_1e6.lean` |

Do **not** import `Beal.Matveev.MatveevThm14General` from the
interpolation / LLL / Bugeaud / Wüstholz / Product / ThreeLogs /
Kraus / KrausZsig / CatalanZsig / DarmonMerel / DarmonMerel44p /
FLT13 / GenuineV25 / TrueV25 / UnconditionalV25 / Gap1 / Gap2 /
Gap4 / Gap5 / Gap6 / Gap7 / Gap8 / Gap9 / Gap10 / Gap11 / Gap12 / Gap13 / Gap14 / Gap15 / GapK / EffectiveLevelLowering modules.

`hGen`, `hLLL`, and `baker_bound_gap3_of_hGen_hLLL` stay
uninhabited `def Prop`. `baker_bound_gap3` stays a `def Prop`
(the theorem is named `baker_bound_gap3_true` in `BealTrueV25`,
and depends on `axiom darmon_merel_4413_axiom`).
`hGen_gap1`, `hLLL_gap1`, and `baker_bound_gap1` stay
uninhabited `def Prop` (`baker_bound_gap1_true` reuses the
same axiom). `hGen_gap2`, `hLLL_gap2`, and `baker_bound_gap2`
stay uninhabited `def Prop` (`baker_bound_gap2_true` reuses the
same axiom). `hGen_gap4`, `hLLL_gap4`, and `baker_bound_gap4`
stay uninhabited `def Prop` (`baker_bound_gap4_true` reuses the
same axiom). `hGen_gap5`, `hLLL_gap5`, and `baker_bound_gap5`
stay uninhabited `def Prop` (`baker_bound_gap5_true` reuses the
same axiom). `hGen_gap6`, `hLLL_gap6`, and `baker_bound_gap6`
stay uninhabited `def Prop` (`baker_bound_gap6_true` reuses the
same axiom). `hGen_gap7`, `hLLL_gap7`, and `baker_bound_gap7`
stay uninhabited `def Prop` (`baker_bound_gap7_true` reuses the
same axiom). `hGen_gap8`, `hLLL_gap8`, and `baker_bound_gap8`
stay uninhabited `def Prop` (`baker_bound_gap8_true` reuses the
same axiom). `hGen_gap9`, `hLLL_gap9`, and `baker_bound_gap9`
stay uninhabited `def Prop` (`baker_bound_gap9_true` reuses the
same axiom). `hGen_gap10`, `hLLL_gap10`, and `baker_bound_gap10`
stay uninhabited `def Prop` (`baker_bound_gap10_true` reuses the
same axiom on odd `B`). `hGen_gap11`, `hLLL_gap11`, and `baker_bound_gap11`
stay uninhabited `def Prop` (`baker_bound_gap11_true` reuses the
same axiom). `hGen_gap12`, `hLLL_gap12`, and `baker_bound_gap12`
stay uninhabited `def Prop` (`baker_bound_gap12_true` reuses the
same axiom). `hGen_gap13`, `hLLL_gap13`, and `baker_bound_gap13`
stay uninhabited `def Prop` (`baker_bound_gap13_true` reuses the
same axiom). `hGen_gap14`, `hLLL_gap14`, and `baker_bound_gap14`
stay uninhabited `def Prop` (`baker_bound_gap14_true` reuses the
same axiom). `hGen_gap15`, `hLLL_gap15`, and `baker_bound_gap15`
stay uninhabited `def Prop` (`baker_bound_gap15_true` reuses the
same axiom). `hGen_gapK`, `hLLL_gapK`, and `baker_bound_gapK`
stay uninhabited `def Prop` (`baker_bound_gapK_true_of_positive_coprime`
reuses the same axiom on positive coprime solutions; not `∀k ¬sol`).
`hGen_padic`, `hLLL_padic`, and `baker_bound_B0_1e6` stay
uninhabited `def Prop` (Bugeaud–Laurent / Kraus / Oesterlé /
Ribet-to-32 / FLT 13 are not in Mathlib 4.12; `C<100` is only
under `A,B≤B0`).
`baker_davenport_reduction`, `bugeaud_LLL_reduction_proof`,
`wuestholz_subgroup_theorem`, and `wuestholz_product_theorem_exp`
stay uninhabited `def Prop`.
