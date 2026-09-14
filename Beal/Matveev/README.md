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

Do **not** import `Beal.Matveev.MatveevThm14General` from the
interpolation / LLL / Bugeaud / Wüstholz / Product / ThreeLogs /
Kraus / KrausZsig / CatalanZsig / DarmonMerel / DarmonMerel44p /
FLT13 / GenuineV25 / TrueV25 / UnconditionalV25 / Gap1 modules.

`hGen`, `hLLL`, and `baker_bound_gap3_of_hGen_hLLL` stay
uninhabited `def Prop`. `baker_bound_gap3` stays a `def Prop`
(the theorem is named `baker_bound_gap3_true` in `BealTrueV25`,
and depends on `axiom darmon_merel_4413_axiom`).
`hGen_gap1`, `hLLL_gap1`, and `baker_bound_gap1` stay
uninhabited `def Prop` (`baker_bound_gap1_true` reuses the
same axiom). `baker_davenport_reduction`, `bugeaud_LLL_reduction_proof`,
`wuestholz_subgroup_theorem`, and `wuestholz_product_theorem_exp`
stay uninhabited `def Prop`.
