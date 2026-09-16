# Darmon–Merel 4413 barrier (`953a174` → Mazur `j`-valuation)

This archive records the honest checkpoint of the Frey / level-32
sieve on signature `(4,4,13)`, `A⁴ + B⁴ = (B+3)¹³`. It is **not** a
v25 mint and it does **not** close `B ≥ B0`.

## Pins

| Object | SHA | Role |
| --- | --- | --- |
| foundation tag `v24.1-foundation-B1000-Lambda-B9-6247c63` | `6247c63` | `B<1000` foldl + `\|Λ\|≤2/B⁹`; 0 sorry; `Beal.Matveev` glob adds no new axiom |
| `main` | reset to `6247c63` | default `lake build BealMatveevBeal` stays the foundation |
| `phase-main-nogo-f337dd5` | `f337dd5` | nogo note that had been on `main` |
| `phase-lll-lift-b8` | `e5a95f5` | `LLL_reduces_C1_to_lt_nine ↔ no_sol_ge_B0` |
| `phase-darmon-merel-4413` | this tree | Frey `Δ`, LMFDB `32a1` traces, `v₂₉`, mixed sieves, Mazur `j`, Tate numerics, `32a1` `j=1728` |
| tag `v24-v24x-final-rank3-shape-nogo` | `c1d173e` | do not move |
| v25 | not minted | `hGen` / `hLLL` stay `def Prop` |

The only Darmon–Merel **axiom** in the default glob remains
`BealTrueV25.darmon_merel_4413_axiom`. Root sieve modules live on
the separate Lake target `BealMatveevBealV25B0Search` and do not
redefine that name.

## LLL nogo (`e5a95f5`) is independent of Frey

On a solution with `B ≥ 100`, `|Λ| ≤ 2/B⁹`. The LLL target
`|Λ| ≥ B⁻⁸` would need a reduced constant `C1' ≤ 8`. Typical
Bugeaud–Laurent constants are `30`–`50`. On a putative solution
`2/B⁹ < 1/B⁸`, so `C1' ≤ 8` is impossible. Hence

```
LLL_reduces_C1_to_lt_nine  ↔  ∀ B ≥ B0, ∀ A, A⁴+B⁴ ≠ (B+3)¹³
```

is a theorem (`LLLTargetB8_C1_lower_bound`). Negation of the LLL
hypothesis stays `def Prop`. C-scaling does not replace this
equivalence. Mazur / Ribet / image work, if ever inhabited, would
be a **separate** implication, not a replacement of C-scaling.

`MazurIrreducibility13.LLL_and_DarmonMerel_separate` re-exports
that iff. The Mazur close stays `def Prop`.

## Displayed Frey curve

Model `y² = x(x−A⁴)(x+B⁴)`:

- `Δ = 16 A⁸ B⁸ (A⁴+B⁴)²`, on a solution `16 A⁸ B⁸ C²⁶`
- `c₄ = 16(A⁸ + B⁸ + A⁴B⁴)` (not a stub with `C²⁶`)
- `j = c₄³ / Δ` as `ℚ`

LMFDB `32a1` (`y² = x³+4x`, conductor 32), recomputed by `𝔽_p`
affine counts `a_p = p − #affine`:

`a₃=0`, `a₅=−2`, `a₇=0`, `a₁₁=0`, `a₁₃=6`, `a₂₃=0`, `a₂₉=−10`.

## What a single prime can kill

On a solution, `gcd(B, B+3) ∣ 3`, so `29` divides at most one of
`A,B,C`.

| Residue | Prime | Trace vs `32a1` | Status |
| --- | --- | --- | --- |
| good `29 ∤ ABC` | `29` | `a₂₉ ≠ −10` | dies (`9a9caa0`) |
| `(2,3) (mod 7)` | `7` | `a₇ = −4 ≠ 0` | dies if traces forced |
| `(2,6) (mod 11)` | `11` | `a₁₁ = −4 ≠ 0` | dies if traces forced |
| `(4,22) (mod 23)` | `23` | `a₂₃ = 8 ≠ 0` | dies if traces forced |
| `(1,6) (mod 7)` | `7` | `a₇ = 0` | **matches** |
| `(6,6) (mod 7)` | `7` | `a₇ = 0` | **matches** |

The surviving class `(A,B) ≡ (1,6) (mod 7)` is mixed at every
tested auxiliary prime:

- `l=11` (`1636a62`): `frey_ap 11 1 6 = 0` matches (and `(1,6)` is
  not even on-solution mod `11`). CRT lifts include `a₁₁=0`
  (`A=15,B=69` and `29∣C` witness `B=1070`) and `a₁₁=−4`
  (`A=57,B=6`).
- `l=23` (`953a174`): `curve32a1_ap 23 = 0` (`#E(𝔽₂₃)=24`), not
  `−6`. Eight good on-solution residues match `a₂₃=0`, ten
  mismatch `{8,4,−4}`. Proper CRT is
  `a + 7·(7⁻¹ mod 23)(b−a)`, not `(a·7+1) % 161`. Every `𝔽₂₃`
  residue lifts through `161=7×23`, so the class inherits every
  trace. Match witness `A=1,B=118`; mismatch `A=50,B=160`
  (`a₂₃=8`); `29∣C` match `B=2694`. The pair `A=15,B=69` is
  `23∣B` (bad reduction), not a good-reduction test.

## Why the whole `(1,6)` class never dies at one `l`

Chebotarev / CRT: for a fixed class mod `7`, and `l` coprime to
`7`, the on-solution set mod `l` always contains both matching
and mismatching `a_l`, because `Frey_{A,B}` varies with `A,B mod
l`. A single-prime sieve can kill **slices** (`(4,22) mod 23`)
but not the whole CRT class. Point-count matching at
`l=3,5,7,11,23` will always have some `a_l=0` lifts surviving.

`residue_1_6_eliminated_at_23` and
`no_sol_ge_B0_29C_1_6_of_l23` therefore stay `def Prop`.
`level_32_no_newform` stays `def Prop` for the same reason:
the empty-table claim is Ribet + modularity + image, not a
finite list of `a_l`.

## Mazur input that **is** inhabited

When `29 ∣ C` and `29 ∤ AB`:

- `v₂₉(Δ) = 26 v₂₉(C) ≥ 26` and `13 ∣ v` (`49d4ade`)
- `29 ∤ c₄` (`t²+t+1` has no root mod `29`; `−3` is a
  nonresidue)
- so `v₂₉(j) ≤ −26`, hence `29 ∣ j.den` and `j.den ≠ 1`

That is the Mazur **input** “`j` is not integral at `29`”. It is
not Mazur’s irreducibility theorem, not Ribet inertia at `I₂₉`,
and not Serre open image.

Root `MazurIrreducibility13.lean` inhabits those valuation
theorems. The following stay `def Prop` (no new axiom):

- `rho_Frey_mod13_irreducible` (alias of displayed Mazur Prop)
- `ribet_29C_lowers_to_32` / `ribet_lowers_Frey_to_level_32`
- `serre_open_image_vs_32a1_CM`
- `mazur_and_ribet_hyp`
- `no_sol_ge_B0_of_darmon_merel_4413`
- `frey_j_not_integral_of_B_ge_B0` (global, all primes)

To inhabit `BealTrueV25.darmon_merel_4413_axiom` one still needs
Mazur irreducibility of `ρ_{Frey,13}` for `B≥B0`, Ribet lowering
at primes with `13 ∣ v_ℓ(Δ)` (Galois inertia `I_ℓ`, not just
`padicValNat`), modularity, and Serre open image of Frey versus
the CM / dihedral image of `32a1`. None of that is in Mathlib
4.12. Level 32 tables in this tree are **docs of the barrier**,
not a close.

## `I₂₉` numerics vs Galois inertia

Root `Inertia29Unramified.lean` inhabits the Tate **input** when
`29 ∣ C` and `29 ∤ AB`:

- `v₂₉(c₄) = 0` (`padicValInt`, from `29 ∤ c₄`)
- `29 ∣ Δ` and `v₂₉(Δ) = 26 v₂₉(C) ≥ 26`
- `displayed_minimal_at_29` (Silverman: `v(c₄)=0` blocks a
  `u`-scaling)

Tate’s Kodaira symbol `I_{26k}` (multiplicative reduction) and
`ρ_{E,13}(I_{29})=1` stay `def Prop`. There is no `InertiaGroup`
in Mathlib 4.12 and no Tate-curve Galois module. `True := trivial`
is not a Kodaira classification.

## `32a1` has `j=1728`; image size stays `def Prop`

Root `SerreImage13.lean` inhabits the Weierstrass computation
for `y²=x³+4x`: `c₄=−192`, `Δ=−4096`, `j=1728`. Also `13≡1
(mod 4)` and `|SL₂(𝔽₁₃)|=2184 > 48`. When `29 ∣ C`, Frey `j`
has denominator divisible by `29`, so `j ≠ 1728`.

That is not CM as a Galois object, not `card(im ρ_{32a1,13})≤48`,
and not Serre open image for Frey. `image_32a1_mod13_small`,
`serre_large_image`, `darmon_merel_4413_full`, and
`no_sol_ge_B0_of_image_contradiction` stay `def Prop`. There is
no `axiom serre_large_image_13_axiom`.

## Four Mathlib gaps (`9030063` → full scaffold)

Closing `B ≥ B0` is **four gaps** (four theorems), not `a₇=−4` / `a₁₁=−4` /
`a₂₃=8` slice kills (`953a174`). Root modules
`MazurIrreducibilityFull`, `TateGalois`, `SerreImageFull`
re-export the inhabited numerics and keep the Galois statements
as `def Prop`. No new axiom; `main` stays `6247c63`.

1. **Mazur irreducibility.** Inhabited: `29 ∣ j.den`, `j ≠ 0`,
   `j ≠ 1728` when `29 ∣ C`. Missing: `HasCM`, Mazur 1978,
   Bilu–Parent–Rebolledo 2013.
2. **Galois `I₂₉`.** Inhabited: `v(c₄)=0`, `v(Δ)=26 v(C)`.
   Missing: Tate curve `ℚ̄_ℓˣ / q^ℤ` and `χ_cyc^{v(q)}`.
3. **Modularity + Ribet to 32.** Missing: Wiles modularity of
   the semistable Frey curve; Ribet `29·32 → 32` after
   unramified `I₂₉`. Not added as axioms on `BealTrueV25`.
4. **Serre large vs `32a1` small.** Inhabited: `j(32a1)=1728`,
   `48 < 2184 = |SL₂(𝔽₁₃)|`. Missing: Serre 1972 open image
   and `card(im ρ_{32a1,13}) ≤ 48`.

`darmon_merel_4413_four_gaps` and `no_sol_ge_B0_of_four_gaps`
stay `def Prop`. The `e5a95f5` LLL iff is re-exported.

## What this tree does not claim

- No `sorry`, no `True := trivial`, no fake `False.elim`.
- No new axiom on `BealMatveevBealV25B0Search`.
- No file under `Beal/Matveev/` for any of these root modules
  (that glob is the axiom-free Matveev surface on `main`).
- `C1_floor = 143186215390`, `B0_nat = 1000000` locked.
- Concept DOI `10.5281/zenodo.22379293`.
