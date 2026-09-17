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

## `X₀(13)` Fricke `j`-map (not a Mazur close)

Root `Mazur_X0_13_RationalPoints.lean` records the Fricke /
Fisher formula

```
j(t) = (t²+5t+13)(t⁴+7t³+20t²+19t+1)³ / t
```

(`X₀(13) ≅ ℙ¹`, degree 14). `X₀(13)(ℚ)` is infinite; there is
no finite list of rational `j`-invariants of 13-isogenies.
Mazur’s finite list is the **integral** `j` case.

Honest `𝔽₂₉` facts (the pasted scan was wrong):

- `t²+5t+13` has no root mod `29` (disc `≡ 2`, nonresidue)
- `f(t)` **does** vanish at `t ≡ 7,9 (mod 29)`; `f(0)=1`
- fourth powers in `𝔽₂₉` are `{0,1,7,16,20,23,24,25}` (not
  `{0,1,7,20,23,24,25,28}`)
- displayed `c₄` uses coefficient `1` in `A⁸+A⁴B⁴+B⁸`, not the
  Fermat-`14` form
- `v₂₉(j_Frey)=−26k` on `29 ∣ C`, `29 ∤ AB`
- if `j_Frey = j(t)` then `v₂₉(t) ∈ {26k, −2k}`

Both remaining cusps hit every unit of `𝔽₂₉ˣ` (`13 u⁻¹` at
`t ∼ 29^{26k}`, `u¹³` at `t ∼ 29^{-2k}` with `gcd(13,28)=1`).
A `∀ u, u·13⁻¹ ≠ RHS` native_decide cannot close Mazur.
`mazur_irreducible_13_via_X0_13` stays `def Prop`.

Gaps 2–4 stay `def Prop` in `Tate_I29_Inertia`,
`Ribet_Level32`, and `Serre_Large_vs_CM_Small`. `48 < 2184` is
a numeral theorem, not `False` without a Galois isomorphism.

## `X₀(26)` full 2-torsion (Momose / Kraus, not a Fricke scan)

Root `X0_26_Full2Torsion.lean` inhabits the displayed cubic
identity

```
x³ + (B⁴ − A⁴) x² − A⁴ B⁴ x  =  x(x − A⁴)(x + B⁴)
```

so the three affine 2-torsion `x`-coordinates `0, A⁴, −B⁴` lie
in `ℤ ⊂ ℚ` and are pairwise distinct for `A,B ≠ 0`. Mathlib
4.12 has no Galois module `E[2] ⊆ E(ℚ)`; the factorization is
the inhabitant that statement would use. The 2-torsion
polynomial is `4` times the affine cubic.

`X₀(13)` has genus 0, so `X₀(13)(ℚ)` is infinite and the Fricke
unit scan at `1d28dc1` cannot close Mazur. Full 2-torsion plus
reducible `ρ_{E,13}` would give a Galois-stable kernel
`C₂ × C₁₃ ≅ ℤ/26`, a cyclic rational 26-isogeny, hence a
non-cuspidal point of `X₀(26)` (genus 2). `X₀(52)` is the
cyclic-4 analogue.

Kenku 1979–81: cyclic isogeny degrees over `ℚ` are
`{1 ≤ N ≤ 19} ∪ {21,25,27,37,43,67,163}`. **26 and 52 are not
on that list** (Finset numeral in the Lean file). Completeness
of the list — emptiness of non-cuspidal `X₀(26)(ℚ)` — stays
`def Prop`. That is **not** a finite CM `j`-list
`{1728, −1728, 0, −3375, 8000}`. The contradiction with Frey is
emptiness, not `v₂₉(j) = −26k` versus integral CM. The
valuation still shows Frey `j` is non-integral when `29 ∣ C`
(any denominator-`1` rational, including those CM values, is
not Frey `j`); that weaker fact is inhabited.

`X₀(26)` is LMFDB `26.42.2.a.1` (genus 2, four rational
cusps), **not** elliptic curve `26.a2` and **not** genus-0
`26.48.0.a.1`. LMFDB odd Weierstrass
`y²+(x³+1)y = 2x⁵+2x⁴+4x³+2x²+2x` completes the square to
González 1991 (AIF 41 p. 794)
`Y² = x⁶−8x⁵+8x⁴−18x³+8x²−8x+1`. Affine theorems:
`(0,0),(0,−1)` on LMFDB and `(0,±1)` on González;
`f(0)=1 ≠ 49`, so pasted `(0,±7)` / six-point lists fail.
Genus formula `1+42/12−2/4−0/3−4/2 = 2` is a numeral, not a
Mathlib `genus`. Jacobian rank 0 / Chabauty /
`X0_26_Q_eq_known` / `J0_26_rank0` / `no_cyclic_26_isogeny_Q`
stay `def Prop`. No `sorry`.

No `axiom kenku_*`. Glue `full2 + 13 ⇒ 26-isogeny`,
`X0_26_model`, `X0_26_Q_points_cusps_only` / `_finite`,
Kenku completeness, and `mazur_irreducible_13_via_X0_26` stay
`def Prop`. Gaps 2–4 (Tate `I₂₉`, Ribet, Serre) stay `def Prop`.

## Barrier lock (`953a174` → `9030063` → `adb1d41`)

Closing `B ≥ B0` is four Mathlib gaps, not an `a₇=−4` slice
kill. Honest status on this branch:

1. **Mazur / `X₀(13)` / `X₀(26)`.** `X₀(13)` genus 0: Fricke
   `j(t)=(t²+5t+13)f³/t` has both remaining cusps onto `𝔽₂₉ˣ`
   (`v(t)=26k` and `v(t)=−2k`), so a unit scan cannot close
   Mazur (`1d28dc1`). `f` roots `7,9` mod `29`; fourth powers
   `{0,1,7,16,20,23,24,25}`; `c₄` coefficient `1`. Frey cubic
   splits at `0,A⁴,−B⁴` (`adb1d41`). LMFDB `26.42.2.a.1` /
   González model and `(0,±1)` are theorems; Kenku emptiness of
   non-cuspidal `X₀(26)(ℚ)` stays `def Prop`.
2. **Tate `I₂₉`.** Numerics `v₂₉(c₄)=0`, `v₂₉(Δ)=26k` are
   theorems. `Padic.valuation (Δ : ℚ_[29]) = 26 v₂₉(C)` is now
   a theorem; a unit of that valuation exists (`Δ` itself).
   Truncated `j(q)=q⁻¹+744+196884q` has `v=−v(q)` when `v(q)>0`;
   Frey `v(j⁻¹)=26k=v(Δ)`. Uniformization `E(ℚ̄_p) ≅ ℚ̄_pˣ / q^ℤ`
   and `inertia_trivial_mod13` stay `def Prop`. This is the only
   gap that does not need Wiles; it needs a Mathlib Tate-curve
   module (Loeffler / Vonk direction).
3. **Ribet `928→32`.** Stays `def Prop`. Needs Wiles + BCDT
   modularity of the semistable Frey curve and Ribet
   level-lowering after unramified `I₂₉`. Abstract Ribet
   (modular `E`, `13 ∣ v_p(Δ)`, trivial inertia ⇒ level
   `N_E / p`) has no Wiles in the **statement**; Mathlib still
   cannot inhabit it. Displayed numerals: `928 / 29 = 32`,
   `928 ≠ 32`, `29 ∤ 32`; `level_after_ribet_29 = 32` when
   `29 ∤ AB` and `928` when `29 ∣ AB`. That is not Néron `N_E`
   and not `ρ_E ≅ ρ_{E'}`. `Ribet_level_lowering_abstract` /
   `level_Frey_eq_32_needs_Wiles` stay `def Prop`. Primes in
   `A` need not drop (`13 ∤ 8`).
4. **Serre.** `48 < 2184` is a numeral theorem (`48 ≠ 2184`).
   `2²+3²=13` and split-Cartan count `2(13−1)²=288` with
   `288/48=6` are theorems. `y²=x³−x` has `j=1728` but is
   **not** LMFDB `32.a1` (`y²=x³+4x`). The Galois isomorphism
   `ρ_Frey ≅ ρ_{32a1}` and `card(im ρ_{32a1,13}) ≤ 48` stay
   `def Prop`.

`BealTrueV25` still has **one** axiom,
`darmon_merel_4413_axiom`. The four gaps are `def Prop` on
`BealMatveevBealV25B0Search`, not extra axioms. `main` stays
`6247c63` (axiom-free Matveev glob except that existing TrueV25
axiom). LLL `e5a95f5` (`C1' ≤ 8` impossible) is independent.
v25 is not minted.

## `ℚ_[29]` valuation scaffold (not Tate uniformization)

Root `Tate_I29_Inertia.lean` now inhabits Mathlib’s field
`ℚ_[p]` on the displayed discriminant:

- `Padic.valuation (n : ℚ_[29]) = padicValNat 29 n` (`n ≠ 0`)
- `Padic.valuation (Δ : ℚ_[29]) = 26 v₂₉(C)` on a solution
  with `29 ∤ AB`
- `13 ∣ Padic.valuation Δ`
- `∃ q : (ℚ_[29])ˣ, v(q) = v(Δ)` — take `q = Δ`

That last fact is **not** the Tate parameter. The truncated
modular expansion `j(q)=q⁻¹+744+196884 q` now has
`v(j(q))=−v(q)` whenever `v(q)>0`, and Frey `j⁻¹` has
`v(j⁻¹)=26k=v(Δ)` (`Tate_q_lead`). Identifying `j⁻¹` with the
Tate parameter of the displayed curve is still missing.
`Tate_q` / `Tate_uniformization` / `inertia_via_cyclo` stay
`def Prop`. No new axiom.

## `J₀(26)` BSD quotients (not the 143a1 Kolyvagin template)

The BSD template repos
`birch-swinnerton-dyer-143a1` and `Birch-and-Swinnerton-Dyer`
are a **rank-1** curve: `ε = −1` forces `L(E,1) = 0`, and the
inhabited Heegner / rational point is `(4,6)` / `(2,0)` on
`y²+y = x³−x²−x−2`. Grep for `Kolyvagin` / `Heegner` / `L(E,1)`
finds **no** `26a1` / `26b1`. Copying `L(E,1)=0` would be the
wrong sign for Jacobian rank 0.

Cremona `26a1` (LMFDB `26.a2`, **not** modular-curve
`26.42.2.a.1`): `[1,0,1,-5,-8]`, `Δ = -17576`, torsion `ℤ/3ℤ`.
BSD quotient `∏c_p / |tors|² = 3/9 = 1/3 ≠ 0`. Affine point
`(4,4)` lies on the model (height 0, not a Heegner point).

Cremona `26b1` (LMFDB `26.b2`): `[1,-1,1,-3,3]`, `Δ = -1664`,
torsion `ℤ/7ℤ`. Quotient `7/49 = 1/7 ≠ 0`. Affine point
`(1,0)` lies on the model. `3·7 = 21` is the Bruin–Najman
torsion-order numeral, not `J₀(26)(ℚ) ≅ ℤ/21ℤ`.

`L(E,1)` itself is a period times that rational. Mathlib 4.12
has no `EllipticLFunction`. Kolyvagin 1988 for analytic rank 0,
`J₀(26) ∼ 26a1 × 26b1`, and `J0_26_rank0` stay `def Prop`.

Root `X0_26_Full2Torsion.lean` now also records the 2-descent
**skeleton** (scan: no Mathlib `mwrank` / `SelmerGroup`; Sage
`certified_mwrank = 0` lives in
`sagemath/j0_26_decomp_foundation.sage`; PARI `|Sel₂|=1` lives
in `scripts/verify_descent_26.py`). Inhabited: `|Sel₂|=1` with
`2^0 = 1`, torsion *Nats* `3` and `7` (not a `torsionOrder`
field, not JSON `torsion: 2`), affine `(4,4)` / `(1,0)`,
`3·7=21`. `J0_26_rank0_via_mwrank`, Bruin–Najman
`J0_26_Q_tors_21`, and `mwrank_skeleton_complete` stay
`def Prop`. No `sorry`.

Root `TwoDescent_26a1_26.lean` relocates the lake-package
kernel (`BealLevel26Foundations.Descent.TwoDescent_26a1_26`
/ `Selmer_26`). Inhabited: PARI `|Sel₂|=1` (`Sel2_card_*`),
Sage `certified_mwrank` *display* `0`, torsion-order Nats
`3`/`7` (JSON `torsion: 2` is wrong), `2⁰=1`, `3·7=21`,
and `Sel2_rank0_implies_rank0_*` which is `1=1 → 0=0` on
those Nats. `RankZero_*_from_Selmer` / `Sha2_*_trivial` are
`1=1`, not Sha[2] and not Mordell–Weil. Jacobian rank 0
(`J0_26_rank0`, `J0_26_rank0_via_mwrank`) stays `def Prop`
on `X0_26_Full2Torsion`. No `BealTrueV25/` subdirectory
(conflicts with root `BealTrueV25.lean`). No Wiles. No
L-function. No new axiom.

Root `BSD_MordellWeil.lean` re-exports Mathlib’s
`WeierstrassCurve.Affine.Point` `AddCommGroup` as
`MordellWeilGroup` and proves `add_comm`. Pasted
`IsRankZero := Subsingleton` is **only the identity**, not
MW rank 0: affine `Point`s `(4,4)` on `26a1` and `(1,0)` on
`26b1` are not `0`, so `¬ IsRankZero` on both models.
`MW_rank_zero` (“every point is torsion”) and
`BSD_rank_statement` (analytic rank = algebraic rank) stay
`def Prop`. Not BSD. Not `J0_26_rank0`. No external-tower
namespace. No new axiom. Status note:
`docs/X0_26_SECTION_8994d38.md`.

## What this tree does not claim

- No `sorry`, no `True := trivial`, no fake `False.elim`.
- No new axiom on `BealMatveevBealV25B0Search`.
- No file under `Beal/Matveev/` for any of these root modules
  (that glob is the axiom-free Matveev surface on `main`).
- `C1_floor = 143186215390`, `B0_nat = 1000000` locked.
- Concept DOI `10.5281/zenodo.22379293`.
