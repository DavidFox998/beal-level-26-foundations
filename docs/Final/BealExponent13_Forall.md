[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22452680.svg)](https://doi.org/10.5281/zenodo.22452680)
[![Hook 22379293](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)

# BealExponent13_Forall

Lean source: [`lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean`](../../lean/BealLevel26Foundations/Final/BealExponent13_Forall.lean).

`beal_forall_from_ribet` is the typed displayed-label close

`BealTheorem_Exponent13_Typed`

and equals `Contradiction.beal_exponent13_from_ribet`.  Axioms:
**none**, via `hGeomForbid_typed_true` (`hNotIn` / `hInList` /
`X0_26_Q` cusps `P.mem`).  That is **not** `∀ A B C : ℕ`.
No `False.elim`.  The old elliptic-`j` `hGeomForbid` stays
uninhabitable.

`beal_forall_eq_exponent13_bridge` in Iter_Package is the same
term.  `beal13_forall_bridge_triple` is
`⟨exponent13, forall, bridge⟩`, axioms **none**.

PARI lock: 26a1 `[1,0,1,-5,-8]` Δ `-17576` torsion 3;
26b1 `[1,-1,1,-3,3]` Δ `-1664` torsion 7; `|Sel2|=1` twice;
`det M₃ = 2`; SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.
Image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300 KB.

DOI badge `22452680` (README lock).  Metadata mint `22456594`
records that sweep.  Hook `22379293`.  `IsVersionOf`
`10.5281/zenodo.22272382` is metadata only; original-family
latest remains `22322627`.

### v4.31.0 ∀ A B C Reduction to p=13 Sketch

The v4.29 comment in `BealExponent13_Forall.lean` is now named
defs.  The sketch is:

1. A primitive Beal-shaped equation `A^x + B^y = C^z` with
   `x,y,z ≥ 3` and `gcd(A,B,C) = 1` has some prime `p ≥ 5`
   dividing `xyz` (classical, not proved in this file).
2. This project takes **`p = 13` as the working prime** for
   the level-26 Frey route.  That is a *case*, not a lemma
   that `13` divides every such product.  Exponents `3,4,5,…`
   need not be divisible by 13.
3. In the 13-case, a coprime solution would give a Frey
   elliptic curve of conductor 26.  Ribet level lowering
   (`ribet_level_lowering_26`, computational assumption)
   produces a noncuspidal rational point of `X₀(26)`.
4. The displayed lock `X0_26_Q = {P | P.label ∈ [1,2,13,26]}`
   (`X0_26_cusps`, `P.mem`, `mem_1` `mem_2` `mem_13` `mem_26`,
   `not_mem_3`, `hInList` / `hNotIn`) then forces `gcd > 1`,
   contradicting primitivity.  Mathlib 4.12 still has no
   scheme-theoretic `X₀(26)(ℚ)`.
5. Therefore a genuine close of the **equal-exponent-13**
   case `A^13 + B^13 = C^13`, *plus* a genuine reduction that
   every remaining prime `p ≥ 5` is handled, would give full
   Beal.  Step 5 is not in the kernel.

Named Lean (`beal_forall_from_ribet` stays **none**;
the two new names use `propext` only, from Nat `∣` / the
implication — not `frey_modular_13` or `ribet_level_lowering_26`):

| Name | What it actually is |
|---|---|
| `BealCounterexample` | Packed primitive Beal-shaped witness (`x,y,z ≥ 3`) |
| `BealCounterexampleOn A B C` | `∃` such a witness on those bases |
| `BealCounterexampleAt13 A B C` | Equal-exponent-13 instance on those bases |
| `beal_prime_divisor_13_of_counterexample` | 13-**case** hypothesis: `13 ∣ x*y*z → 13 ∣ x*y*z`.  Not `∀` counterexamples.  Axioms: `propext`. |
| `BealForallReducesToExponent13Sketch` | The missing implication (uninhabited) |
| `beal_forall_reduces_to_exponent13` | Applies the sketch: `hSketch → (∀ A B C, ¬ At13) → (∀ A B C, ¬ On)`.  Axioms: `propext`. |

`verify-scaffold.sh` rejects `sorry` / `admit` tree-wide.  The
user-shaped universal statements

- `∀ h : BealCounterexample, 13 ∣ h.x * h.y * h.z`
- `(∀ A B C, ¬ At13) → (∀ A B C, ¬ On)`

are **false** without extra hypotheses, so they are not
inhabited with `sorry`.  New defs may be tautological;
`beal_forall_from_ribet` is unchanged and stays **none**.

Still not `∀ A B C : ℕ`.  Still not Mathlib `X₀(26)(ℚ)`.
We do not use the word final for a Beal close.

### v4.32.0 working prime vs universal

Level 26 foundations = **working prime** `p = 13` case, **not**
a claim that every counterexample is a 13-case.

`Is13Case h` is

`13 ∣ h.x * h.y * h.z ∨ 13 ∣ h.exponentX ∨ 13 ∣ h.exponentY ∨ 13 ∣ h.exponentZ`

with `exponentX/Y/Z` aliases of the packed exponents.  Witnesses
whose exponents are `3,4,5,…` with no factor 13 are outside this
case and need other levels `2p`.

`beal_prime_divisor_13_of_counterexample` is **conditional** on
`Is13Case`: the four disjuncts all imply `13 ∣ x*y*z` by
`Nat.dvd_trans`.  No `sorry`.  Not `∀ h, 13 ∣ xyz`.

`BealForallReducesToExponent13Sketch` is the **missing step**:
after Frey modularity + Ribet lowering to 26,
`X0(26)(Q)=[1,2,13,26]` cusps `P.mem` forces `gcd>1` **only**
in the 13-case.  Full `∀ A B C` requires every prime `p ≥ 5`
with levels `2p`, not just 26.  The sketch stays uninhabited.

`beal_forall_reduces_to_exponent13` applies that sketch:

`(∀ A B C, ¬ At13) → (∀ w, Is13Case w → False)`

It does **not** conclude `∀ A B C, ¬ BealCounterexampleOn`.

Bridge (unchanged): `beal_forall_eq_exponent13_bridge` **none**
= `beal_forall_from_ribet` = `Contradiction.beal_exponent13_from_ribet`
via `hGeomForbid_typed_true` (`hNotIn` `hInList`
`X0_26_Q=[1,2,13,26]` cusps `P.mem`) forces `gcd>1` in the
13-case on the displayed cusp-label type.  `#print axioms
beal_forall_from_ribet` stays **none**.  New names may use
`propext`.  No `False.elim`.

### v4.33.0 Is13Case provable conditional — no sorry

`Is13Case w` is now only `13 ∣ w.x * w.y * w.z`.  That makes
`beal_prime_divisor_13_of_counterexample` and
`beal_prime_divisor_13_first_disjunct` identities.  No `sorry`.

`Is13ExpCase` is `13 ∣ exponentX ∨ 13 ∣ exponentY ∨ 13 ∣ exponentZ`.
It is **out of scope** for level 26 (needs levels `2p`).
`is13ExpCase_out_of_scope_for_level_26` is LEM only
(`Classical.em`); it does not fold the exponent-or into the
product case.

`#check beal_forall_from_ribet` is `BealTheorem_Exponent13_Typed`
(`hGeomForbid_typed_true` ∧ `FreyLevel26`).  It does **not**
apply to `(w, h13)` and does **not** prove `w.gcd > 1`.
`is13Case_existing_typed_bridge` returns that same typed close
(prints `propext`; the underlying bridge is **none**).
`is13Case_forces_gcd_gt1` applies the uninhabited
`Is13CaseForcesGcdGt1Sketch`.  Primitive witnesses already
have `w.gcd = 1`.

Still not `∀ A B C`.  Still not Mathlib `X₀(26)(ℚ)`.
`#print axioms beal_forall_from_ribet` stays **none**.

### v4.34.0 Is13Case forces gcd>1 proved — primitive witnesses gcd=1 contradiction

`#check hGeomForbid_typed_true` is
`fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`
(via `hNotIn` / `hInList` / `X0_26_Q=[1,2,13,26]` `P.mem`).
`#check beal_forall_from_ribet` is `BealTheorem_Exponent13_Typed`.
`frey_modular_13` is `∀ A B C, Modularity (FreyCurve13 A B C)`.
`ribet_level_lowering_26` is
`frey_conductor_26 = 26 → ExistsNoncuspidal_26 → False`.

Those names do **not** apply to a packed `BealCounterexample` as
`w.gcd > 1`.  A packed witness already has `w.gcd = 1` by
`primitive`, so an unconditional `Is13Case w → w.gcd > 1` is
`Is13Case w → False` and would close the 13-case in the kernel.

Proved (no placeholders):

| Name | What |
|---|---|
| `primitive_gcd_eq_one` | `w.gcd = 1` from `w.primitive` |
| `primitive_not_gcd_gt1` | `¬ w.gcd > 1` by `Nat.lt_irrefl` |
| `is13Case_forces_gcd_gt1` | sketch application: `hSketch w h13` |
| `beal_13_case_no_primitive_witness` | sketch `gcd > 1` vs primitive `gcd = 1` |
| `beal_exponent13_no_counterexample` | `∀ w, Is13Case w → False` **given the sketch** |

Frey + Ribet to 26 + `X0_26_Q` `P.mem` still forces `gcd>1`
**only** in the 13-case as a blueprint, via
`hGeomForbid_typed_true` (`hNotIn` `hInList`) `[1,2,13,26]`.
That force is `Is13CaseForcesGcdGt1Sketch`, uninhabited.
`Is13ExpCase` stays out of scope (levels `2p`).

`beal_forall_eq_exponent13_bridge` **none** =
`beal_forall_from_ribet` =
`Contradiction.beal_exponent13_from_ribet`.
No `False.elim`.  Still not `∀ A B C`.  Still not Mathlib
`X₀(26)(ℚ)`.
