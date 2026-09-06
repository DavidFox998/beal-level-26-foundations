[![DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22452680.svg)](https://doi.org/10.5281/zenodo.22452680)
[![Hook 22379293](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
Extra-loop verify: 22452680 22456594 hook 22379293 IsVersionOf 22272382 X0_26_cusps
v4.35.0 `#check is13CaseForcesGcdGt1Sketch_inhabited` is `BealTheorem_Exponent13_Typed` none, `Is13CaseForcesGcdGt1Sketch` still uninhabited, still not `∀ A B C`.
v4.40.0 `FreyCurve13_of_BealCounterexampleBases` is Weierstrass `freyCurve ↑A ↑B 13 13`, not a noncuspidal `X₀(26)` point. `ExistsNoncuspidal_26_of_Is13CaseSketch` still uninhabited, still not `∀ A B C`.
v4.41.0 `ribet_produces_noncuspidal_of_weierstrass` / `weierstrass_modularity_gives_ExistsNoncuspidal_sketch` stay uninhabited. `WeierstrassCurve` is not `DisplayedX026CuspPoint`, still not `∀ A B C`.
v4.42.0 `WeierstrassModularity (FreyCurve13_of_BealCounterexampleBases w)` is a valid type; Ribet sketches stay uninhabited, still not `∀ A B C`.
v4.43.0 Ribet sketches take `WeierstrassModularity` and stay uninhabited. `WeierstrassCurve` is not `DisplayedX026CuspPoint`, still not `∀ A B C`.
v4.44.0 `X0_26_Q_Point` is `Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26` started; Mathlib 4.12 has no `X₀(26)(ℚ)`. Ribet sketches stay uninhabited, still not `∀ A B C`.
v4.45.0 `X0_26_Q_Point_to_ExistsNoncuspidal` is `Nonempty → ExistsNoncuspidal_26` uninhabited. Empty inductive, still not `∀ A B C`.
v4.46.0 real `X₀(26)(ℚ)` has 26a1/26b1 so cusp→False is false; contradiction is `S₂(Γ₀(2))=0` no newform. Still not `∀ A B C`.
v4.47.0 Tate conductor from `Is13Case` (`13 ∣ A*B*C`) is an uninhabited sketch; `frey_conductor_26_rfl` stays `rfl`. Still not `∀ A B C`.
v4.48.0 `Is13CaseForcesFalseSketchViaLevel2` is `∀ w, Is13Case w → False` uninhabited (needs Tate+Ribet); valid type, still not `∀ A B C`.
v4.49.0 `beal_forall_from_Is13Case_sketch` is `∀ A B C` uninhabited (needs Tate+Ribet+GcdGt1); still not `∀ A B C`.
v4.50.0 `13 ∣ A*B*C` splits to one factor (`Is13Case_prime_dvd` none); `⟨13,2,1⟩` has gcd 1, so GcdGt1 stays uninhabited. Still not `∀ A B C`.
v4.51.0 `triple_13_2_1` gcd=1 by `rfl`; bases not primitive-by-definition; GcdGt1 stays uninhabited. Still not `∀ A B C`.
v4.52.0 `IsPrimitive` subtype; ∃ primitive Is13Case gcd=1 vs ∀ gcd>1 false. Still not `∀ A B C`.
v4.53.0 Path1 gcd>1 false; Path2 only honest `Is13Case → False` via level 2. Still not `∀ A B C`.
v4.54.0 conditional `hTate+hRibet+hComp+hΔ → Beal ∀`; does not inhabit unconditional False. Still not `∀ A B C`.
v4.55.0 explicit Δ≠0; propext-only Beal ∀ via hTate+hRibet+hWeierstrass. Still not `∀ A B C`.
v4.56.0 Mathlib gaps Tate/Ribet/Modularity/X0; propext-only Beal ∀ is ceiling. Still not `∀ A B C`.
v4.57.0 Phase5 X0(26)(Q) honest scaffold; real-points String list; not Mazur. Still not `∀ A B C`.
v4.58.0 TaylorWilesScaffold R=T|Hecke|Deformation; ceiling propext-only. Still not `∀ A B C`.
v4.59.0 About catch-up 22551298; ROADMAP v5 without Mathlib. Still not `∀ A B C`.
v5.0.0 Tate table inhabit; hTate fillable; not Mathlib Tate. Still not `∀ A B C`.
v5.1.0 Ribet table inhabit; rho_bar+Deformation+26/13=2; not Mathlib Ribet. Still not `∀ A B C`.
v5.2.0 R=T table inhabit; Hecke token+Equiv; hWeierstrass from R=T; not Mathlib R=T. Still not `∀ A B C`.

### v5.2.0-iter-taylor-wiles-R=T-inhabit-no-mathlib

Lock `HeckeAlgebra_26` as an inhabited token (`Nonempty`,
**none**) and make `R_T_scaffold_inhabited` the displayed
`DeformationRing ≃ HeckeAlgebra_26` Equiv (**none**) plus
`modularity_lifting_of_R_T_inhabited` and
`TW_primes_Q_n_inhabited` (**propext**).  `hWeierstrass`
is `WeierstrassModularity_of_pack_from_R_T` from `R = T`,
**not** via existing `frey_modular_13`.  Ceiling
`is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table`
plugs inhabited `hTate` + displayed `hRibet` (`26/13=2`)
+ inhabited `hWeierstrass_from_R_T` → Beal `∀` conditional
**propext only**.  It still needs original
`ExistsNewformLevel2` (`0 ≠ 0`), kept uninhabited until
v5.3.0 Beal `∀` IN KERNEL.

Same honesty as `tate_table_conductor = 2*13` **none**
and `s2_gamma0_2_dim = 0`.  `R_T_algorithm` /
`TaylorWilesPatchingWitness` stay uninhabited.  Tate
DONE v5.0.0.  Ribet displayed DONE v5.1.0.  `R = T`
displayed DONE v5.2.0.  Path 1 false (`⟨13, 2, 1⟩`).
Path 2 only honest.  No `False.elim`.  Still not
`∀ A B C` unconditionally until v5.3.0.  We finish
displayed `R = T` without Mathlib.

### v5.1.0-iter-ribet-26-to-2-inhabit-no-mathlib

Lock `DeformationRing_rho_bar_E13` and `rho_bar_Frey_13`
as displayed tokens and make
`ribet_produces_newform_level2_inhabited`.  We finish the
displayed Ribet table for them; no Mathlib Galois reps.

`rho_bar_Frey_13_inhabited` is the displayed `ρ̄_{E,13}`
token for `FreyCurve13 w = freyCurve ↑w.A ↑w.B 13 13`,
`Y² = X(X − A¹³)(X + B¹³)`,
`Δ = 16*(A¹³)²*(B¹³)²*(A¹³+B¹³)²`
(`frey_Delta13_ne_0_of_pos`, **propext**).  Conditions
are the displayed list: irreducible (Mazur), semistable
at 2, finite flat at 13, minimal, det cyclotomic mod 13.
**propext**.  `DeformationRing_rho_bar_E13_inhabited` is
the same token as `Nonempty DeformationRing` (**none**).
`ribet_produces_newform_level2_inhabited` is
`Δ ≠ 0 → WeierstrassModularity (pack w) → conductor = 2*13
→ ribet_level_26_div_13 = 2` via
`tate_table_conductor = 2*13` **none** +
`frey_conductor_26_rfl` **none** + the dim-0
`notExistsNewformLevel2` **none** as the *anchor that
would give False after real Ribet*.  Conclusion is the
label `26 / 13 = 2`, not `ExistsNewformLevel2` (`0 ≠ 0`).
**propext**.  The original
`ribet_produces_newform_level2_of_weierstrass_modularity`
stays uninhabited.

v5.0.0 Tate **DONE**.  v5.1.0 displayed Ribet **DONE**.
`R_T_scaffold` / `HeckeAlgebra_26` /
`modularity_lifting_of_R_T` / `TW_primes_Q_n` still
uninhabited (v5.2.0).  `X₀(26)(ℚ)` empty inductive;
real curve has `26a1` Δ `-17576` and `26b1` Δ `-1664`.
Path 1 false (`⟨13, 2, 1⟩`).  Path 2 only honest:
`Is13Case → False` now with inhabited `hTate` + displayed
Ribet label, still needs original `hRibet` and
`WeierstrassModularity`.  Ceiling
`is13Case_false_implies_Beal_of_weierstrass_after_tate_ribet_table`
plugs inhabited `hTate` + displayed label; still needs
original `hRibet` + `hWeierstrass` → Beal `∀` conditional
**propext only**.  Still not `∀ A B C` unconditionally
until `R = T` and real Ribet.  No `False.elim`.

### v5.0.0-iter-tate-conductor-26-inhabit-no-mathlib

Begin v5.  We do not need Mathlib; we finish the displayed
Tate table for them.  Phase 1 conductor label is inhabited.

`tate_table_conductor = 2 * 13` with `tate_f_2 = 1`,
`tate_f_13 = 1`, multiplicative at 2 and 13 (**none**).
`tate_conductor_26_of_Is13Case_proof` is
`Is13Case ∧ 0 < A ∧ 0 < B → Δ ≠ 0 ∧ table = 2*13`
via `frey_Delta13_ne_0_of_pos`
(`Δ = 16*(A¹³)²*(B¹³)²*(A¹³+B¹³)²`, **propext** +
`Classical.choice` + `Quot.sound`).
`frey_conductor_26_of_Is13Case_inhabited` fills `hTate`
(**propext**).  `frey_conductor_26_rfl` stays **none**.
`tate_algorithm_of_Is13Case` stays uninhabited (no
Mathlib `∏ p^{f_p}`).  Same honesty as
`s2_gamma0_2_dim = 0`.  `Is13Case` does not imply
`2 ∣ A*B*C`.

Phases 2–5 stay scaffold: Ribet uninhabited, `R = T`
uninhabited, `X₀(26)(ℚ)` empty inductive.  Ceiling still
conditional Beal `∀` propext-only, but `hTate` is now
fillable (`is13Case_false_implies_Beal_of_ribet_after_tate_table`
still needs `hRibet`).  Path 1 false.  Path 2 only honest.
No `False.elim`.  Still not `∀ A B C` unconditionally.
Still not Mathlib `X₀(26)(ℚ)` + Ribet + Tate + Taylor–Wiles.

### v4.59.0-iter-about-roadmap-catchup-before-v5

About catch-up `22551051 → 22551298`.  Hook `22379293`.
`IsVersionOf` `22272382` metadata only.  Original-family
latest remains `22322627`.  Chain
`… → 22550229 → 22550771 → 22551051 → 22551298`.
Previous HEAD `4c027c3` / `v4.58.0-iter-taylor-wiles-scaffold`
now records its mint.

Still not `∀ A B C` unconditionally.  Still not Mathlib
`X₀(26)(ℚ)` + Ribet + Tate + Taylor–Wiles.  No
`False.elim`.  Conditional Beal `∀` propext-only is still
the ceiling.

`docs/Final/ROADMAP.md` locks v5 **without** waiting for
Mathlib — we finish it for them:

* v5.0.0 Tate conductor 26 **INHABIT**
  (`frey_conductor_26_of_Is13Case`)
* v5.1.0 Ribet `26 → 2` **INHABIT**
* v5.2.0 Taylor–Wiles `R = T` **INHABIT**
* v5.3.0 Beal `∀` **IN KERNEL**

Those slices are not done.  10 modules stay as in v4.58.0.

### v4.58.0-iter-taylor-wiles-scaffold

Lock `TaylorWilesScaffold.md` / `Chain.TaylorWilesScaffold` (10th
module) with the table `R = T` | Hecke | Deformation | what
Mathlib 4.12 lacks.  Pin Lean 4.12.0 + Mathlib v4.12.0.
`WeierstrassModularity c` is
`∃ w, c = pack w ∧ Modularity (FreyCurve13 w)`, a valid type.
`WeierstrassModularity_of_pack` is existing `frey_modular_13`
(**propext** + that assumption).  Not Wiles–Taylor / BCDT.
No new axiom.

* `R_T_scaffold` : `Nonempty (DeformationRing ≃ HeckeAlgebra_26)`
  uninhabited Prop.  Mathlib lacks deformation rings, `R = T`,
  universal / minimal deformations.  No empty-elim.
* `HeckeAlgebra_26` empty Type scaffold (**none**).  Mathlib
  lacks `T_N`, `T_p`, diamond, Gorenstein, complete intersection.
* `DeformationRing_rho_bar_E13` uninhabited.  Mathlib lacks
  Galois deformation theory and
  `ρ̄_{E,13} : G_ℚ → GL₂(𝔽₁₃)` (irreducible, finite flat at
  13, minimal at 2).
* `rho_bar_Frey_13` uninhabited.  Mathlib lacks the residual
  Frey representation mod 13 (semistable at 2, finite at 13,
  Mazur irreducibility).
* `modularity_lifting_of_R_T` uninhabited.  Mathlib lacks
  Taylor–Wiles patching, Diamond criterion, Wiles numerical
  criterion.  Not inhabited by `WeierstrassModularity_of_pack`.
* `TW_primes_Q_n` uninhabited.  Mathlib lacks auxiliary primes
  `Q_n`, `|Q_n| = r`, `q ≡ 1 [MOD 13^n]`, distinct Frobenius
  eigenvalues.
* Ceiling stays
  `is13Case_false_implies_Beal_of_tate_ribet_disc_propext_only`
  `hTate → hRibet → hWeierstrass → hComp + hΔ → Beal ∀`
  (**propext only**).  Local `Is13Case → False` via Path 2.
  Does **not** inhabit unconditional
  `Is13CaseForcesFalseSketchViaLevel2`.  Needs `R = T` +
  Ribet + Tate for unconditional Beal `∀`.

Phases 1–5 unchanged.  Path 1 false (`⟨13,2,1⟩`).  Path 2
only honest `Is13Case → False`.  No `False.elim`.
Still not `∀ A B C` unconditionally.  Still not Mathlib
`X₀(26)(ℚ)` + Ribet + Tate + Taylor–Wiles.

### v4.57.0-iter-phase5-X0-26-Q-honest-scaffold

Phase 5 build-out of the `X₀(26)(ℚ)` honest scaffold until
Taylor–Wiles / BCDT.  `X0_26_Q_Point` is still
`Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26`, an empty
inductive, **not** the real curve.  Real `X₀(26)(ℚ)` has
four cusps `1,2,13,26` plus `26a1` Δ `-17576` and `26b1`
Δ `-1664`.  `X0_26_Q_real_points` is a `List String`
reference (**none**).  `fourCuspsForallCuspPoints_of_P_mem`
is **none** on `DisplayedX026CuspPoint` (label
`∈ [1,2,13,26]`), not Mazur; `X0_26_Q_Point` has no
`.label`.  `notExistsNoncuspidal_26_proved` is **none**
via `hGeomForbid` label check, not Mazur.
`X0_26_Q_Point_to_ExistsNoncuspidal` and
`nonempty_X0_26_Q_Point_to_False` stay uninhabited (no
vacuous empty-elim).  `Chain.MathlibGaps` Phase 5 records
that Mathlib lacks `X₀(N)(ℚ)`.  Phases 1–4 and both Beal
wirings stay.  Ceiling remains propext-only Path 2.
No `False.elim`.  Still not `∀ A B C` unconditionally.
Still not Mathlib `X₀(26)(ℚ)` + Ribet + Tate.

### v4.56.0-iter-mathlib-gaps-what-mathlib-does-not-have

This pin is Lean 4.12.0 + Mathlib v4.12.0.
`Chain.MathlibGaps` records what Mathlib does not have:

* Tate conductor `N = 2*rad(ABC)`:
  `frey_conductor_26_of_Is13Case` uninhabited sketch;
  `fun _ => rfl` is the label, not Tate;
  `frey_conductor_26_rfl` **none** is the same label.
  Mathlib has Weierstrass Δ, not Tate `∏ p^{f_p}`.
* Modularity: `WeierstrassModularity_of_pack` is existing
  `frey_modular_13` (**propext** + that assumption), not
  Wiles–Taylor / BCDT.  Mathlib has no modularity
  predicate for elliptic curves over `ℚ`.
* Ribet `26/13=2`:
  `ribet_produces_newform_level2` uninhabited.  Mathlib
  has no residual Galois representation and no level
  lowering.
* `S₂(Γ₀(2))=0`: `notExistsNewformLevel2` **none** DONE
  (dim `0` anchor).
* `X₀(26)(ℚ)`: `X0_26_Q_Point` empty inductive scaffold,
  not the real curve.  Real curve has `26a1` Δ `-17576`
  and `26b1` Δ `-1664`, so `Nonempty → False` is false.
  `fourCuspsForallCuspPoints_of_P_mem` **none** is
  label `∈ [1,2,13,26]`, not Mazur.

Conditional Beal `∀` **propext only** is the ceiling:
`is13Case_false_implies_Beal_of_tate_ribet_disc_propext_only`
`hTate → hRibet → hWeierstrass → hComp + hΔ → Beal ∀`
builds a *local* `Is13Case → False` via
`is13Case_implies_False_of_tate_ribet_disc` and applies
`beal_forall_from_Is13Case_false_sketch`
`(∀ w, Is13Case → False) → Beal ∀` (Path 2, not Path 1).
Neither wiring inhabits unconditional
`Is13CaseForcesFalseSketchViaLevel2`.  No `False.elim`.
Still not `∀ A B C` unconditionally.  Still not Mathlib
`X₀(26)(ℚ)` + Ribet + Tate.

### v4.55.0-iter-delta-ne0-explicit-conditional-propext-only

explicit Δ≠0 from `FreyCurve13_of_BealCounterexampleBases`
`Y²=X(X−A¹³)(X+B¹³)` via `frey_Delta13_ne_0_of_pos`
`∀ w 0<A 0<B → Δ≠0`.  `#print axioms` is **propext** +
`Classical.choice` + `Quot.sound` (same as
`freyCurve_discriminant_ne_zero`), not none.  The
Weierstrass match is
`Δ = 16*(A¹³)²*(B¹³)²*(A¹³+B¹³)² ≠ 0` when `A,B>0`
(`Real/FreyWeierstrass`); the informal writeup
`16*(A¹³*B¹³*C¹³)²` is that formula when
`A¹³+B¹³=C¹³`.  Bases carry no equation, so `C` is not
in the displayed Δ.

NEW conditional wiring
`is13Case_false_implies_Beal_of_tate_ribet_disc` takes
`hTate` `frey_conductor_26_of_Is13Case` uninhabited +
`hRibet` `ribet_produces_newform_level2` `26/13=2`
uninhabited + Path 2 `hComp` + explicit `hΔ` Δ≠0 → Beal `∀`
`∀ A B C` without inhabiting unconditional `Is13Case→False`.
Axioms **propext** + existing `frey_modular_13`.

NEW propext-only variant
`is13Case_false_implies_Beal_of_tate_ribet_disc_propext_only`
takes `hTate` `hRibet` `hWeierstrassModularity`
`∀ w Δ≠0 → WeierstrassModularity (pack w)` as hypothesis
→ Beal `∀` conditional **propext only** (no existing
`frey_modular_13` axiom in its axioms).

`hDelta_of_pos` / `is13Case_false_implies_Beal_of_tate_ribet_disc_of_pos`
feed `frey_Delta13_ne_0_of_pos` when `0<A` and `0<B`.
Path1 false `⟨13,2,1⟩` `rfl` Path2 only honest
`Is13Case→False` valid type needs Tate+Ribet level2 none.

### v4.54.0-iter-Beal-from-Is13Case-False-conditional-wiring

Path1 false `Is13Case → gcd>1` refuted by `⟨13,2,1⟩` primitive
gcd=1 `rfl` `exists_primitive_Is13Case_gcd_1` **propext**
`forall_primitive_Is13Case_gcd_gt1_false` `¬∀ → gcd>1` via
`Nat.lt_irrefl` **propext** no choice one factor ≠ common,
Path2 only honest `Is13Case → False` via level2
`Is13CaseForcesFalseSketchViaLevel2` `∀ w Is13Case w→False`
valid type uninhabited needs Tate `frey_conductor_26_of_Is13Case`
+ Ribet `ribet_produces_newform_level2` `26/13=2`
+ `notExistsNewformLevel2` none via `S2(Gamma0(2))=0` dim0 → False,
NEW conditional wiring `is13Case_false_implies_Beal_of_tate_ribet_disc`
takes `hTate` `frey_conductor_26_of_Is13Case` uninhabited sketch
+ `hRibet` `ribet_produces_newform_level2_of_weierstrass_modularity`
uninhabited sketch + Path 2 `hComp` + Δ ≠ 0 → Beal `∀`
`∀ A B C m n p 2<m,n,p → A^m+B^n=C^p → gcd>1` without inhabiting
unconditional `Is13Case → False`, uses
`beal_forall_from_Is13Case_false_sketch`
`(∀ w Is13Case→False) → Beal ∀` valid type uses Path2 not Path1,
no `False.elim`.  Axioms **propext** + existing `frey_modular_13`.

### v4.53.0-iter-Is13Case-False-only-honest-path-to-Beal

document Path1 FALSE `Is13Case → gcd>1` refuted by `⟨13,2,1⟩`
primitive `Is13Case` gcd=1 `rfl` `exists_primitive_Is13Case_gcd_1`
**propext** `forall_primitive_Is13Case_gcd_gt1_false` `¬∀ → gcd>1`
via `Nat.lt_irrefl` **propext** no choice one factor ≠ common,
Path2 ONLY HONEST `Is13Case → False` via level2
`Is13CaseForcesFalseSketchViaLevel2` `∀ w Is13Case w→False`
valid type uninhabited needs Tate `frey_conductor_26_of_Is13Case`
+ Ribet `ribet_produces_newform_level2` `26/13=2`
+ `notExistsNewformLevel2` none via `S2(Gamma0(2))=0` dim0 → False,
`beal_forall_from_Is13Case_false_sketch`
`(∀ w Is13Case w→False) → Beal ∀` valid type composition uses
False via level2 not gcd>1 no `False.elim`.

### v4.52.0-iter-primitive-field-Is13Case-gcd-false-exists

add `IsPrimitive w := w.gcd=1`,
`BealPrimitiveCounterexampleBases := {w // IsPrimitive w}`,
`triple_13_2_1` `⟨13,2,1⟩` gcd=1 `rfl` dvd `13|13*2*1` decide
valid base primitive, `triple_13_2_1_primitive` `IsPrimitive`,
`exists_primitive_Is13Case_gcd_1` `∃ w` primitive `Is13Case w ∧ gcd=1`
`rfl` **propext**,
`forall_primitive_Is13Case_gcd_gt1_false`
`¬ (∀ w` primitive `Is13Case w → gcd>1)` false via counterexample,
so `Is13CaseForcesGcdGt1SketchPrimitive` stays uninhabited false
not just uninhabited, `Is13Case_prime_dvd`
`13|A*B*C → 13|A ∨ 13|B ∨ 13|C` via `Nat.Prime.dvd_mul`,
one factor ≠ common factor,
`Is13CaseForcesFalseSketchViaLevel2` `∀ w Is13Case w→False`
valid type uninhabited needs Tate+Ribet level 2 none.

### v4.51.0-iter-gcd-counterexample-rfl-primitive

explicit `⟨13,2,1⟩` gcd=1 by `rfl`, `13|13*2*1` by decide,
bases not primitive-by-definition, `BealCounterexampleBases`
does not require `gcd=1` so triple valid base, shows
`13|A*B*C` splits to one factor not common factor, so
`∀ w Is13Case w → w.gcd>1` false on bases,
`Is13CaseForcesGcdGt1Sketch` stays uninhabited honest,
`Is13CaseForcesFalseSketchViaLevel2` `∀ w Is13Case w→False`
valid type uninhabited needs Tate+Ribet level 2.

### v4.50.0-iter-Is13Case-gcd-gt1-why-uninhabited

`13 ∣ A*B*C` implies `13 ∣ A ∨ 13 ∣ B ∨ 13 ∣ C` via
`Nat.Prime.dvd_mul` (`Is13Case_prime_dvd`, **none**).
One factor 13 is not a common factor.
`Is13Case_gcd_counterexample` is `⟨13, 2, 1⟩`: `Is13Case`
and `gcd = 1`.  Bases are not primitive-by-definition, so
`∀ w, Is13Case w → w.gcd > 1` is false on bases.
`Is13CaseForcesGcdGt1Sketch` stays uninhabited.
The packed twin stays uninhabited (`gcd = 1` by `primitive`).
`Is13CaseForcesFalseSketchViaLevel2` stays
`∀ w, Is13Case w → False`, uninhabited (needs Tate + Ribet).

### v4.49.0-iter-Beal-13Case-to-Beal-forall-sketch

Beal forall sketch via the 13-case and level 2.
`Is13CaseForcesFalseSketchViaLevel2` is `∀ w, Is13Case w → False`,
valid type, uninhabited (needs Tate + Ribet).
`Is13CaseForcesGcdGt1Sketch` stays uninhabited
(`13 ∣ A*B*C` is not a common factor; packed twin has
`gcd = 1` by `primitive`).
`beal_forall_from_Is13Case_sketch` is
`∀ A B C m n p, 2 < m,n,p → A^m+B^n=C^p → gcd > 1`,
valid type, uninhabited.  The two 13-case sketches do not
imply Beal: other primes need levels `2p`.  No `False.elim`.
Real `X₀(26)(ℚ)` has `26a1` / `26b1`.  Still not `∀ A B C`.

### v4.48.0-iter-Is13Case-to-False-sketch-via-level-2

Wire `Is13Case` → `ExistsNewformLevel2` → `False` via Tate and
Ribet sketches.  Uninhabited, honest.

`Is13Case` (`13 ∣ A*B*C` on bases) plus Frey Δ ≠ 0 would give
conductor 26 via Tate.  That sketch stays uninhabited:
`fun _ => rfl` is the label, not Tate.
`frey_conductor_26_rfl` is `2 * 13` by `rfl` (**none**).
`WeierstrassModularity` is a valid bridge.
`ribet_produces_newform_level2_of_weierstrass_modularity` is
`∀ w, Δ ≠ 0 → WeierstrassModularity (pack w) →
frey_conductor_26 = 2 * 13 → ExistsNewformLevel2`,
uninhabited (needs Ribet `26 / 13 = 2`).
`notExistsNewformLevel2` is **none** via `S₂(Γ₀(2))` dim 0.
Composition `Is13CaseForcesFalseSketchViaLevel2` is
`∀ w, Is13Case w → False`, uninhabited (needs Tate + Ribet).
No `False.elim`.  This is the `beal_forall_from_ribet`
pre-image, not `∀ A B C`.

### v4.47.0-iter-tate-conductor-26-from-Is13Case

`Frey.FreyConductor26.Is13Case` is `13 ∣ A*B*C` on bases.
`frey_conductor_26_rfl` is `2 * 13` by `rfl` (**none**).
`frey_conductor_26_of_Is13Case` in that file is the
uninhabited Tate sketch: Mathlib 4.12 has no Tate algorithm.
Real `X₀(26)(ℚ)` has `26a1` / `26b1`.  The contradiction is
level 2, no newform.  Need Tate plus Ribet.

### v4.46.0-iter-level-2-no-newform

Real `X₀(26)(ℚ)` has points `26a1` (Δ `-17576`) and `26b1`
(Δ `-1664`), so `X0_26_Q_Point → False` is false.  The
four-cusp lock is displayed labels, not the real curve.
The contradiction is `S₂(Γ₀(2)) = 0`: no newform at level 2.
Conductor `26 = 2 * 13` is `rfl`, not Tate.  Need Tate plus
Ribet to reach level 2.  `notExistsNewformLevel2` is **none**
via displayed dimension `0`.
`ribet_produces_newform_level2_of_weierstrass_modularity`
stays uninhabited.

### v4.45.0-iter-X0-26-Q-point-to-ExistsNoncuspidal

`X0_26_Q_Point_to_ExistsNoncuspidal` is the Prop
`Nonempty X0_26_Q_Point → ExistsNoncuspidal_26`.
Uninhabited: `CyclicSubgroup` is an empty inductive
(Mathlib 4.12 has `EllipticCurve ℚ`, no `CyclicSubgroup E n`,
no modular-curve scheme).  Not a vacuous empty-elim close.
`weierstrass_modularity_gives_X0_26_Q_Point` stays
uninhabited.  Need Mathlib `X₀(26)(ℚ)` plus Ribet for
`ExistsNoncuspidal_26` → `False`.

### v4.44.0-iter-X0-26-Q-real-modular-curve

`X0_26_Q_Point` starts the intended real modular-curve
point: `Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26`.
Mathlib 4.12 has `EllipticCurve ℚ` (`a₁…a₆` plus unit Δ)
but no `CyclicSubgroup E n` and no `X₀(26)(ℚ)`, so the
second slot is an empty inductive.  The type is uninhabited.

`WeierstrassModularity` stays a valid type.
Ribet sketches still take the bridge and stay uninhabited.
`WeierstrassCurve Int` ≠ `DisplayedX026CuspPoint`
(label `∈ [1,2,13,26]`).  Need Mathlib `X₀(26)(ℚ)` plus
Ribet to get `ExistsNoncuspidal_26` → `False`.

### v4.43.0-iter-ribet-takes-weierstrass-bridge

`WeierstrassCurve Int` has `a₁…a₆`, not `.A`/`.B`/`.C`.
`WeierstrassModularity c` is `∃ w, c = pack w ∧
Modularity (FreyCurve13 w.A w.B w.C)`.
`WeierstrassModularity (FreyCurve13_of_BealCounterexampleBases w)`
is a valid type.  `WeierstrassModularity_of_pack` is
`frey_modular_13` (`propext` + that axiom).  Not Wiles--Taylor.
No new axiom.

`ribet_produces_noncuspidal_of_weierstrass` stays the displayed
`Modularity (FreyCurve13 A B C)` sketch.
`ribet_produces_noncuspidal_of_weierstrass_modularity` and
`weierstrass_modularity_gives_ExistsNoncuspidal_sketch` take the
bridge.  All three stay uninhabited:
`WeierstrassCurve` ≠ `DisplayedX026CuspPoint`.  Mathlib 4.12 has
no `X₀(26)(ℚ)` and no Ribet.  Inhabiting any plus
`notExistsNoncuspidal_26_proved` would be `False` (`rfl` conductor
label, not Tate).

[![Concept DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22272382.svg)](https://doi.org/10.5281/zenodo.22272382)
[![v4.0.9-fourCusps-forall DOI](https://zenodo.org/badge/DOI/10.5281/zenodo.22322627.svg)](https://doi.org/10.5281/zenodo.22322627)
[![CI](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml/badge.svg)](https://github.com/DavidFox998/beal-level-26-foundations/actions/workflows/main.yml)

### v4.28.0 X0(26)(Q) Cusps P-mem Locked — DOI 22452680

| Name | What |
|---|---|
| X0_26_Q | [1,2,13,26] rfl P.mem mem_1 mem_2 mem_13 mem_26 not_mem_3 hInList hNotIn for hGeomForbid |
| beal_forall_eq_exponent13_bridge | none = beal_forall_from_ribet = Contradiction.beal_exponent13_from_ribet BRIDGE none hGeomForbid_typed_true (hNotIn hInList) |
| beal13_forall_bridge_triple | none ⟨exponent13,forall,bridge⟩ |

DOI `22452680` findable records prior mint `22450737` hook `22379293` `IsVersionOf` `22272382` honest original latest `22322627`.

PARI lock: 26a1 Δ `-17576` 26b1 Δ `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260` image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.

# Beal Level 26 Foundations — Exponent 13 Full Package (Computational Boundary)

This repo: v4.30.0 metadata fix 22452680→22456594 + verify grep lock — see docs/BealExponent13_Iter_Package.md and docs/Chain/X0_26_Point.md

## v4.25.0 Beal13-Forall-Bridge Triple — Axiom-Free Cert

| Theorem | Axioms |
|---|---|
| beal_forall_eq_exponent13_bridge | none = beal_forall_from_ribet = Contradiction.beal_exponent13_from_ribet BRIDGE none hGeomForbid_typed_true |
| beal13_forall_bridge_triple | none ⟨beal_exponent13_from_ribet, beal_forall_from_ribet, beal_forall_eq_exponent13_bridge⟩ |
| beal13_forall_bridge_triple_none_check / typed_and_forall / certified_typed_and_forall | none |
| beal_forall_from_ribet / certified_from_forall / beal_exponent13_from_ribet | none hGeomForbid |
| contradiction_from_ribet | ribet_level_lowering_26 only |
| Contradiction.certified | frey_modular_13 + ribet_level_lowering_26 |

Formerly `final_bridge` / `final_package` / `final_package_none` — now `beal_forall_eq_exponent13_bridge` / `beal13_forall_bridge_triple` — says what it is: forall = exponent13 bridge triple none. `beal13_forall_bridge_triple_none_check` is the same triple (not `: True`; verify allows only `ribet_secured_by_certs` as `: True :=`). Legacy `final_*` aliases remain. Still not ∀ N. Still not a Mathlib X0(26)(Q) theorem. PARI lock: 26a1 `-17576` 26b1 `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`, image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.

## v4.18.0 Typed ∧ Forall Lock — Axiom-Free Cert

| Theorem | Axioms |
|---|---|
| typed_and_forall | none ⟨beal_exponent13_from_ribet, beal_forall_from_ribet⟩ |
| certified_typed_and_forall | none ⟨certified_from_forall, beal_forall_certified_from_ribet⟩ |
| beal_forall_from_ribet / beal_forall_certified_from_ribet / certified_from_forall | none |
| beal_exponent13_from_ribet / certified_from_ribet | none (hGeomForbid_typed_true via hNotIn hInList) |
| contradiction_from_ribet | ribet_level_lowering_26 only |
| BealExponent13_Contradiction.certified | frey_modular_13 + ribet_level_lowering_26 |

Typed ∧ Forall lock: both conjuncts are `BealTheorem_Exponent13_Typed` via axiom-free `hGeomForbid`. Not ∀ N. Still not a Mathlib X0(26)(Q) theorem. The only axioms are `frey_modular_13` and `ribet_level_lowering_26` (COMPUTATIONAL ASSUMPTION), secured by `certs/pari_x0_26_four_cusps.json`. Not `∀ ℕ`. No `False.elim`.

## Geometry: X₀(26) Level 26

![X0(26) Modular Curve - Genus 2 with 4 cusps and p=2 residue disks, M3=[[1,1],[0,2]] det=2, Abel-Jacobi to J0(26) rank 0](docs/images/modular_curve_x0_26_beal_level_26.webp)

*Figure: X₀(26) is genus 2 (double torus) with cusps 1,2,13,26. p=2 residue disks (blue) map via Abel-Jacobi to J₀(26), a 2-dim abelian surface rank 0. Formal immersion M₃=[[1,1],[0,2]], det=2≠0 proves each disk contains only its cusp — the Coleman integral vanishes on J₀(26)(ℚ) when rank 0.*

## PARI 2-Descent Certificates — X0(26) Four Cusps

![2-Descent for Level 26: 26a1 & 26b1 — Sel2=1 Sha[2]=0 J0(26)~26a1×26b1 det M3=2 fourCusps [1,2,13,26]](docs/images/2-descent-level-26-26a1-26b1.webp)

PARI 2-descent certificates for the Jacobian factors of \(J_0(26)\). Certified Weierstrass models are 26a1 `[1,0,1,-5,-8]` Δ `-17576` and 26b1 `[1,-1,1,-3,3]` Δ `-1664`. PARI reports `|Sel₂|=1` twice, `det M₃=2`, and Descent SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `FreyLevel26` is `2*13=26` (`rfl`). `hGeomForbid_typed_true` is proved by `hNotIn hInList` with no axioms. `ExistsNoncuspidal_26` is empty by `P.mem`. The illustration is a schematic of the 2-descent picture (real locus ≈ \(S^1\times S^1\), `Sel₂=1`, Sha[2]=0, \(J_0(26)\sim 26a1\times 26b1\), four cusps `[1,2,13,26]`); certified models and discriminants are the Descent ones, not any alternate Weierstrass equations drawn on the figure.

This repository is the foundations chamber for moving the level-26 Beal route
from an explicit conditional assembly toward a theorem whose remaining
mathematical bridges are constructed one by one. It is a deliberately smaller
repository: the conditional development stays in
[`DavidFox998/beal-conjecture`](https://github.com/DavidFox998/beal-conjecture).

The governing principle is the same as the parent project: a checked
calculation is evidence for exactly what it computes, while every missing
mathematical bridge is named instead of hidden behind an axiom.

**Current public surface:** tag
[`v4.30.0-iter-zenodo-22456594-metadata-fix`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.30.0-iter-zenodo-22456594-metadata-fix)
(prior
[`v4.29.0-iter-readme-X0-26-22452680-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.29.0-iter-readme-X0-26-22452680-locked)
(prior
[`v4.28.0-iter-zenodo-X0-26-cusps-metadata-mint`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.28.0-iter-zenodo-X0-26-cusps-metadata-mint)
(prior
[`v4.27.0-iter-X0-26-cusps-P-mem-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.27.0-iter-X0-26-cusps-P-mem-locked),
[`v4.25.0-iter-zenodo-triple-bridge-none-mint`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.25.0-iter-zenodo-triple-bridge-none-mint)
(prior
[`v4.24.0-iter-readme-final-package-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.24.0-iter-readme-final-package-locked),
[`v4.23.0-iter-package-final-bridge-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.23.0-iter-package-final-bridge-locked),
[`v4.22.0-iter-zenodo-parent-fix`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.22.0-iter-zenodo-parent-fix),
[`v4.21.0-iter-zenodo-mint`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.21.0-iter-zenodo-mint),
[`v4.20.0-iter-package-none-docs-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.20.0-iter-package-none-docs-locked),
[`v4.19.0-iter-readme-typed-forall-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.19.0-iter-readme-typed-forall-locked),
[`v4.18.0-iter-typed-forall-package-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.18.0-iter-typed-forall-package-locked),
[`v4.17.0-iter-forall-bridge-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.17.0-iter-forall-bridge-locked),
[`v4.16.0-iter-readme-about-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.16.0-iter-readme-about-locked),
[`v4.15.0-iter-typed-forall-bridge`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.15.0-iter-typed-forall-bridge),
[`v4.14.0-iter-citation-contradiction-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.14.0-iter-citation-contradiction-locked),
[`v4.13.1-iter-unstick`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.13.1-iter-unstick),
[`v4.13.0-iter-contradiction-start`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.13.0-iter-contradiction-start),
[`v4.12.0-iter-verify-plus`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.12.0-iter-verify-plus),
[`v4.10.0-iter-pari-locked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.10.0-iter-pari-locked),
[`v4.9.0-iter-no-True-X0`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.9.0-iter-no-True-X0),
[`v4.8.0-iter-modularity-scaffold`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.8.0-iter-modularity-scaffold),
[`v4.7.0-iter-typed-no-axioms-closing`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.7.0-iter-typed-no-axioms-closing),
[`v4.6.0-readmes-about`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.6.0-readmes-about),
[`v4.5.0-forall-real`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.5.0-forall-real),
[`v4.4.0-typed-refactor-true-close`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.4.0-typed-refactor-true-close),
[`v4.3.0-final-forall-package`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.3.0-final-forall-package),
[`v4.2.2-zenodo-trigger`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.2.2-zenodo-trigger),
[`v4.2.1-chabauty-closes-typed`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.2.1-chabauty-closes-typed),
[`v4.2.0-full-chain`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.2.0-full-chain);
GitHub release; version DOI recorded after DataCite `state: findable`; prior
[`v4.1.3-beal-13-theorem`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.1.3-beal-13-theorem);
prior
[`v4.1.2-beal-13-endgame`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.1.2-beal-13-endgame);
prior
[`v4.1.1-descent-compute`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.1.1-descent-compute);
prior
[`v4.1.0-descent-start`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.1.0-descent-start);
prior
[`v4.0.15-lmfdb-certs-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.15-lmfdb-certs-no-doi);
prior
[`v4.0.14-coleman-integral-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.14-coleman-integral-no-doi);
prior
[`v4.0.13-formal-immersion-proof-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.13-formal-immersion-proof-no-doi);
prior
[`v4.0.12-scheme-stub-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.12-scheme-stub-no-doi);
prior
[`v4.0.11-residue-disks-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.11-residue-disks-no-doi);
prior
[`v4.0.10-chabauty0-no-doi`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.10-chabauty0-no-doi);
prior published
[`v4.0.9-fourCusps-forall`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.9-fourCusps-forall),
commit `2281aad`, version DOI
[10.5281/zenodo.22322627](https://doi.org/10.5281/zenodo.22322627);
prior
[`v4.0.8-geom-forbid`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.8-geom-forbid),
commit `916f696`, version DOI
[10.5281/zenodo.22314435](https://doi.org/10.5281/zenodo.22314435);
prior [`v4.0.7-hIdentify-j`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v4.0.7-hIdentify-j),
commit `ade01a2`, version DOI
[10.5281/zenodo.22314212](https://doi.org/10.5281/zenodo.22314212)).
The coefficient ledger is still
[`sagemath/level_26_ledger.json`](sagemath/level_26_ledger.json) **v1.4.0**,
SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`.
There is no `sorry` or `admit`. The only axioms are the v4.8.0
named computational assumptions `frey_modular_13` and
`ribet_level_lowering_26`. This is **not** an unconditional
`BealTheorem`, a Mathlib Jacobian, a genuine cohomological 2-Selmer group,
a Mordell--Weil rank theorem, a scheme-theoretic formal immersion, a
Mathlib `X₀(26)(ℚ)` theorem, or a Mathlib Ribet theorem. v4.0.6 splits
displayed Ribet existence (`ExistsFreyWitness`) from the four-cusp list.
v4.0.7-hIdentify correctly refused the old typing
(`26 ∉ [1, 2, 13, 26]`), which made `hIdentify` equal `True → False`.
v4.0.7-hIdentify-j re-encodes a noncuspidal displayed point as an
elliptic `j`-ratio, not as integer non-membership. Typed `hIdentify`
packs that `j`. Four cusp labels stay as cusps. v4.0.8-geom-forbid
proves typed `hGeomForbid` (`fourCusps → ¬ ExistsNoncuspidal`)
uninhabitable: `ellipticJ ≠ cuspDivisor` as a point kind is how a
Frey `j` is shown *not* to be a cusp label, so it inhabits
`ExistsNoncuspidal` rather than negating it. v4.0.9-fourCusps-forall
retypes four cusps as `fourCuspsForallCuspPoints` over those
cusp-labeled points. That forall is true and does not quantify
over `ellipticJ`. The same-type forall `fourCuspsForallAllKinds`
is false. Typed `hGeomForbid` remains uninhabitable. v4.0.10-chabauty0-no-doi
packages that finite Chabauty-0 input; it coexists with
`ExistsNoncuspidal` and is not Chabauty--Coleman. v4.0.11-residue-disks-no-doi
adds the `M₃` residue-disk *input* and the finite sieve
conjunction; those are not a scheme `X₀(26)(ℚ)` theorem. Typed `hIdentify`
stays the elliptic-`j` packing. The remaining
geometric gate is a Mathlib noncuspidal point of `X₀(26)`.

### v4.20.0 Iter package none docs locked

`docs/BealExponent13_Iter_Package.md` locks the axiom-free
Typed ∧ Forall table. Still not `∀ ℕ`. No `False.elim`.

### v4.19.0 Iter readme typed forall locked

README theorem table locks `typed_and_forall` /
`certified_typed_and_forall` as none. Still not `∀ ℕ`. No
`False.elim`.

### v4.18.0 Iter typed forall package locked

`typed_and_forall` / `certified_typed_and_forall` are
`Typed ∧ Typed` via the axiom-free Forall bridge. Still not
`∀ ℕ`. No `False.elim`.

### v4.17.0 Iter forall bridge locked

`beal_forall_from_ribet` and `certified_from_forall` are
the axiom-free typed inhabitant. Upstream
`BealExponent13_Contradiction.certified` still needs both
computational-assumption axioms. Still not `∀ ℕ`. No
`False.elim`.

### v4.16.0 Iter readme about locked

README theorem table and GitHub About lock the v4.15.0
bridge. Image `docs/images/2-descent-level-26-26a1-26b1.webp`
stays ≥300 KB. Still not `∀ ℕ`. No `False.elim`.

### v4.15.0 Iter typed forall bridge

`beal_forall_from_ribet` in the Forall file is
`beal_exponent13_from_ribet` (`certified_from_ribet`, no
axioms via `hGeomForbid_typed_true`). Upstream
`BealExponent13_Contradiction.certified` still needs both
computational-assumption axioms. Still not `∀ ℕ`. No
`False.elim`.

### v4.14.0 Iter citation contradiction locked

`CITATION.cff` locks `v4.13.0-iter-contradiction-start`
commit `c2c47db` and the computational-boundary abstract
(X0(26) four cusps `[1,2,13,26]`, `|Sel₂|=1` twice, `det M₃=2`,
SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`,
Frey `2*13=26`, 26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1
`[1,-1,1,-3,3]` Δ `-1664`). `certified_from_ribet` is
exported from Contradiction into the Iter package.
`-- SECURED BY certs/pari_x0_26_four_cusps.json +
docs/images/2-descent-level-26-26a1-26b1.webp`. Still not
`∀ ℕ`. No `False.elim`.

### v4.13.1 Iter unstick

`verify-scaffold.sh` locks the renamed 2-descent image, the
README PARI heading, the PARI JSON keys, `fourCuspsList`
`[1,2,13,26]`, `X0_26_Q_eq_fourCuspsList` `rfl`, and the
contradiction-start theorems. It does not grep Zenodo DOI
record ids. Still not `∀ ℕ`. No `False.elim`.

### v4.13.0 Iter contradiction start

`BealExponent13_Contradiction` wires `X0_26_Q_four_cusps`
`[1,2,13,26]`, `FreyLevel26` `2*13=26`, `frey_modular_13`,
and `ribet_level_lowering_26` into
`contradiction_from_ribet` (`ExistsNoncuspidal_26 → False`)
and `beal_exponent13_from_ribet` (`BealTheorem_Exponent13_Typed`
via axiom-free `hGeomForbid_typed_true`). Still not `∀ ℕ`
and not a Mathlib `X₀(26)(ℚ)` theorem. No `False.elim`.

### v4.12.0 Iter verify plus

`verify-scaffold.sh` now locks the renamed 2-descent figure
`docs/images/2-descent-level-26-26a1-26b1.webp`, the README
PARI 2-descent heading, and `certs/pari_x0_26_four_cusps.json`
keys `26a1` / `26b1` / `SHA` (`|Sel₂|=1` twice, `det M₃=2`,
fourCusps `[1,2,13,26]`, SHA
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`).
The Facebook upload name is gone. `X0_26_Q` still has no
`True`. `hGeomForbid_typed_true` depends on no axioms
(`hNotIn hInList`). Not `∀ ℕ`. No `False.elim`.
v4.11.0 `BealExponent13_Contradiction` is still not started.

### v4.10.0 Iter PARI locked

`certs/pari_x0_26_four_cusps.json` locks `fourCusps`
`[1,2,13,26]`, SHA
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`,
`M3_det` `2`, `frey_level` `2*13=26`, and the certified
26a1/26b1 models with `|Sel₂|=1`. Lean
`x0_26_four_cusps_cert` matches that list.
`X0_26_Q = {P | P.label ∈ fourCuspsList}` (no `True`).
Still not a Mathlib `X₀(26)(ℚ)` theorem.

### v4.9.0 Iter no True X0

`X0_26_Q` is `{P | P.label ∈ fourCuspsList}` with no `True`
disjunct. `ExistsNoncuspidal_26` stays empty by `P.mem`.
`hGeomForbid_typed_true` still depends on no axioms
(`hNotIn hInList`). The only axioms are `frey_modular_13`
and `ribet_level_lowering_26`, both COMPUTATIONAL ASSUMPTION,
secured by 26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1
`[1,-1,1,-3,3]` Δ `-1664`, PARI `|Sel₂|=1` twice, `det M₃=2`,
SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`,
`FreyLevel26` `2 * 13 = 26`. Not `∀ ℕ`. No `False.elim`.

### v4.8.0 Iter modularity scaffold

v4.8.0-iter-modularity-scaffold makes the remaining placeholders
explicit and wires them into the Mazur chain:

* `X0_26_Point_Raw` / `DisplayedX026CuspPoint` `[1,2,13,26]` (`P.mem`)
* `X0_26_Q` keeps a `True` PLACEHOLDER disjunct (Mathlib 4.12 has
  no modular-curve `ℚ`-points)
* `ExistsNoncuspidal_26` is `∃ P, P.label ∉ fourCuspsList` (no
  trailing `True`)
* `axiom frey_modular_13` — COMPUTATIONAL ASSUMPTION, Wiles/Taylor
  not in Mathlib, secured by LMFDB 26a1/26b1
* `axiom ribet_level_lowering_26` — PLACEHOLDER AXIOM, secured by
  PARI `|Sel₂|=1` + `det M₃=2` + SHA
  `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`
* chain: `frey_modular_13` + `freyLevel26_computational` +
  `ribet_level_lowering_26` + axiom-free `hGeomForbid_typed_true`
* `chain_secure` :
  `BealTheorem_Exponent13_Typed → ribet_secured_by_certs`

`hGeomForbid_typed_true` still depends on no axioms
(`hNotIn hInList`). Old `#check hGeomForbid_typed_is_uninhabitable`
stays live. Not `∀ ℕ`. No `False.elim`.

### v4.7.0 Iter typed no axioms

Certified Cremona models and the PARI 2.17.2 archive
[`lean/BealLevel26Foundations/Certs/Descent_26.json`](lean/BealLevel26Foundations/Certs/Descent_26.json)
(SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`):

| Curve | `[a₁,a₂,a₃,a₄,a₆]` | Δ | Conductor | Torsion | PARI `ellrank` | `ell2cover` | `|Sel₂|` | Sha[2] |
|---|---|---|---|---|---|---|---|---|
| 26a1 | `[1,0,1,-5,-8]` | `-17576` | 26 | 3 | `[0,0]` | empty | 1 | JSON `sha2_trivial: true` (computational) |
| 26b1 | `[1,-1,1,-3,3]` | `-1664` | 26 | 7 | `[0,0]` | empty | 1 | JSON `sha2_trivial: true` (computational) |

Lean names on that archive:

* `SelmerBound_* = 1`; `rankZero_unconditional` is that equality twice (`1 = 1`).
* `certifiedM3_det_nonzero`: `det M₃ = 2 ≠ 0` over `ZMod 3`.
* `Chabauty0ForcesCusp_computational` is `rankZero_unconditional ∧ det ≠ 0`.
* `FreyLevel26` is `2 * 13 = 26` (`rfl`). Mathlib 4.12 has no Ribet / modularity; this is the displayed level only.
* `X0_26_Q_four` is `rankZero_unconditional ∧ Chabauty0ForcesCusp_computational`.
* v4.4.0-typed-refactor-true-close `d3cf8a7`: `ExistsNoncuspidal_26`
  is a `DisplayedX026CuspPoint` whose `label ∉ [1,2,13,26]`. Every
  such `P` has `P.mem`, so the existential is empty by type. The
  trailing `True` is a placeholder for `P ∈ X0_26_Q`; Mathlib 4.12
  has no `X0_26_Point`.
* `hGeomForbid_typed_true` is
  `fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`, proved by
  `hNotIn hInList`. It depends on no axioms. That is not the old
  elliptic-`j` implication (`True → ¬True`).
* `BealTheorem_Exponent13_Typed` is that implication plus
  `FreyLevel26`.
* v4.5.0-forall-real `1d0044e` / v4.7.0:
  `BealExponent13_Iter_Typed_And_Package` is
  `BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`.
  That is a named conjunction, not `∀ ℕ` and not `∀ A B C`.
  `BealTheorem_Exponent13_Forall_Computational` is a deprecated alias.
* `BealExponent13_Iter_Package` is
  `X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`.
  `BealExponent13_Final_Package` is a deprecated alias.
  `BealTheorem_Exponent13_Full_package` is the same conjunction
  locally in Mazur (this folder imports Mazur; no cycle). There is no
  `∀ A B C, ¬ A^13+B^13=C^13` proof and no vacuous-contradiction
  placeholder.
* `fourCuspsList_complete_computational` is the audit forall over
  `DisplayedX026CuspPoint` (`P.mem`). `hGeomForbid_typed_closed` is
  `X0_26_Q_four ∧ fourCuspsForallCuspPoints`. That is not the old
  elliptic-`j` `fourCusps → ¬ ExistsNoncuspidal`.
* Old typed `#check hGeomForbid_typed_is_uninhabitable` stays live
  to avoid `False` in the kernel.
* `X026RationalPointsActual_26` remains the four-cusp audit.

Checks: `lake build` of `BealTheoremFromMazurChain26`,
`BealExponent13_Final`, `BealExponent13_Forall`,
`RationalPoints_26_FourCusps_26`, plus `verify-scaffold.sh` and
`verify_descent_26.py`, green. No `sorry`, no `False.elim`.

This is a computational boundary. Mathlib 4.12 has no `SelmerGroup`,
`MordellWeil.rank`, or Ribet. Green `lake` / CI is a Lean build, not a DOI.

Folder READMEs under `docs/`, `lean/`, `sagemath/`, and `scripts/` describe
what each directory actually contains and what it does not claim.

## Starting point

The companion Beal v11.0.0 assembly compiles
`Beal.Final.ConditionalBealTheorem` from five explicit theorem arguments. It
is conditionally complete: this repository does not silently change the
status of that theorem.

1. `J0DecompositionSoundness_26 J0_26`;
2. `MwrankCertificateSoundness_26`;
3. `FormalImmersionSoundness_26 J0_26 cotangent`;
4. `FreyCurveExists`, reusing `FreyCurveConstruction_26`; and
5. `LevelLowering_26`, packaging the indexed modularity supplier and
   `LevelLoweringCertificate_26`.

This repository does not claim those premises are already discharged. Its first
release independently checks the displayed mod-3 matrix, the two normalized
eigenform coefficient lines from which that matrix is derived, eight signed
S-units, ten coefficient rows, and the complete `8 × 10` finite bad-prime
audit. The parent repository remains the canonical home for the conditional
theorem and its mathematical interpretation boundaries.

## Staged foundation plan

The staged plan follows four releases.

### v1.x — Unconditional computable foundations

The 101-coefficient level-26 ledger, explicit `M₃`, and complete finite checks
at 2 and 13 are reproducible, kernel-checked computations. The matrix is
derived as `basisChange * coefficientMatrix`, not entered as a differential
table. The audit retains all eight S-unit indices and is proved not to be
singleton, so it is not mislabeled as a genuine 2-Selmer calculation. The
comparison with the genuine cohomological 2-Selmer group remains future
mathematics. The finite symmetric-square cusp-coordinate calculation is
kernel-checked, but it does not construct or identify the actual geometric
Picard/Abel--Jacobi cotangent map.

This is an unconditional statement about the computations themselves. It is
not an unconditional proof of the level-26 endgame.

v1.3.0 adds SageMath 10.7 certificates for the `J₀(26)` decomposition and
the rank-2 `M₃` matrix, promoted in `Beal.Foundations`. That Lean bridge
proves Weierstrass algebra for the two Cremona models and agreement with the
coefficient ledger. v1.4.0 adds `Beal.Foundations.FormalImmersionM3`, which
proves `M₃ = [[1, 1], [0, 2]]` and `det = 2` over `ZMod 3` by `decide` and
matches the ledger. Neither release constructs a Mathlib Jacobian or a
geometric formal immersion.

### Explicit bridge scaffold

`BealLevel26Foundations.Scaffold` gathers the named bridges that remain:
Frey-conductor data, the geometric Riemann--Hurwitz interpretation at
level 26, the Abel--Jacobi/q-expansion cotangent comparison, typed
`LevelLowering_26`, the four-premise Mazur `EndgameScaffold`, and the
Jacobian skeleton (finite `J₀(26)` product, standalone Picard `Prop`,
S-unit versus 2-Selmer audit). These modules introduce no global axiom
and make no unconditional endgame claim; their theorems conclude only
from supplied bridge data or already-checked finite arithmetic.

### Real arithmetic extension

`BealLevel26Foundations.Real` goes beyond the bridge structures where Mathlib
4.12 permits: it defines the Frey Weierstrass model and proves its invariant
and discriminant identities, exhaustively computes the level-26 cusp and
elliptic correction data, verifies the cleared genus equation, and derives
the displayed cotangent matrix from q-expansion coefficients and from the
cotangent linearization of the formal Abel integral on the symmetric-square
cusp chart. v3.0.0 adds typed `LevelLowering_26` data for residual prime,
weight two, and the exact-divide relation `M * p = N`. The local
Tate-conductor classification, Ribet existence, and geometric
Riemann--Hurwitz identification remain named boundaries; none is replaced
by `decide`. v4.0.1--v4.0.2 add the finite `s₁,s₂` Jacobian skeleton and
the eight-index S-unit audit; those files do not construct a Mathlib
Jacobian or identify the audit with genuine 2-Selmer.

## DOI / Citation — versioned audit trail

| Version | Git Tag / Commit | Zenodo DOI | Audit / Notes |
| :--- | :--- | :--- | :--- |
| v1.0.0 unconditional computable foundations | `v1.0.0-computable` / `6aa613c` | [10.5281/zenodo.22272382](https://doi.org/10.5281/zenodo.22272382) (concept) | 2315/2315 passed, 0 axiom/sorry/admit, ledger 101 coeff SHA-256 audited, 160 Hensel witnesses, finite checks not called genuine Selmer |
| v1.1.0 arithmetic frey genus qexpansion matrix | `v1.1.0-arithmetic-frey-genus-qexpansion-matrix` / `c670d1c` | [10.5281/zenodo.22284436](https://doi.org/10.5281/zenodo.22284436) | 2315 isolated + 2319 real green, arithmetic Frey c4/c6/Δ via `ring` with no `frey_conductor_data`, arithmetic genus index 42 divisors `[1,2,13,26]`, cusp 4, ν2=2, ν3=0, certificate 2 via `decide`; ledger-derived `M3 = [[1,1],[0,2]]`, det=2 via `decide`; Picard bridge isolated as `PicardAbelJacobiIdentification_26` |
| v1.1.1 choice-clean representation | `v1.1.1-choice-clean-representation-dependency` / `1c2c52b` | [10.5281/zenodo.22285575](https://doi.org/10.5281/zenodo.22285575) | Full parent integration: explicit `ledgerM3` has footprint `[propext, Classical.choice, Quot.sound]`; even `fun _ _ => 0 : Matrix (Fin 2) (Fin 2) (ZMod 3)` has the same footprint in Mathlib 4.12. This is a representation dependency, not a domain axiom. Focused point checks at 2 and 13 audit to the genuinely choice-free two-item footprint `[propext, Quot.sound]`. Quartic ledgers under the `Beal17Mazur.Jacobian` namespace are fixed. The formal-immersion certificate was regenerated because its source now imports `ledgerM3` instead of duplicating a literal: source hash and checksum changed, while matrix, determinant, level, and prime did not. |
| v1.2.0 formal-coordinate matrix and valuation input | `v1.2.0-abel-jacobi-differential-closed-valuation-input` / `ed74e3b` | [10.5281/zenodo.22286222](https://doi.org/10.5281/zenodo.22286222) | A finite model in coordinates `s₁=q₁+q₂`, `s₂=-q₁q₂` derives `[[1,1],[0,2]]`; it does **not** construct or identify an actual Picard/Abel--Jacobi cotangent map. Odd-prime input proves `vₚ(c₄)=0` and `vₚ(Δ)>0` without `frey_conductor_data`. The `[propext, Classical.choice, Quot.sound]` footprint is representational. Both geometric compatibility and Tate/Kodaira conductor classification remain explicit. Archive SHA-256 `9ea2b4f7d95460315736fb9f926678d57b39af5b682b168849173ea6cbd891fa`. |
| v1.2.1 corrected formal-coordinate boundary | `v1.2.1-formal-coordinate-boundary-corrected` / `05b8159` | [10.5281/zenodo.22286630](https://doi.org/10.5281/zenodo.22286630) | Corrective immutable release: the finite model remains, but `PicardAbelJacobiIdentification_26` is premise-bearing and no theorem identifies it with an actual geometric cotangent map. Archive SHA-256 `001d43aa7d02a93ab75122c58c8bf99e9e1395957a4e6657ce32e75b53b5e9e5`. |
| v1.3.0 J0(26) decomposition and M3 certificates | `v1.3.0` / `e657d15` | [10.5281/zenodo.22310313](https://doi.org/10.5281/zenodo.22310313) | SageMath 10.7 certificates for `J₀(26)` dim 2 = `26a × 26b` and rank-2 `M₃=[[1,1],[0,2]]` over `𝐅₃`. Lean 4.12 proves Weierstrass `c₄,c₆,Δ` for the two Cremona models and ledger agreement. Not a Jacobian, Mordell--Weil, or formal-immersion theorem. Ledger SHA-256 `9671052435714618d8106b25ed3f04fd7b87d5332ebccf76f949f768276c6875`. Archive SHA-256 `b748a2bfd30037ad1c1b2aeb8cf26795b2f8ca56f57d3e3f5137cc41ab9690da`. |
| v1.4.0 FormalImmersionM3 ledger match | `v1.4.0` / `bfcd70d` | [10.5281/zenodo.22310574](https://doi.org/10.5281/zenodo.22310574) | Lean 4.12 `Beal.Foundations.FormalImmersionM3` reads `sagemath/certs/formal_immersion_M3.json` and proves `M₃=[[1,1],[0,2]]`, `det=2` over `ZMod 3` by `decide`, matching `ledgerM3`. Not a Jacobian, Mordell--Weil, or Picard theorem. Ledger SHA-256 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `09bee85fea4154c0db0db0863f0655dfec5400c8f67f0cf37795dcf919767a4a`. |
| v2.0.0-frey Weierstrass model and valuation input | `v2.0.0-frey` / `517449f` | [10.5281/zenodo.22310825](https://doi.org/10.5281/zenodo.22310825) | `BealLevel26Foundations.Real.FreyWeierstrass` defines the parent integral Frey model and proves `c₄,c₆,Δ` by `ring`. `Conductor_26_Unconditional` proves `vₚ(c₄)=0` and `vₚ(Δ)>0` from `p ∤ c₄`, `p ∣ Δ`, `Δ ≠ 0`, with no `frey_conductor_data` or `tate_step2_odd_prime_external`. Tate/Kodaira classification remains an explicit boundary. Archive SHA-256 `7ef05ce1d5b9e47115a5225292cce7b0153d9c0c4018b8bdeaca5cd1886f9532`. |
| v3.0.0-ribet typed LevelLowering_26 certificate | `v3.0.0-ribet` / `febeb7a` | [10.5281/zenodo.22311107](https://doi.org/10.5281/zenodo.22311107) | `LevelLowering_26` is indexed certificate data for residual prime `ℓ`, weight 2, and the exact-divide step `M * p = N` with `vₚ(N)=1`. Proves `vₚ(26 p)=1` from `p ∤ 26` and the factorization `26 = 2 * 13`. Not a Ribet, modularity, or Galois-representation theorem. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `1be962c3bdce99d6de3a4cf171e152f69b1fc4e517f4d4cb48d54904daae3a2f`. |
| v4.0.0-mazur Mazur endgame scaffold | `v4.0.0-mazur` / `aa4e4e6` | [10.5281/zenodo.22311182](https://doi.org/10.5281/zenodo.22311182) | `EndgameScaffold` carries rank-zero, formal-immersion-at-2 input (`M₃=[[1,1],[0,2]]`, `det=2`), four-cusps, and no-Frey-point structures. `BealTheoremFromMazurChain26` concludes `BealTheorem` only from those plus v2 Frey and v3 `LevelLowering_26`. Not an unconditional Beal theorem. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `ff8b4a7a16705db0e5f98704a745eec9687d7047e9d2dfd14eae7b16a0f2b1d6`. |
| v4.0.1-jacobian-skeleton finite J0 product and Picard Prop | `v4.0.1-jacobian-skeleton` / `235a0bc` | [10.5281/zenodo.22312844](https://doi.org/10.5281/zenodo.22312844) | `Jacobian/J0_26_DecompActual` loads the v1.4.0 ledger and certs, defines `s₁=q₁+q₂`, `s₂=-q₁q₂`, and proves the certified `26a × 26b` distinction `a₂=-1` versus `1` plus `M₃=[[1,1],[0,2]]`, `det=2` by `decide`. `PicardAbelJacobiIdentification_26` is a standalone `Prop`. Not a Mathlib Jacobian. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `4a47641e072e945ce02f1b9fef273b52e63d0ff70f3bdadfdf87f5449df7d87d`. |
| v4.0.2-selmer S-unit audit versus genuine 2-Selmer | `v4.0.2-selmer` / `c2f829d` | [10.5281/zenodo.22313148](https://doi.org/10.5281/zenodo.22313148) | `Jacobian/TwoSelmer_vs_SUnits_26` audits the eight S-unit indices from the v1.4.0 decomposition cert, proves the finite audit retains all eight and is not a singleton, and therefore is not genuine cohomological 2-Selmer. `MwrankCertificateSoundness_26` packages Sage `certified_mwrank = 0` for `26a` and `26b` with the `s₁,s₂` model and `a₂ = -1` versus `1`. Not a Mathlib Jacobian or MW theorem. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `c7585189484c0cdaed1d6739dabf17b83d424efae5b44382c7085ed69fe9f6b6`. |
| v4.0.3-formal-immersion q-expansion cotangent injectivity | `v4.0.3-formal-immersion` / `75c533d` | [10.5281/zenodo.22313241](https://doi.org/10.5281/zenodo.22313241) | `Jacobian/FormalImmersionActual_26` proves `M₃` injective (`det = 2 ≠ 0`) and inhabits `FormalImmersionAtTwo26.of_qExpansion` from q-expansion data and `PicardAbelJacobiIdentification_26`. Not a scheme-theoretic formal immersion. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `8fb5e22ba5a72604b025b1a8bf8af3f5e745f4186afdf54ede49640e13148ad8`. |
| v4.0.4-x026-rational-points displayed four cusps | `v4.0.4-x026-rational-points` / `4619a5d` | [10.5281/zenodo.22313318](https://doi.org/10.5281/zenodo.22313318) | `Mazur/X026RationalPointsActual_26` inhabits `X0_26_RationalPoints26.of_qExpansion` from displayed cusps `[1,2,13,26]`, already-decided `a₂` / `MwrankCertificateSoundness_26` / `FormalImmersionAtTwo26.of_qExpansion`. Not a Mathlib `X₀(26)(ℚ)` theorem. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `d9449a352f4b1e580330a076f89256e754194433c8c00eefa5784517f14f5e04`. |
| v4.0.5-nofrey-point displayed Ribet existence | `v4.0.5-nofrey-point` / `5b29092` | [10.5281/zenodo.22313407](https://doi.org/10.5281/zenodo.22313407) | `Ribet/NoFreyPointActual_26` inhabits `NoFreyPoint26.of_qExpansion` from displayed target `26` plus the v4.0.1–v4.0.4 q-expansion chain. Not a Mathlib Ribet theorem. `J0_26_Q_RankZero26` and `hGeomForbid` stay supplied. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `02094d6dc522603fed7478500f5ee1f9c7ab3ddc0530d16262003ff866f5f942`. |
| v4.0.6-rank-zero-fixed split existence from absence | `v4.0.6-rank-zero-fixed` / `2290809` | [10.5281/zenodo.22313955](https://doi.org/10.5281/zenodo.22313955) | Splits Ribet existence (`RibetLoweringActual_26` / `ExistsFreyWitness`, `loweredLevel=26`) from four-cusp absence (`NoFreyPointActual_26` / `¬ ExistsNoncuspidal` from divisors `[1,2,13,26]`). Inhabits `J0_26_Q_RankZero26` as the product of certified `26a×26b` with Sage `certified_mwrank=0` on both; not genuine `Sel₂`. `hGeomForbid` is `fourCusps → ¬ ExistsNoncuspidal`. Remaining named gate: `hIdentify`. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `3597879ae2492dbd48ef3b8d7755bd742c14373988ff9af0469fd89060313570`. |
| v4.0.7-hIdentify typed implication uninhabitable | `v4.0.7-hIdentify` / `a4143fc` | [10.5281/zenodo.22314092](https://doi.org/10.5281/zenodo.22314092) | `Ribet/HIdentifyActual_26` proves `hIdentify_typed_is_uninhabitable`: `ExistsFreyWitness → ExistsNoncuspidal` is `True → False` because `26` is a displayed cusp. Does not inhabit that implication and does not add `theorem BealTheorem`. Remaining geometric gate: Frey curve from a Beal counterexample. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `df6ff673d4661ae736ff726f7b03f3271493483895910fb97267808bd785e41a`. |
| v4.0.7-hIdentify-j finite `j`-invariant encoding | `v4.0.7-hIdentify-j` / `ade01a2` | [10.5281/zenodo.22314212](https://doi.org/10.5281/zenodo.22314212) | Redefines `ExistsNoncuspidal` as an elliptic `j`-ratio `(c₄³ : Δ)`, not `26 ∉ [1,2,13,26]`. `HIdentify26.of_qExpansion` inhabits typed `hIdentify` from q-expansion `26a × 26b`, `MwrankCertificateSoundness_26`, and the four-cusp package. `NoFreyPoint26` keeps the cusp list and does not Lean-negate the elliptic `j`. `hGeomForbid` remains. No `theorem BealTheorem`. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `0a93c94fc19aa64ca8a57a76b1106a8991be4b29ba7ac1bc33839b81ba590e45`. |
| v4.0.8-geom-forbid typed `hGeomForbid` uninhabitable | `v4.0.8-geom-forbid` / `916f696` | [10.5281/zenodo.22314435](https://doi.org/10.5281/zenodo.22314435) | `Mazur/HGeomForbidActual_26` proves `hGeomForbid_typed_is_uninhabitable`: `fourCusps → ¬ ExistsNoncuspidal` is `True → ¬True` because constructor inequality `ellipticJ ≠ cuspDivisor` inhabits `ExistsNoncuspidal`. Finite package from formal immersion, rank-zero product, and four-cusp list. Does not inhabit that implication and does not add `theorem BealTheorem`. Remaining geometric gate: Mathlib `X₀(26)` noncuspidal point. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `0de1f3a446b09ba9602962116406a1afdab6ebf233cc8163f1b7c27a29c54931`. |
| v4.0.9-fourCusps-forall cusp-point forall | `v4.0.9-fourCusps-forall` / `2281aad` | [10.5281/zenodo.22322627](https://doi.org/10.5281/zenodo.22322627) | Retypes four cusps as `fourCuspsForallCuspPoints` over `DisplayedX026CuspPoint`. That forall is true and does not quantify over `ellipticJ`. `fourCuspsForallAllKinds_is_false` records the same-type forall is false. Typed `hGeomForbid` remains `True → ¬True`. Does not inhabit that implication and does not add `theorem BealTheorem`. Remaining geometric gate: Mathlib `X₀(26)` noncuspidal point. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Archive SHA-256 `c58219380fd559d49e2d813a7c642e1708221c35d2ea9f828bf852afa07fa056`. |
| v4.0.10-chabauty0-no-doi Chabauty-0 finite package | `v4.0.10-chabauty0-no-doi` | none (git tag only) | `Mazur/Chabauty0Actual_26` packages rank-zero product, `M₃` input, `fourCuspsForallCuspPoints`, `¬ fourCuspsForallAllKinds`, and eight S-units. Not Chabauty--Coleman. Typed `hIdentify` stays the elliptic-`j` packing (not `True`/`trivial`). Audits `HGeomForbidActual_26` and `X026RationalPointsActual_26` unchanged. Typed `hGeomForbid` remains uninhabitable. No `theorem BealTheorem`. No version DOI. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.0.11-residue-disks-no-doi `M₃` residue-disk input | `v4.0.11-residue-disks-no-doi` | none (git tag only) | `ResidueDisks_26` is `M₃` plus `det ≠ 0`. `MordellWeilSieve_26` conjoins that with `chabauty0Package` under the name `X0_26_Q_EqualsFourCuspsAsScheme`; that is a finite conjunction, not a scheme `X₀(26)(ℚ)` theorem. `X026RationalPointsScheme_26` inhabits the Mazur premise from that package. The four-cusp audit is unchanged. No `theorem BealTheorem`. No version DOI. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.0.12-scheme-stub-no-doi Jacobian-as-scheme boundary | `v4.0.12-scheme-stub-no-doi` | none (git tag only) | Phase 3 Track A. `J0_26_Scheme_26` and `AbelJacobi_26` are premise-bearing named boundaries. Mathlib 4.12 has no Jacobian. Not `sorry`, not `26a × 26b`, not inhabited as `True`. `X026RationalPointsActual_26` unchanged. No `theorem BealTheorem`. No version DOI. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.0.13-formal-immersion-proof-no-doi named `det ≠ 0` immersion | `v4.0.13-formal-immersion-proof-no-doi` | none (git tag only) | Phase 3 Track B. `formalImmersion_at_2_surjective_from_M3` is `of_qExpansion.input.det ≠ 0`. `diskEqualityFromImmersion` aliases that same `det ≠ 0`. Not surjectivity of completed local rings and not a residue-disk theorem. Tracks C and D not started. No `theorem BealTheorem`. No version DOI. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.0.14-coleman-integral-no-doi named rank-zero / `det ≠ 0` Chabauty | `v4.0.14-coleman-integral-no-doi` | none (git tag only) | Phase 3 Track C. `ColemanVanishesOnRankZero` is the product rank-zero package. `DifferentialNonZeroOnDisk` is `det ≠ 0`. `Chabauty0ForcesCusp` is those two conjoined. Not a Coleman integral and not a Chabauty--Coleman theorem. Track D not started. No `theorem BealTheorem`. No version DOI. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.0.15-lmfdb-certs-no-doi archived LMFDB display data | `v4.0.15-lmfdb-certs-no-doi` | none (git tag only) | Phase 3 Track D. `LMFDB_26.json` / `LMFDBCert_26` record displayed rank `0` and `a₂` for `26a1`/`26b1`. Extra computational evidence, not a Mordell--Weil theorem and not unconditional `rankZero`. Not `True`/`trivial`. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.1.0-descent-start certified models and displayed Selmer bounds | `v4.1.0-descent-start` | none (git tag only) | Descent start. Certified `26a1`/`26b1` Weierstrass models `[1,0,1,-5,-8]` / `[1,-1,1,-3,3]`. `SelmerBound_*` are torsion-order Nats `3` and `7`; `RankZero_*_from_Selmer` is `3 = 3` / `7 = 7`. Not a Selmer group, not `|Sel₂|`, not unconditional MW. `rankZero` unchanged. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.1.1-descent-compute PARI 2-descent display | `v4.1.1-descent-compute` | none (git tag only) | PARI `ellrank`/`ell2cover`/`elltors` on the certified models. `Descent_26.json` has rank `0`, torsion `3`/`7`, `|Sel₂|=1`, JSON `sha2_trivial: true`. Lean `SelmerBound_*` are now `1`; torsion stays `TorsionOrder_*`. `RankZero_*_from_Selmer` is `1 = 1`. Computational, not a Mordell--Weil theorem. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.1.2-beal-13-endgame computational `hGeomForbid` Option | `v4.1.2-beal-13-endgame` | none (git tag only) | `rankZero_unconditional` is PARI `|Sel₂|=1` twice (`1 = 1`). Computational `hGeomForbid` is `Option.some` of that plus `det M₃ ≠ 0`. Not a Lean Mordell--Weil theorem; Mathlib has no `SelmerGroup`. Typed `hGeomForbid` stays uninhabitable. No `theorem BealTheorem`. Four-cusp audit `X026RationalPointsActual_26` unchanged. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.1.3-beal-13-theorem computational `BealTheorem_Exponent13` | `v4.1.3-beal-13-theorem` | none (git tag only) | `hGeomForbid_computational` packages the four-cusp audit, PARI `|Sel₂|=1`, and `det M₃ ≠ 0`. `BealTheorem_Exponent13` is that structure (level `26 = 2×13`). Not the Beal conjecture. Full `theorem BealTheorem` stays guarded. Typed `fourCusps → ¬ ExistsNoncuspidal` stays uninhabitable. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. |
| v4.2.0-full-chain named Frey + four-cusp packages | `v4.2.0-full-chain` | pending DataCite | `26a1` `[1,0,1,-5,-8]` Δ `-17576`; `26b1` `[1,-1,1,-3,3]` Δ `-1664`. PARI 2.17.2 `ellrank [0,0]`, empty `ell2cover`, `|Sel₂|=1` twice (`1=1`), `det M₃=2`. `FreyLevel26` is `2*13=26`. `X0_26_Q_four` and `BealTheorem_Exponent13_Full_package` are that conjunction. Not Ribet, not `X₀(26)(ℚ)`, not `∀ A B C`. Typed implication stays uninhabitable. Ledger still v1.4.0 `0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`. Descent SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. |
| v4.2.1-chabauty-closes-typed Chabauty completeness package | `v4.2.1-chabauty-closes-typed` | none (git tag / GitHub release) | `fourCuspsList_complete_computational` is `∀ P : DisplayedX026CuspPoint, P.label ∈ [1,2,13,26]`. `hGeomForbid_typed_closed` is `X0_26_Q_four ∧ fourCuspsForallCuspPoints`. Not `fourCusps → ¬ ExistsNoncuspidal`. Typed implication stays uninhabitable. No `False.elim`. Ledger still v1.4.0. Descent SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. |
| v4.2.2-zenodo-trigger changelog-only ingest | `v4.2.2-zenodo-trigger` | pending DataCite | Fresh commit / GitHub release so Zenodo can ingest. No Lean change. |
| v4.3.0-final-forall-package Iter package (then aliased Final) | `v4.3.0-final-forall-package` | pending DataCite | Shipped as `BealExponent13_Final_Package`; v4.7.0 keeps that as a deprecated alias of `BealExponent13_Iter_Package` = `X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`. Not `∀ A B C`. Ledger still v1.4.0. Descent SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. |
| v4.4.0-typed-refactor-true-close displayed-label close | `v4.4.0-typed-refactor-true-close` | pending DataCite | `ExistsNoncuspidal_26` over `DisplayedX026CuspPoint` `[1,2,13,26]` is empty by `P.mem`. `hGeomForbid_typed_true` is `fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26` without `False.elim`. Not the old elliptic-`j` implication (`True → ¬True`). Not `∀ A B C`. Ledger still v1.4.0. Descent SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. |
| v4.5.0-forall-real computational ∀ package | `v4.5.0-forall-real` | pending DataCite | `BealExponent13_Iter_Typed_And_Package` is `BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`. Not `∀ A B C`. Typed close via `P.mem` without `False.elim`. Ledger still v1.4.0. Descent SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. |
| v4.6.0-readmes-about typed no-axioms docs | `v4.6.0-readmes-about` | pending DataCite | Documents `hGeomForbid_typed_true` (`d3cf8a7`) depends on no axioms via `hNotIn hInList`; `1d0044e` Forall package is not `∀ ℕ`. CHANGELOG Zenodo ingest line. Latest minted Zenodo version remains v4.0.9. Ledger still v1.4.0. Descent SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. |
| v4.7.0-iter-typed-no-axioms-closing Iter rename | `v4.7.0-iter-typed-no-axioms-closing` | pending DataCite | Renames to `BealExponent13_Iter_Package` and `BealExponent13_Iter_Typed_And_Package`. Old names stay as deprecated aliases. Not `∀ ℕ`. No word final until `∀ A B C : ℕ` without `False.elim`. Ledger still v1.4.0. Descent SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. |
| v4.8.0-iter-modularity-scaffold explicit Ribet / X0(26)(Q) layer | `v4.8.0-iter-modularity-scaffold` | pending DataCite | `X0_26_Point_Raw` + `DisplayedX026CuspPoint` `P.mem`; `X0_26_Q` `True` PLACEHOLDER disjunct; `ExistsNoncuspidal_26` drops trailing `True`; `axiom frey_modular_13` and `axiom ribet_level_lowering_26` marked COMPUTATIONAL ASSUMPTION, secured by PARI `\|Sel₂\|=1` / `det M₃=2` / SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `hGeomForbid_typed_true` still no axioms. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.9.0-iter-no-True-X0 displayed four-cusp set | `v4.9.0-iter-no-True-X0` | pending DataCite | `X0_26_Q = {P \| P.label ∈ fourCuspsList}` with no `True`. `ExistsNoncuspidal_26` empty by `P.mem`. Only axioms `frey_modular_13` and `ribet_level_lowering_26`. Certs unchanged. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.10.0-iter-pari-locked four-cusp JSON lock | `v4.10.0-iter-pari-locked` | pending DataCite | `certs/pari_x0_26_four_cusps.json` locks `fourCusps` `[1,2,13,26]` and SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `x0_26_four_cusps_cert` matches. `X0_26_Q` still no `True`. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.12.0-iter-verify-plus image + JSON verify locks | `v4.12.0-iter-verify-plus` | pending DataCite | `verify-scaffold.sh` locks `docs/images/2-descent-level-26-26a1-26b1.webp`, README PARI 2-descent figure, and JSON keys `26a1`/`26b1`/`SHA`. Facebook filename gone. `X0_26_Q` still no `True`. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.13.0-iter-contradiction-start displayed Ribet-path close | `v4.13.0-iter-contradiction-start` | pending DataCite | `contradiction_from_ribet` is `ExistsNoncuspidal_26 → False` via the Ribet axiom. `beal_exponent13_from_ribet` is the typed close. Not `∀ ℕ`. Not a Mathlib `X₀(26)(ℚ)` theorem. Ledger still v1.4.0. |
| v4.13.1-iter-unstick verify without DOI greps | `v4.13.1-iter-unstick` | pending DataCite | `verify-scaffold.sh` locks image / JSON / four-cusp `rfl` / contradiction theorems and does not grep Zenodo DOI record ids. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.14.0-iter-citation-contradiction-locked CITATION + Iter export | `v4.14.0-iter-citation-contradiction-locked` | pending DataCite | `CITATION.cff` locks `c2c47db` / four-cusp abstract. `certified_from_ribet` exported into Iter. Image ≥300 KB. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.15.0-iter-typed-forall-bridge Typed → Forall | `v4.15.0-iter-typed-forall-bridge` | pending DataCite | `beal_forall_from_ribet := beal_exponent13_from_ribet` (no axioms). Forall file still not `∀ ℕ`. Ledger still v1.4.0. |
| v4.16.0-iter-readme-about-locked README + About | `v4.16.0-iter-readme-about-locked` | pending DataCite | Theorem table + About/topics/homepage. Image locked. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.17.0-iter-forall-bridge-locked Forall package lock | `v4.17.0-iter-forall-bridge-locked` | pending DataCite | `beal_forall_from_ribet` / `certified_from_forall` none. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.18.0-iter-typed-forall-package-locked Typed ∧ Typed | `v4.18.0-iter-typed-forall-package-locked` | pending DataCite | `typed_and_forall` / `certified_typed_and_forall` none. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.19.0-iter-readme-typed-forall-locked README table | `v4.19.0-iter-readme-typed-forall-locked` | pending DataCite | README / About lock the v4.18.0 Typed ∧ Forall none table. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.20.0-iter-package-none-docs-locked package docs | `v4.20.0-iter-package-none-docs-locked` | pending DataCite | `docs/BealExponent13_Iter_Package.md` locks none table. Not `∀ ℕ`. Ledger still v1.4.0. |
| v4.21.0-iter-zenodo-mint Typed ∧ Forall Zenodo mint | `v4.21.0-iter-zenodo-mint` / `bc450c6` | [10.5281/zenodo.22406482](https://doi.org/10.5281/zenodo.22406482) (DataCite `state: findable`; IsVersionOf concept [10.5281/zenodo.22272382](https://doi.org/10.5281/zenodo.22272382); GitHub–Zenodo parent [10.5281/zenodo.22379293](https://doi.org/10.5281/zenodo.22379293)) | Typed ∧ Forall none abstract minted. Not `∀ ℕ`. Ledger still v1.4.0. |

The corrected v1.0.1 theorem uses each signed S-unit in the finite-field
equation. It supersedes v1.0.0, whose Lean predicate indexed but did not use
that dimension; the accompanying strong-Hensel replay was already signed.

### v2.0.0 — Frey discriminant foundations

The Frey curve and its `c4`, `c6`, and discriminant identities are constructed
directly. `Conductor_26_Unconditional.lean` proves the odd-prime valuation
input `v_p(c4)=0` and `v_p(Δ)>0` from `p ∤ c4`, `p ∣ Δ`, and `Δ ≠ 0`, without
`frey_conductor_data` or `tate_step2_odd_prime_external`. Mathlib 4.12 has no
Kodaira-type or elliptic-conductor API, so the implication to type `I_n`,
conductor exponent one, and `N = 2^e * rad(ABC)` remains the explicit
Tate-classification boundary.

### v3.0.0 — Ribet level lowering

`LevelLowering_26` is typed certificate data: residual prime, weight two,
source/target levels, and the exact-divide relation. The arithmetic
`v_p(26 p) = 1` from `p ∤ 26` is proved in Mathlib 4.12. Mathlib has no
residual Frey representation, Hecke-algebra transport, or newform existence
theorem, so Ribet's existence statement remains the explicit
`RibetTheoremBoundary26`. This does not replace the parent supplier.

### v4.0.0 — Mazur endgame

Formalize the remaining Mazur chain:

```text
J₀(26)(ℚ) rank 0
  + formal immersion at 2
  ⇒ X₀(26)(ℚ) = four cusps
  ⇒ no level-26 Frey point
  ⇒ BealTheorem
```

v4.0.0-mazur packages that chain as `EndgameScaffold`. The four premises
are typed structures. `BealTheoremFromMazurChain26` concludes `BealTheorem`
only from those structures plus v2 Frey Weierstrass and v3
`LevelLowering_26`. Mathlib 4.12 has no Jacobian, Mordell--Weil, or
formal-immersion API, so rank, actual immersion, `X₀(26)(ℚ) = four cusps`,
and `R = T` remain explicit boundaries. A green scaffold build is not an
unconditional `BealTheorem`.

v4.0.1-jacobian-skeleton adds the finite `s₁ = q₁ + q₂`,
`s₂ = -q₁ q₂` model and the certified `26a × 26b` distinction
`a₂ = -1` versus `1`, and moves `PicardAbelJacobiIdentification_26`
to a standalone Jacobian file.

v4.0.2-selmer audits the eight S-unit indices against genuine
cohomological 2-Selmer. The finite audit retains all eight and is not
a singleton, so it is not mislabeled as a genuine 2-Selmer
calculation. `MwrankCertificateSoundness_26` here is that finite
package for `26a` and `26b`, not a Mordell--Weil theorem.

v4.0.3-formal-immersion inhabits `FormalImmersionAtTwo26` from
q-expansion cotangent injectivity: `M₃ = [[1, 1], [0, 2]]` has
`det = 2 ≠ 0`, so the cotangent map is injective over `ZMod 3`. That
can replace the formal-immersion *input* premise. It is not a
scheme-theoretic immersion.

v4.0.4-x026-rational-points inhabits `X0_26_RationalPoints26` from
the displayed four cusps `[1, 2, 13, 26]` together with that
already-decided q-expansion package. `ofRankZeroAndImmersion` returns
the finite Prop and does not read geometric rank. It is not a Mathlib
`X₀(26)(ℚ)` theorem.

v4.0.5-nofrey-point inhabited `NoFreyPoint26` from the displayed
lowering target `26` together with the v4.0.1 (`235a0bc`) → v4.0.2
(`c2f829d` / [10.5281/zenodo.22313148](https://doi.org/10.5281/zenodo.22313148))
→ v4.0.3 (`75c533d` / [10.5281/zenodo.22313241](https://doi.org/10.5281/zenodo.22313241))
→ v4.0.4 (`4619a5d` / [10.5281/zenodo.22313318](https://doi.org/10.5281/zenodo.22313318))
q-expansion chain. That made `hGeomForbid` the uninhabitable
`True → True → False`.

v4.0.6-rank-zero-fixed (this tag) splits that file: Ribet
existence stays in `RibetLoweringActual_26` as
`ExistsFreyWitness` (`loweredLevel = 26`);
`NoFreyPointActual_26` proves `¬ ExistsNoncuspidal` from the
four displayed cusps. `J0_26_Q_RankZeroActual_26` inhabits rank
zero as the product of two Sage-certified rank-zero factors,
without identifying eight S-units with genuine `Sel₂`.
`hGeomForbid` is now `fourCusps → ¬ ExistsNoncuspidal`.
`BealTheoremFromMazurChain26` still names
`hIdentify : ExistsFreyWitness → ExistsNoncuspidal`. v4.0.7-hIdentify
proves that *old* typed implication uninhabitable
(`hIdentify_typed_is_uninhabitable`): a displayed target `26` is a
listed cusp. v4.0.7-hIdentify-j retypes `ExistsNoncuspidal` as an
elliptic `j`, so typed `hIdentify` is the constructor packing
`HIdentify26.of_qExpansion`. Four cusp labels stay as cusps.
`hGeomForbid` (`fourCusps → ¬ ExistsNoncuspidal`) remains the
named geometric gate: that implication would put `False` in the
kernel if inhabited together with the new `hIdentify`.
v4.0.8-geom-forbid records that fact as
`hGeomForbid_typed_is_uninhabitable`. v4.0.9-fourCusps-forall
retypes four cusps as `fourCuspsForallCuspPoints` over
cusp-labeled points. That forall does not range over
`ellipticJ`, so typed `hGeomForbid` stays uninhabitable.
v4.0.10-chabauty0-no-doi adds `Mazur/Chabauty0Actual_26` as that
finite package; it coexists with `ExistsNoncuspidal` and is not
Chabauty--Coleman. v4.0.11-residue-disks-no-doi adds the `M₃`
residue-disk *input* and finite sieve conjunction; those are not
a scheme-theoretic `X₀(26)(ℚ)` theorem. v4.0.12-scheme-stub-no-doi
adds Jacobian-as-scheme and Abel--Jacobi named boundaries; those
are not a Mathlib Jacobian. v4.0.13-formal-immersion-proof-no-doi
names `det ≠ 0` as `formalImmersion_at_2_surjective_from_M3` and
aliases it as `diskEqualityFromImmersion`; that is not
surjectivity of a map of completed local rings.
v4.0.14-coleman-integral-no-doi names the rank-zero product as
`ColemanVanishesOnRankZero` and conjoins it with `det ≠ 0` as
`Chabauty0ForcesCusp`; that is not a Coleman integral and not a
Chabauty--Coleman theorem. v4.0.15-lmfdb-certs-no-doi records
archived LMFDB display fields; that is not unconditional rank
zero. v4.1.0-descent-start records certified Weierstrass
models. v4.1.1-descent-compute archives PARI `ellrank` /
`ell2cover` with displayed `|Sel₂| = 1`; Lean `SelmerBound_*`
are `1 = 1`, not a Selmer group and not unconditional
Mordell--Weil. v4.1.2-beal-13-endgame records
`rankZero_unconditional` from those equalities and inhabits
an `Option` `hGeomForbid` as that plus `det M₃ ≠ 0`. That is
a computational boundary, not typed
`fourCusps → ¬ ExistsNoncuspidal` and not a Lean
Mordell--Weil theorem. v4.1.3-beal-13-theorem inhabits a
computational `hGeomForbid` structure and names
`BealTheorem_Exponent13` for the `2 × 13` package; that is
not the Beal conjecture. Full `theorem BealTheorem` stays
guarded behind the four-cusp audit. v4.2.0-full-chain names `FreyLevel26` (`2 * 13 = 26`),
`X0_26_Q_four`, and `BealTheorem_Exponent13_Full_package`
as that computational conjunction; that is not
`∀ A B C, ¬ A^13+B^13=C^13`. v4.2.1-chabauty-closes-typed
names `hGeomForbid_typed_closed` as the Chabauty package plus
the cusp-point forall; typed `fourCusps → ¬ ExistsNoncuspidal`
stays uninhabitable. There is no unconditional
`BealTheorem`.

The detailed milestones, acceptance gates, and dependency order are in
[`PLAN.md`](PLAN.md).

## Repository layout

```text
.
├── README.md                    # this file: status, DOI trail, how to build
├── PLAN.md                      # v1–v4 unconditionalization plan and open gates
├── CITATION.cff                 # v1.0.1-computable citation record
├── .github/workflows/main.yml   # lake + verify-scaffold on github.com main
├── DOCKERFILE                   # Elan + Lean 4.12.0 + Mathlib verification image
├── certs/                       # v4.10.0 PARI four-cusp lock (SHA + [1,2,13,26])
├── docs/                        # versioned release notes (see docs/README.md)
│   └── releases/
├── lean/                        # Lean 4.12 sources (see lean/README.md)
│   ├── Beal/                    # Beal.Foundations certificate re-exports
│   └── BealLevel26Foundations/  # computable, scaffold, and real modules
│       ├── Frey/
│       ├── Jacobian/            # v4.0.1–v4.0.3 skeleton, Selmer audit, immersion input, v4.0.6 rank-zero product, v4.0.11 residue-disk input, v4.0.12 scheme boundary, v4.0.13 named det≠0 immersion, v4.0.14 named Coleman/Chabauty packages
│       ├── Certs/               # v4.0.15 LMFDB display; v4.1.1 Descent_26.json PARI 2-descent (not MW)
│       ├── Descent/             # certified Weierstrass models; displayed |Sel₂|=1 from PARI (not a Selmer group)
│       ├── Chain/               # v4.2.0 FreyLevel26 (2*13=26), X0_26_Q_four, v4.8.0 X0_26_Point_Raw
│       ├── Final/               # v4.7.0 Iter_Package + Iter_Typed_And_Package (not ∀ A B C)
│       ├── Mazur/               # genus arithmetic, endgame scaffold, v4.8.0 chain_secure
│       ├── Modularity/          # v4.8.0 frey_modular_13 + ribet_level_lowering_26 axioms
│       ├── Real/
│       └── Ribet/               # typed lowering; v4.0.6 split; v4.0.7-j finite j-invariant hIdentify
├── sagemath/                    # v1.4.0 ledger + SageMath 10.7 certs
│   └── certs/                   # j0_26_decomposition.json, formal_immersion_M3.json
├── scripts/                     # ledger, cert, Hensel, and scaffold checks
├── lakefile.lean                # three lake targets
└── lean-toolchain               # pinned leanprover/lean4:v4.12.0
```

Each of those directories has a `README.md` stating current contents and
the interpretation boundary. The initial Lean entrypoint intentionally
contains no `sorry`, `admit`, or domain axiom. New mathematical assumptions
belong in named theorem arguments until the corresponding release removes
them constructively.

## Verification

The workflow runs on pushes and pull requests:

```sh
lake exe cache get
lake build BealLevel26Foundations
lake build BealLevel26FoundationsScaffold
lake build BealLevel26FoundationsReal
bash scripts/verify-scaffold.sh
python3 scripts/verify_descent_26.py
```

The corrected v1.0.1-computable release uses Lean 4.12.0 to match the parent Beal project. The
workflow caches the pinned toolchain and Mathlib artifacts; it does not copy
the parent repository's `.lake` directory or silently import its theorem
boundaries.

A containerized replay of the same three Lake targets is in `DOCKERFILE`.
It installs Elan with no default toolchain, then follows `lean-toolchain`
(`leanprover/lean4:v4.12.0`) and Mathlib `v4.12.0`. Build with:

```sh
docker build -f DOCKERFILE -t beal-level-26-foundations .
docker run --rm beal-level-26-foundations
```

## Relationship to `beal-conjecture`

The repositories are companion works with different purposes:

- `beal-conjecture` keeps the conditionally complete theorem assembly and its
  exact five-premise audit in the archived v11.0.0 companion release
  ([DOI 10.5281/zenodo.22281075](https://doi.org/10.5281/zenodo.22281075));
- this repository independently checks the finite matrix and ledger evidence,
  then develops the missing cohomological and geometric comparisons in staged
  releases;
- migration back to the parent project is a later, explicit decision after a
  foundation is independently checked.

This separation prevents an unfinished unconditionalization effort from
changing the interpretation of the already-released conditional theorem.
Foundations v1 is unconditional computable foundations, archived separately
as a Zenodo companion. It does not claim that `decide` proves a genuine Selmer
singleton, and it does not claim an unconditional proof of the endgame.

## Citation

For the v4.0.9 cusp-point forall record, cite version DOI
[`10.5281/zenodo.22322627`](https://doi.org/10.5281/zenodo.22322627).
For the v4.0.8 typed-`hGeomForbid` record, cite version DOI
[`10.5281/zenodo.22314435`](https://doi.org/10.5281/zenodo.22314435).
For the v4.0.7-j finite `j`-invariant encoding, cite version DOI
[`10.5281/zenodo.22314212`](https://doi.org/10.5281/zenodo.22314212).
For the v4.0.7 typed-`hIdentify` record, cite version DOI
[`10.5281/zenodo.22314092`](https://doi.org/10.5281/zenodo.22314092).
For the v4.0.6 existence/absence split and product rank-zero
package, cite version DOI
[`10.5281/zenodo.22313955`](https://doi.org/10.5281/zenodo.22313955).
For the displayed Ribet-existence package,
cite version DOI
[`10.5281/zenodo.22313407`](https://doi.org/10.5281/zenodo.22313407).
For the displayed four-cusp package,
cite version DOI
[`10.5281/zenodo.22313318`](https://doi.org/10.5281/zenodo.22313318).
For q-expansion formal-immersion input,
cite version DOI
[`10.5281/zenodo.22313241`](https://doi.org/10.5281/zenodo.22313241).
For the S-unit audit versus genuine 2-Selmer,
cite version DOI
[`10.5281/zenodo.22313148`](https://doi.org/10.5281/zenodo.22313148).
For the Jacobian skeleton,
cite version DOI
[`10.5281/zenodo.22312844`](https://doi.org/10.5281/zenodo.22312844).
For the Mazur endgame scaffold,
cite version DOI
[`10.5281/zenodo.22311182`](https://doi.org/10.5281/zenodo.22311182).
For the typed `LevelLowering_26` certificate,
cite version DOI
[`10.5281/zenodo.22311107`](https://doi.org/10.5281/zenodo.22311107).
For the Frey Weierstrass model and odd-prime valuation input,
cite version DOI
[`10.5281/zenodo.22310825`](https://doi.org/10.5281/zenodo.22310825).
For the FormalImmersionM3 ledger match,
cite version DOI
[`10.5281/zenodo.22310574`](https://doi.org/10.5281/zenodo.22310574).
For the SageMath `J₀(26)` decomposition and `M₃` certificates,
cite version DOI
[`10.5281/zenodo.22310313`](https://doi.org/10.5281/zenodo.22310313).
For the finite formal-coordinate matrix calculation and unconditional
valuation input, cite
[`10.5281/zenodo.22286630`](https://doi.org/10.5281/zenodo.22286630).
For the corrected finite-only release, cite
[`10.5281/zenodo.22272714`](https://doi.org/10.5281/zenodo.22272714).
The stable DOI for the evolving Foundations project is
[`10.5281/zenodo.22272382`](https://doi.org/10.5281/zenodo.22272382).
Citation metadata is in [`CITATION.cff`](CITATION.cff), and the exact v1 claims
are recorded in
[`docs/releases/v1.0.1-computable.md`](docs/releases/v1.0.1-computable.md).
