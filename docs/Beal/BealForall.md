# v4.49.0 Beal forall sketch from the 13-case

`lean/BealLevel26Foundations/Beal/BealForall.lean`

`beal_forall_from_Is13Case_sketch` is the Beal statement

`∀ A B C m n p, 2 < m,n,p → A^m+B^n=C^p → gcd(A,B,C) > 1`.

Valid type.  Uninhabited.

| Name | Status |
|---|---|
| `Is13CaseForcesFalseSketchViaLevel2` | `∀ w, Is13Case w → False` on bases; uninhabited; needs Tate + Ribet |
| `Is13CaseForcesGcdGt1Sketch` (this file) | `13 ∣ A*B*C → gcd > 1` on bases; uninhabited |
| `Is13CaseForcesGcdGt1Sketch` (Forall) | packed `w.gcd > 1`; uninhabited |
| `beal_forall_from_Is13Case_sketch` | `∀ A B C m n p` Beal; uninhabited; needs Tate + Ribet + GcdGt1 and levels `2p` for other primes |
| `beal_forall_from_Is13Case_composition` | the two 13-case sketches imply Beal; uninhabited (they do not) |

Real `X₀(26)(ℚ)` has `26a1` (Δ `-17576`) and `26b1`
(Δ `-1664`).  The 13-case contradiction is level 2, no
newform.  Still not `∀ A B C` in the kernel.

### v4.50.0 why GcdGt1 is uninhabited

`Is13Case_prime_dvd` (**none**): prime 13 divides one
factor of `A*B*C`.  `Is13Case_gcd_counterexample` is
`⟨13, 2, 1⟩` with `gcd = 1`.  So
`∀ w, Is13Case w → w.gcd > 1` is false on bases.
`not_Is13CaseForcesGcdGt1Sketch` records that (**none**,
`Nat.lt_irrefl`).  The packed Forall twin stays
uninhabited (`gcd = 1` by `primitive`).

### v4.51.0 gcd counterexample `rfl` + primitive vs not

`triple_13_2_1` is the named base `⟨13,2,1⟩`.
`gcd_13_2_1_eq_1` is `rfl` (**propext**).
`dvd_13_2_1` is **none**.
`Is13Case_gcd_counterexample_rfl` is
`∃ w, Is13Case w ∧ w.gcd = 1` (**propext**).
`primitive_vs_not_primitive` records that bases may be
primitive (`gcd = 1`) or not (`gcd > 1`).
`Is13Case` does not imply primitive.
Bases are not primitive-by-definition.
The packed twin stays uninhabited (`gcd = 1` by
`primitive` if that field is present).

### v4.52.0 primitive subtype: exists vs forall false

`IsPrimitive w := w.gcd = 1` is a derived Prop, not a
structure field.  `BealPrimitiveCounterexampleBases` is
`{w // IsPrimitive w}`.
`triple_13_2_1_primitive` is `rfl` (**propext**).
`exists_primitive_Is13Case_gcd_1` is
`∃ w` primitive `Is13Case w.val ∧ w.val.gcd = 1` (**propext**).
`forall_primitive_Is13Case_gcd_gt1_false` is
`¬ ∀ w` primitive `Is13Case → gcd > 1` (**propext**).
`Is13CaseForcesGcdGt1SketchPrimitive` stays uninhabited
and is now provably false, not just uninhabited.
`Is13Case → False` stays a valid type, uninhabited.

### v4.53.0 only honest path is False via level 2

Path 1 (`Is13Case → gcd > 1`) is false.
Path 2 (`Is13Case → False` via level 2) is the only
honest composition into Beal `∀`.
`beal_forall_from_Is13Case_false_sketch` is
`(∀ w, Is13Case w → False) → Beal ∀` (**propext** type eq).
Uninhabited.  Uses Path 2, not Path 1.  No `False.elim`.
`only_honest_path_is_False_via_level2` records Path 1
false and Path 2 as the typed `∀ w, Is13Case w → False`.

### v4.54.0 conditional Beal from Tate + Ribet

`is13Case_false_implies_Beal_of_tate_ribet_disc` takes
`hTate`, `hRibet`, Path 2 `hComp`, and Δ ≠ 0, and returns
Beal `∀`.  It builds a *local* `Is13Case → False` and does
**not** inhabit the unconditional sketch.
Axioms **propext** + existing `frey_modular_13`.
`is13Case_false_implies_Beal_of_tate_ribet_disc_type` is
the uninhabited `hTate → hRibet → Beal ∀`.

### v4.55.0 explicit Δ ≠ 0 and propext-only wiring

`frey_Delta13_ne_0_of_pos` is `∀ w, 0 < A → 0 < B → Δ ≠ 0`
on `Y² = X(X − A¹³)(X + B¹³)`.  Axioms **propext** +
`Classical.choice` + `Quot.sound`.
`is13Case_false_implies_Beal_of_tate_ribet_disc` still
takes explicit `hΔ` (propext + `frey_modular_13`).
`is13Case_false_implies_Beal_of_tate_ribet_disc_propext_only`
takes `hTate`, `hRibet`, and `hWeierstrass` as hypotheses
so `#print axioms` is **propext only**.
`hDelta_of_pos` feeds positivity into the existing Δ lemma.
Does **not** inhabit unconditional `Is13Case → False`.
No `False.elim`.

### v4.56.0 Mathlib gaps; propext-only is the ceiling

Both wirings stay.  `Chain.MathlibGaps` records Tate,
modularity, Ribet, and `X₀(26)(ℚ)` as missing from
Mathlib 4.12.  `notExistsNewformLevel2` **none** is the
DONE anchor.  The propext-only wiring is the ceiling
until those gaps close.  Uses Path 2, not Path 1.
No `False.elim`.

### v4.57.0-iter-phase5-X0-26-Q-honest-scaffold

Both Beal wirings stay as in v4.55.0 / v4.56.0.  This
slice builds out **Phase 5** `X₀(26)(ℚ)` as an honest
scaffold until Taylor–Wiles / BCDT.

- `X0_26_Q_Point` stays the **empty inductive** scaffold
  `Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26`.  It is
  **not** real `X₀(26)(ℚ)`.
- Real curve has four cusps (`1, 2, 13, 26`) **and**
  `26a1` (Δ `-17576`) and `26b1` (Δ `-1664`).  Reference
  list: `X0_26_Q_real_points` (`List String`, **none**).
- `fourCuspsForallCuspPoints_of_P_mem` is **none** via
  displayed `label ∈ [1, 2, 13, 26]`, **not** Mazur.
- `notExistsNoncuspidal_26_proved` is **none** via
  `hGeomForbid` **label check**, **not** Mazur `X₀(N)(ℚ)`
  classification.
- `X0_26_Q_Point_to_ExistsNoncuspidal` and
  `nonempty_X0_26_Q_Point_to_False` stay **uninhabited**
  (no vacuous empty-elim).
- `Chain.MathlibGaps` Phase 5 now states Mathlib 4.12
  lacks `X₀(N)(ℚ)` / Mazur.

Still not `∀ A B C` unconditionally.  Still not Mathlib
`X₀(26)(ℚ)` + Ribet + Tate.

### v4.58.0-iter-taylor-wiles-scaffold

Both Beal wirings stay.  New 10th module
`Chain.TaylorWilesScaffold` records `R = T`, Hecke,
deformation, `ρ̄_{E,13}`, lifting, and TW primes as
uninhabited scaffolds.  `HeckeAlgebra_26` is an empty
Type (**none**).  Ceiling stays
`is13Case_false_implies_Beal_of_tate_ribet_disc_propext_only`
(**propext only**).  Needs `R = T` + Ribet + Tate for
unconditional Beal `∀`.  Path 2 only honest.  No
`False.elim`.

Still not `∀ A B C` unconditionally.  Still not Mathlib
`X₀(26)(ℚ)` + Ribet + Tate + Taylor–Wiles.

