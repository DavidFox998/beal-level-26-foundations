# ROADMAP to `∀ A B C` in kernel without Mathlib — we finish it for them

Pin Lean 4.12.0 + Mathlib v4.12.0, but we do not wait.
Mathlib lacks Tate, Ribet, and `R = T`.  We provide them
in later slices.  This file is a lock, not an inhabitant.

Still not `∀ A B C` unconditionally.  Still not Mathlib
`X₀(26)(ℚ)` + Ribet + Tate + Taylor–Wiles.  No `False.elim`.

## DONE

### v4.57.0 Phase 5 `X₀(26)(ℚ)` honest scaffold — DONE

`X0_26_Q_Point` is
`Σ (E : EllipticCurve ℚ), CyclicSubgroup E 26`, an empty
inductive, **not** the real curve.
`X0_26_Q_real_points` is a `List String` (**none**):
`["cusp_1", "cusp_2", "cusp_13", "cusp_26",
"26a1 Δ -17576", "26b1 Δ -1664"]`.
`fourCuspsForallCuspPoints_of_P_mem` is **none** via
`label ∈ [1, 2, 13, 26]`, **not** Mazur.
`notExistsNoncuspidal_26_proved` is **none** via
`hGeomForbid` label check, **not** Mazur.
`X0_26_Q_Point_to_ExistsNoncuspidal` stays uninhabited
(no vacuous empty-elim).

### v4.58.0 Taylor–Wiles scaffold — DONE

`R_T_scaffold` uninhabited.
`HeckeAlgebra_26` empty Type (**none**).
`DeformationRing_rho_bar_E13` uninhabited.
`rho_bar_Frey_13` uninhabited.
`modularity_lifting_of_R_T` uninhabited.
`TW_primes_Q_n` uninhabited.
`WeierstrassModularity_of_pack` **propext** + existing
`frey_modular_13`, not BCDT.
Ceiling
`is13Case_false_implies_Beal_of_tate_ribet_disc_propext_only`
is **propext only**.

### v4.59.0 About + ROADMAP catch-up — DONE

About records mint `22551298` (v4.58.0) and the chain
`22550229 → 22550771 → 22551051 → 22551298`.
This file locks the v5 inhabit plan.

### v5.0.0-iter-tate-conductor-26-INHABIT — DONE (displayed table)

Displayed Tate table inhabited: `tate_f_2 = 1`,
`tate_f_13 = 1`, multiplicative at 2 and 13,
`tate_table_conductor = 2 * 13` (**none**).
`tate_conductor_26_of_Is13Case_proof` inhabited
(Δ ≠ 0 from `0 < A`, `0 < B` + table).
`frey_conductor_26_of_Is13Case_inhabited` fills `hTate`
via the table + label (**propext**).
`frey_conductor_26_rfl` stays **none**.
`tate_algorithm_of_Is13Case` stays uninhabited
(no Mathlib `v_p(Δ)` / Kodaira).
Not Mathlib Tate.  `Is13Case` does not imply `2 ∣ A*B*C`.

## PLANNED — we finish it for them

### v5.1.0-iter-ribet-26-to-2-INHABIT

Inhabit `ribet_produces_newform_level2`:
`ρ̄_{E,13}` irreducible, finite at 13, level lowers
`26 → 2`.  Then `notExistsNewformLevel2` **none** via
`S₂(Γ₀(2)) = 0` dim-0 anchor gives `False`.

### v5.2.0-iter-taylor-wiles-R=T-INHABIT

Inhabit `R_T_scaffold`
(`DeformationRing ≃ HeckeAlgebra_26`),
Gorenstein + complete intersection on
`HeckeAlgebra_26`, `modularity_lifting_of_R_T`, and
`TW_primes_Q_n` existence.  Then inhabit
`WeierstrassModularity_of_pack` from `R = T`, **not**
via the existing `frey_modular_13` assumption.
Target `#print axioms` **none** or **propext only**.

### v5.3.0-iter-beal-forall-IN-KERNEL

Compose `is13Case_implies_False_of_tate_ribet_disc`
with inhabited `hTate`, `hRibet`, `hWeierstrass`,
`hDelta` so `∀ w, Is13Case w → False` is inhabited.
Then `beal_forall_from_Is13Case_false_sketch` gives
Beal `∀ A B C m n p, 2 < m,n,p → A^m+B^n=C^p → gcd > 1`
inhabited in the kernel.
`#print axioms` may still include `propext` (and
whatever the Tate / Ribet / `R = T` slices use), but
the type is no longer uninhabited.
Beal `∀` in kernel.  `BealLevel26Foundations` DONE.

We do not need Mathlib.  We will finish it out for them.

Until v5.3.0: still not `∀ A B C` unconditionally.
Path 1 stays false (`⟨13, 2, 1⟩`).  Path 2 stays the
only honest `Is13Case → False` type.  No `False.elim`.
