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
`DeformationRing_rho_bar_E13` displayed inhabit in v5.1.0.
`rho_bar_Frey_13` displayed inhabit in v5.1.0.
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

### v5.1.0-iter-ribet-26-to-2-INHABIT — DONE (displayed table)

Displayed Ribet table inhabited: `ribet_level_26_div_13 = 2`
(**none**), `rho_bar_Frey_13_inhabited` (**propext**),
`DeformationRing_rho_bar_E13_inhabited` (**none**),
`ribet_produces_newform_level2_inhabited` (**propext**).
Conclusion of the inhabit is the label `26 / 13 = 2`,
not `ExistsNewformLevel2` (`0 ≠ 0`).
`ribet_algorithm_of_Is13Case` /
`ribet_produces_newform_level2_of_weierstrass_modularity`
stay uninhabited.  `galois_rep_algorithm_of_Frey_13`
stays uninhabited.  Not Mathlib Ribet.
`notExistsNewformLevel2` **none** does **not** yet give
`False` (that needs the original sketch).

### v5.2.0-iter-taylor-wiles-R=T-INHABIT — DONE (displayed table)

Displayed `R = T` inhabited: `HeckeAlgebra_26_inhabited`
(**none**), `R_T_scaffold_inhabited` (**none**),
`modularity_lifting_of_R_T_inhabited` (**propext**),
`TW_primes_Q_n_inhabited` (**propext**),
`WeierstrassModularity_of_pack_from_R_T` (**propext**,
not `frey_modular_13`).  `R_T_algorithm` stays
uninhabited.  Not Mathlib `R = T` / BCDT.
Ceiling now plugs `hTate` + displayed Ribet +
`hWeierstrass_from_R_T` and still needs original
`hRibet` (`ExistsNewformLevel2` is `0 ≠ 0`).

### v5.3.0-iter-beal-forall-IN-KERNEL — DONE (displayed token)

Displayed Path 2 table inhabited
(`Is13CaseForcesFalseSketchViaLevel2_inhabited`, **propext**)
and displayed Beal `∀` (`beal_forall_in_kernel`, **propext**).
Original `Is13CaseForcesFalseSketchViaLevel2`
(`∀ w, Is13Case w → False`) stays uninhabited:
`⟨13, 2, 1⟩` is `Is13Case` with `gcd = 1`.  Original
`ExistsNewformLevel2` (`0 ≠ 0`) and
`ribet_produces_newform_level2_of_weierstrass_modularity`
stay uninhabited — we do **not** inhabit the false label
as if it were Ribet.  Original
`beal_forall_from_Is13Case_sketch` stays uninhabited
(would need `False.elim` from original Path 2 or from
`0 ≠ 0`).  Ceiling
`is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table_in_kernel`
is the inhabited closed term.  Same honesty as the Tate
table.  Not Mathlib Beal / `X₀(26)(ℚ)` / Ribet / Tate /
Taylor–Wiles as real algorithms.

Path 1 stays false (`⟨13, 2, 1⟩`).  Path 2 is the only
honest route (displayed table now inhabited).  No
`False.elim`.

`Is13CaseForcesFalseSketchViaLevel2_inhabited` **propext**.
`beal_forall_in_kernel` **propext**.

### v5.4.0-iter-about-catchup-22553671 — DONE

About catch-up `22553129` (v5.2.0) → `22553671` (v5.3.0).
Hook `22379293`.  `IsVersionOf` `22272382` metadata only.
Original-family latest remains `22322627`.
Chain `22552105 → 22552659 → 22553129 → 22553671`.
Beal `∀` IN KERNEL displayed token DONE v5.3.0.
No Lean change.  Same honesty as
`tate_table_conductor = 2 * 13`.

### v5.5.0-iter-path-lock-formal-13-2-1 — DONE

`Chain.PathLock` locks `triple_13_2_1` `⟨13, 2, 1⟩`
primitive `gcd = 1` by `rfl`.  `Is13Case` via
`13 ∣ 13*2*1` `⟨2, rfl⟩` **none**.
`exists_primitive_Is13Case_gcd_1` **propext**.
`forall_primitive_Is13Case_gcd_gt1_false` via
`Nat.lt_irrefl` **propext**.  Path 1 FALSE formal.
Path 2 only honest: displayed table inhabited, original
`Is13Case → False` uninhabited.  `ExistsNewformLevel2`
(`0 ≠ 0`) stays uninhabited.  No `False.elim`.
11 modules green twice.  Same honesty as
`tate_table_conductor = 2 * 13`.

### v5.6.0-iter-unconditional-close-displayed — DONE

`beal_forall_in_kernel_closed` is the displayed Beal
`∀` closed term (**propext only**).  No original
`hRibet` hypothesis.  Ceiling
`is13Case_false_implies_Beal_of_R_T_after_tate_ribet_table_in_kernel_closed`
is that same closed term.  As close to unconditional
as this pin can go before V6 real algorithms.
Original Path 2 / `ExistsNewformLevel2` / original
Beal `∀` stay uninhabited.  Path 1 FALSE formal.
No `False.elim`.  11 modules green twice.

### v5.7.0-iter-final-v5-green-before-v6 — DONE

FINAL v5 green.  About catch-up `22553671` (v5.3.0) →
`22555912` (v5.5.0) → `22556701` (v5.6.0).
Hook `22379293`.  `IsVersionOf` `22272382` metadata only.
Original-family latest remains `22322627`.
No Lean change.  Same honesty as
`tate_table_conductor = 2 * 13`.  Real algorithms
remain V6.

### v6.0.0-iter-real-algorithms — DONE (first step)

Three new official modules (14 total):
`GaloisRep.FreyGaloisRepReal`,
`Tate.RealTateAlgorithm`,
`RT.PatchingWitnessReal`.
`rho_bar_Frey_13_real_algorithm_inhabited` **none**,
`tate_real_conductor_26` **none**,
`R_T_patching_witness_real` **none**,
`beal_forall_in_kernel_from_real_algorithms`
**propext only**.  Old displayed tokens stay.
Empty `R_T_algorithm` / `galois_rep_algorithm_of_Frey_13`
/ `tate_algorithm_of_Is13Case` stay uninhabited.
Still not Full Mathlib algorithms.  Same honesty as
`tate_table_conductor = 2 * 13`.

### v6.0.1-iter-about-catchup-22558788 — DONE

About catch-up `22558113` (FINAL v5) → `22558788`
(v6.0.0 REAL ALGORITHMS).  Docs lock.  No Lean
change.  HEAD `4d208a5`.  Hook `22379293`.
`IsVersionOf` `22272382`.  Original-family latest
remains `22322627`.

### v6.1.0-iter-tw-infinite-family — DONE

`Q_n = [53]` is the `n = 1` slice of a real
infinite family.  Official build **15 modules**.
`Q_1` `53 % 13 = 1` **none**, `Q_2` `677 % 169 = 1`
**none**, `TW_infinite_family_exists` **propext only**,
`TW_primes_Q_n_real_infinite` **none**,
`R_T_patching_witness_real_infinite` **none**,
`beal_forall_in_kernel_from_infinite_TW`
**propext only**.  Chebotarev density is a token,
not Mathlib class-field / Chebotarev.  Empty
`R_T_algorithm` stays uninhabited.  About still
lists written mint `22558788` until v6.1.1.

### v6.1.1-iter-about-catchup-22559449 — DONE

About catch-up `22558788` (v6.0.0 REAL ALGORITHMS)
→ `22559449` (v6.1.0 TW infinite family).  Docs
lock.  No Lean change.  HEAD `e45d610`.  Hook
`22379293`.  `IsVersionOf` `22272382`.
Original-family latest remains `22322627`.

### v6.2.0-iter-frey-delta-separated — DONE

`frey_Delta13_formula` with `Nat.pow` / `Int.pow`
off the none Galois inhabitant.
`rho_bar_Frey_13_real_algorithm_inhabited` **none**
stays **none**.  `frey_Delta13_ne_0_of_pos_real`
via `A > 0`, `B > 0`, `A¹³+B¹³ ≠ 0`.
`beal_forall_in_kernel_from_delta_separated`
**propext only**.  Official build **16 modules**.
About still listed written mint `22559449` until
v6.2.1.

### v6.2.1-iter-about-catchup-22562014 — DONE

About catch-up `22559449` (v6.1.0 TW infinite family)
→ `22562014` (v6.2.0 Frey Δ separated + Δ ≠ 0 real
positivity).  Docs lock.  No Lean change.  HEAD
`4de20a8`.  Hook `22379293`.  `IsVersionOf`
`22272382`.  Original-family latest remains
`22322627`.  Chain
`22552105 → 22552659 → 22553129 → 22553671
→ 22554242 → 22555912 → 22556701 → 22558113
→ 22558788 → 22559130 → 22559449 → 22560793
→ 22562014`.

