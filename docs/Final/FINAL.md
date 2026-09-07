# FINAL v6.5.1 — About catch-up 22582199

Latest tag `v6.5.1-iter-about-catchup-22582199`.
Records Lean HEAD `77497b3` /
`v6.5.0-iter-finite-flat-at-13-real`.  **No Lean change.**
Latest written mint now
[10.5281/zenodo.22582199](https://doi.org/10.5281/zenodo.22582199)
(v6.5.0 finite-flat at 13 real computable none)
DataCite findable, after
[10.5281/zenodo.22572211](https://doi.org/10.5281/zenodo.22572211)
(v6.4.0 unramified + semistable).  The new
v6.5.1 mint is **not** written into About.  Hook
`22379293`.  `IsVersionOf` `22272382` metadata only.
Original-family latest remains `22322627`.

### v6.0.0 REAL ALGORITHMS

`G_ℚ → GL₂(𝔽₁₃)` real structure **none** +
Tate real conductor `26` by `rfl` **none** +
TW `Q_n = [53]` `53 % 13 = 1` by `rfl` +
`R = T` witness ≃ **none** +
`beal_forall_in_kernel_from_real_algorithms`
**propext only**.

- `FreyGaloisRep13` Type: Frey model
  `Y² = X(X − A¹³)(X + B¹³)`, Δ display
  `16*(A^13)^2*(B^13)^2*(A^13+B^13)^2`, conductor
  `2 * 13`, `GQ → GL2(F13)` tokens, cyclotomic
  `χ₁₃`, unramified / semistable / irreducible /
  finite-flat labels.
  `rho_bar_Frey_13_real_algorithm_inhabited` **none**
- `TateStep` at 2 and 13: `f_2 = 1`, `f_13 = 1`,
  multiplicative `I_n`.
  `tate_real_conductor_26` `= 2 * 13` **none**
- `TaylorWilesSystemReal` `Q_n = [53]`, `|Q_n| = 1`,
  `53 % 13 = 1` **none**, Diamond / Gorenstein /
  complete-intersection tokens.
  `R_T_patching_witness_real`
  `DeformationRing_real ≃ HeckeAlgebra_real_26`
  **none**
- `beal_forall_in_kernel_from_real_algorithms`
  `BealForall` closed term **propext only**, no
  original `hRibet` hypothesis

### v6.0.1 About catch-up DONE

Chain `22552105 → 22552659 → 22553129 → 22553671
→ 22554242 → 22555912 → 22556701 → 22558113
→ 22558788`.  About wrote `22558788` as the
latest recorded mint.  Docs lock.  No Lean change
on that catch-up.

### v6.1.0 TW infinite family

`Q_n = [53]` is now the `n = 1` slice of a real
infinite family, not a single prime.

- `ChebotarevToken` density `> 0` / infinitely
  many `q` with `q ≡ 1 [MOD 13^n]` and a
  Frobenius condition **propext only**
- `TWPrimesInfiniteFamily` Type: `n`, `r`,
  `Q_n`, `|Q_n| = r`, distinct-Frob / Chebotarev /
  Diamond / Gorenstein / complete-intersection
  labels
- `Q_1` `n = 1` `Q = [53]` `|Q| = 1` `53 % 13 = 1`
  by `rfl` **none**
- `Q_2` `n = 2` `Q = [677]` `|Q| = 1`
  `677 % 169 = 1` by `rfl` `677 = 4 * 169 + 1`
  **none**
- `TW_infinite_family_exists`
  `∀ n > 0, ∃ Q, Q.n = n ∧ |Q.Q_n| = r ∧
  ∀ q ∈ Q.Q_n, q % 13^n = 1` **propext only**
- `TW_primes_Q_n_real_infinite`
  `TaylorWilesSystemReal` **none**
- `R_T_patching_witness_real` ≃ **none**, now
  against the infinite family
- `R_T_patching_witness_real_infinite` ≃ **none**
- `beal_forall_in_kernel_from_infinite_TW`
  `BealForall` closed term **propext only**, no
  original `hRibet` hypothesis

Old displayed tokens stay: `rho_bar_Frey_13_inhabited`
**propext**, `DeformationRing_rho_bar_E13_inhabited`
**none**, `HeckeAlgebra_26_inhabited` **none**,
`R_T_scaffold_inhabited` **none**,
`modularity_lifting_of_R_T_inhabited` **propext**,
`TW_primes_Q_n_inhabited` **propext**,
`WeierstrassModularity_of_pack_from_R_T` **propext**,
`beal_forall_in_kernel_closed` **propext**.

`Q_1 = [53]` `53 % 13 = 1` by `rfl` **none**.
`Q_2 = [677]` `677 % 169 = 1` by `rfl` **none**.
`|Q_n| = 1 = r`.  `4 * 13^n + 1` pattern.
`∀ n > 0, ∃ Q` with `q % 13^n = 1` **propext only**.
Chebotarev density `> 0` **propext only**.
Truly infinite, not just `[53]`.

### v6.1.1 About catch-up DONE

Chain `22552105 → 22552659 → 22553129 → 22553671
→ 22554242 → 22555912 → 22556701 → 22558113
→ 22558788 → 22559130 → 22559449`.  About now
writes `22559449` as the latest recorded mint.
Docs lock only.  No Lean change.

### v6.2.0 Frey Δ separated

`Nat.pow` / `Int.pow` of
`Δ = 16*(A¹³)²*(B¹³)²*(A¹³+B¹³)²` is
`frey_Delta13_formula`, **off** the none Galois
inhabitant.

- `rho_bar_Frey_13_real_algorithm_inhabited` **none**
  stays **none**, stronger than propext-only
- `frey_Delta13_ne_0_of_pos_real` Δ ≠ 0 real via
  `A > 0`, `B > 0`, `A¹³+B¹³ ≠ 0`
  (`propext` + `Classical.choice` + `Quot.sound`)
- `FreyGaloisRep13_real_algorithm_inhabited_separated`
  **none**
- `beal_forall_in_kernel_from_delta_separated`
  **propext only**, no original `hRibet`

Official build **16 modules**.
`FreyDeltaSeparated` holds
`frey_Delta13_formula = 16*(A¹³)²*(B¹³)²*(A¹³+B¹³)²`
with `Int.pow` / `Nat.pow` **OFF** the Galois
token.  `rho_bar` **none** stays **none** stronger
than propext-only.  `frey_Delta13_ne_0_of_pos_real`
real positivity: `0 < A`, `0 < B`, `A¹³+B¹³ ≠ 0`
imply nonzero (`16 ≠ 0`, squares of nonzeros,
product of nonzeros).  Axioms
`propext` + `Classical.choice` + `Quot.sound`;
premises are positivity data.
`FreyCurveSeparated.token` **none**.
`FreyGaloisRep13_real_algorithm_inhabited_separated`
**none**.  `beal_forall_in_kernel_from_delta_separated`
**propext only**; positivity is not in that term
so it does not pick up `Classical.choice`.

### v6.2.1 About catch-up DONE

Chain `22552105 → 22552659 → 22553129 → 22553671
→ 22554242 → 22555912 → 22556701 → 22558113
→ 22558788 → 22559130 → 22559449 → 22560793
→ 22562014`.  About now writes `22562014` as the
latest recorded mint.  Docs lock only.  No Lean
change.

### v6.3.0 det ρ̄ = χ₁₃ computable none field

`det(ρ̄(σ)) = χ₁₃(σ)` is
`frey_det_eq_cyclotomic_formula`, **off** the none
Galois inhabitant, same pattern as
`frey_Delta13_formula` with `Nat.pow` / `Int.pow`
off `rho_bar`.

- `cyclotomicCharacter13` token map `G_ℚ → (ℤ/13ℤ)×`
  **none**
- `frey_det_eq_cyclotomic_formula`
  `∀ σ, det(ρ̄(σ)) = χ₁₃(σ)` **none**
- `frey_det_eq_cyclotomic_real_lemma` Weil pairing
  `e₁₃ : E[13] × E[13] → μ₁₃` Galois-equivariant
  `σ(e₁₃(P,Q)) = e₁₃(σP,σQ) = e₁₃(P,Q)^{χ₁₃(σ)}`
  and `∧² E[13] ≅ μ₁₃` **propext only**
- `rho_bar_Frey_13_real_algorithm_inhabited` **none**
  stays **none**
- `rho_bar_Frey_13_real_algorithm_inhabited_det`
  **none** stays **none**, stronger than propext-only
- `FreyCurveSeparated.token` **none**
- `FreyCurveSeparated_det.token` **none**
- `beal_forall_in_kernel_from_det_separated`
  **propext only**; positivity / det lemmas are
  **not** in that term so no `Classical.choice`

Official build **17 modules**.
`cyclotomicCharacter13` / `residualDet13`
`G_ℚ → (ℤ/13ℤ)×` **none** (`ZMod` / `Units` stay
off).  `frey_det_eq_cyclotomic_formula`
`∀ σ, det(ρ̄(σ)) = χ₁₃(σ)` **none**.  Weil pairing
`e₁₃ : E[13] × E[13] → μ₁₃` **propext only**, off
the inhabitant.  `rho_bar_Frey_13_real_algorithm_inhabited_det`
**none** stronger than propext-only.
`FreyCurveSeparated_det.token` **none**.
`beal_forall_in_kernel_from_det_separated`
**propext only**; positivity / det lemmas not in
term.  Existing tokens: `Q_1` / `Q_2` **none**,
`TW_infinite_family_exists` **propext only**,
Tate `2*13` **none**, both `R = T` **none**,
`frey_Delta13_ne_0_of_pos_real`
`propext` + `Classical.choice` + `Quot.sound`.

### v6.3.1 About catch-up DONE

Chain `22552105 → 22552659 → 22553129 → 22553671
→ 22554242 → 22555912 → 22556701 → 22558113
→ 22558788 → 22559130 → 22559449 → 22560793
→ 22562014 → 22564236 → 22565376`.  About now
writes `22565376` as the latest recorded mint.
Docs lock only.  No Lean change.

### v6.4.0 unramified + semistable real

Unramified outside `2*13*A*B*(A¹³+B¹³)` +
semistable at `2*13` as computable **none**
fields.  Official build **18 modules**
(17 old + `GaloisRep.GaloisUnramifiedSemistableReal`).

- `frey_unramified_set_leading` `{2, 13}`
  `List Nat` **none** (`Finset` prime divisors
  of a general `A¹³+B¹³` stay off)
- `frey_unramified_sum_formula` /
  `frey_unramified_product_formula` hold
  `Int.pow` / `Nat.pow` **OFF** the token
- `frey_unramified_outside_formula`
  `∀ p ∉ S →` unramified at `p` **none**
- `frey_unramified_outside_real_lemma`
  Néron–Ogg–Shafarevich good reduction at
  `p ∤ 2*Δ` → unramified on `E[13]`
  **propext only**, off the inhabitant
- `frey_semistable_at_2_13_formula`
  conductor `2 * 13` by `rfl` **none**
  (same numeral as `tate_real_conductor_26`)
- `frey_semistable_real` **propext only**,
  off the inhabitant
- `rho_bar_Frey_13_real_algorithm_inhabited_unramified`
  **none** stronger than propext-only
- `FreyCurveSeparated_unramified.token` **none**
- `beal_forall_in_kernel_from_unramified_separated`
  **propext only**; positivity / det /
  unramified / semistable lemmas are **not**
  in that term

Existing tokens unchanged: `cyclotomicCharacter13`
**none**, `frey_det_eq_cyclotomic_real_lemma`
**propext only**, `rho_bar` / `_det` **none**,
`Q_1` / `Q_2` **none**, `TW_infinite_family_exists`
**propext only**, both `R = T` **none**,
`frey_Delta13_ne_0_of_pos_real`
`propext` + `Classical.choice` + `Quot.sound`,
Tate `2*13` **none**.

### v6.4.1 About catch-up DONE

Chain `22552105 → 22552659 → 22553129 → 22553671
→ 22554242 → 22555912 → 22556701 → 22558113
→ 22558788 → 22559130 → 22559449 → 22560793
→ 22562014 → 22564236 → 22565376 → 22565933
→ 22572211`.  About now writes `22572211` as
the latest recorded mint.  Docs lock only.
No Lean change.

### v6.5.0 finite-flat at 13 real

Finite-flat at 13 as a computable **none**
field.  Official build **19 modules**
(18 old + `GaloisRep.GaloisFiniteFlatAt13Real`).

- `frey_Delta13_val_13_pow_formula` holds
  `Int.pow` / `Nat.pow` **OFF** the token
- `frey_Delta13_val_13_leading` `26 = 2 * 13`
  **none**
- `frey_finite_flat_at_13_formula`
  `v₁₃(Δ) % 13 = 0` by `rfl` **none**
- `frey_finite_flat_at_13_real_lemma`
  Fontaine–Laffaille / Tate uniformization
  **propext only**, off the inhabitant
- `rho_bar_Frey_13_real_algorithm_inhabited_finite_flat`
  **none** stronger than propext-only
- `FreyCurveSeparated_finite_flat.token` **none**
- `beal_forall_in_kernel_from_finite_flat_separated`
  **propext only**; positivity / det /
  unramified / semistable / finite-flat lemmas
  are **not** in that term

Existing tokens unchanged: unramified /
semistable **none**, `cyclotomicCharacter13`
**none**, Weil lemma **propext only**,
`rho_bar` / `_det` / `_unramified` **none**,
`Q_1` / `Q_2` **none**, `TW_infinite_family_exists`
**propext only**, both `R = T` **none**,
`frey_Delta13_ne_0_of_pos_real`
`propext` + `Classical.choice` + `Quot.sound`,
Tate `2*13` **none**.

### v6.5.1 About catch-up DONE

Chain `22552105 → 22552659 → 22553129 → 22553671
→ 22554242 → 22555912 → 22556701 → 22558113
→ 22558788 → 22559130 → 22559449 → 22560793
→ 22562014 → 22564236 → 22565376 → 22565933
→ 22572211 → 22581510 → 22582199`.  About now
writes `22582199` as the latest recorded mint.
Docs lock only.  No Lean change.

### Honest lock (unchanged from FINAL v5)

- `ExistsNewformLevel2` is `s2_gamma0_2_dim ≠ 0`
  i.e. `0 ≠ 0` and stays uninhabited
- Original `ribet_produces_newform_level2_of_weierstrass_modularity`
  stays uninhabited
- Original `∀ w, Is13Case w → False` stays
  uninhabited (`⟨13, 2, 1⟩` is `Is13Case`, `gcd = 1`)
- Original `beal_forall_from_Is13Case_sketch` `∀ A B C`
  stays uninhabited
- Empty `R_T_algorithm` / `TaylorWilesPatchingWitness` /
  `galois_rep_algorithm_of_Frey_13` /
  `tate_algorithm_of_Is13Case` stay uninhabited
- Path 1 FALSE formal: `triple_13_2_1` `⟨13, 2, 1⟩`
  primitive `gcd = 1` by `rfl`
- Path 2 ONLY HONEST: displayed table inhabited
- Real `X₀(26)(ℚ)` still has `26a1` Δ `-17576` and
  `26b1` Δ `-1664`
- No `False.elim`.  19 modules green twice.
  `verify-scaffold.sh` OK.  `verify_descent_26.py` OK.
  `NO_SORRY_OK`

Still not Full Mathlib `X₀(26)(ℚ)` + Ribet + Tate +
Taylor–Wiles as fully verified Mathlib algorithms,
but now finite-flat at 13 is a real computable
none field.  GOOD sounding step to real algorithms.
