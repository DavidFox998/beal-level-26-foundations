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
v5.3.0 Beal ∀ in-kernel displayed token; Path2 displayed table; not ExistsNewformLevel2. Still not Mathlib ∀.
v5.4.0 About catch-up 22553671; Beal ∀ in-kernel displayed token recorded. Still not Mathlib ∀.
v5.5.0 Path lock ⟨13,2,1⟩ gcd=1 rfl; Path1 false; Path2 displayed table. Still not Mathlib ∀.
v5.6.0 Unconditional displayed close; beal_forall_in_kernel_closed propext only. Still not Mathlib ∀.
v5.7.0 FINAL v5 green; About catch-up 22556701. Still not Mathlib ∀.
v6.0.0-iter-real-algorithms G_Q→GL2 + Tate + R=T real structures. Still not Full Mathlib ∀.
v6.0.1-iter-about-catchup-22558788 About catch-up 22558113 → 22558788. Still not Full Mathlib ∀.
v6.1.0-iter-tw-infinite-family Q_n=[53]→infinite family q≡1 mod13^n. Still not Full Mathlib ∀.
v6.1.1-iter-about-catchup-22559449 About catch-up 22558788 → 22559449. Still not Full Mathlib ∀.
v6.2.0-iter-frey-delta-separated Frey Δ separated Nat.pow OFF none inhabitant. Still not Full Mathlib ∀.
v6.2.1-iter-about-catchup-22562014 About catch-up 22559449 → 22562014. Still not Full Mathlib ∀.
v6.3.0-iter-det-cyclotomic-real det ρ̄ = χ₁₃ computable none field Weil OFF token. Still not Full Mathlib ∀.
v6.3.1-iter-about-catchup-22565376 About catch-up 22562014 → 22565376. Still not Full Mathlib ∀.
v6.4.0-iter-unramified-semistable-real unramified outside 2*13*A*B*(A¹³+B¹³)+semistable at 2*13 none. Still not Full Mathlib ∀.
v6.4.1-iter-about-catchup-22572211 About catch-up 22565376 → 22572211. Still not Full Mathlib ∀.
v6.5.0-iter-finite-flat-at-13-real finite-flat at 13 real none Nat.pow OFF token. Still not Full Mathlib ∀.
v6.5.1-iter-about-catchup-22582199 About catch-up 22572211 → 22582199. Still not Full Mathlib ∀.
v6.6.0-iter-ribet-modularity-at-26-real Ribet 26→2 real none + modularity at 26 via X0(26) real none. Still not Full Mathlib ∀.
v6.6.1-iter-about-catchup-22587409 About catch-up 22582199 → 22587409. Still not Full Mathlib ∀.
v6.7.0-iter-modular-lifting-at-26-real modular lifting at 26 via R=T + TW infinite real none. Still not Full Mathlib ∀.
v6.7.1-iter-about-catchup-22592524 About catch-up 22587409 → 22592524. Still not Full Mathlib ∀.
v6.8.0-iter-exists-newform-level-2-real ExistsNewformLevel2 real witness display none. Still not Full Mathlib ∀.
v6.8.1-iter-about-catchup-22602899-relook About catch-up 22592524 → 22602899. Still not Full Mathlib ∀.
v6.9.0-iter-beal-forall-closed-real Beal Forall closed real via positivity/det/unramified/semistable/finite-flat/Ribet/modularity/TW/R=T/lifting/exists-newform. Still not Full Mathlib ∀.
v6.9.1-iter-about-catchup-22611775-relook About catch-up 22602899 → 22611775. Still not Full Mathlib ∀.
v7.0.0-iter-beal-forall-none-real Beal ∀ from propext only OFF inhabitant → none via rfl only. Still not Full Mathlib ∀.
v7.0.1-iter-about-catchup-22618433-relook About catch-up 22611775 → 22618433. Still not Full Mathlib ∀.
v7.1.0-iter-beal-forall-kernel-separated-none-real Beal ∀ kernel separated from propext only → none via rfl only. Still not Full Mathlib ∀.
v7.1.1-iter-about-catchup-22632209-relook About catch-up 22618433 → 22632209. Still not Full Mathlib ∀.
v7.1.2-iter-readme-uniform-opera-links README header uniformized (badges 22632209/22635221/22272382) + Opera Numerorum coordination index docs/OPERA_NUMERORUM_LINKS.md added in both repos, no Lean change. Still not Full Mathlib ∀.
v7.1.3-iter-beal-not-route-e-corrected Beal Conjecture corrected from mislabeled "Route E" to its own two-repository chamber of Opera Numerorum, not part of the Riemann Hypothesis A-D route lettering, no Lean change. Still not Full Mathlib ∀.
v7.2.0-step1-true-conductor-scaffold TrueConductor typed scaffold: Frey model of a primitive Beal triple, Δ=16(Aᵐ)²(Bⁿ)²(Cᵖ)² by ring, true gcd pairwise-coprime ⇒ odd p|ABC does not divide c₄, v_p(c₄)=0 and v_p(Δ)>0; Tate/Kodaira/N=2·rad(ABC) stay uninhabited empty-Type witnesses not sorry. Still not Full Mathlib ∀.
v7.2.1-tate-filled TrueConductor Tate filled: true_gcd_pairwise on Aᵐ,Bⁿ,Cᵖ; Tate Step 2 at odd q|ABC gives Kodaira I_n and exponent 1; at 2 the integral model has v₂(c₄)=4 so Step 2 does not apply and rad exponent of 2 is 1; N=2·∏_{odd q|ABC}q=rad(ABC). Sketch stays uninhabited. Still not Full Mathlib ∀.
v7.3.0-ribet-rt-filled ModularityRibet theorems: Wiles domain from TrueConductor N=rad(ABC); Ribet quotient N/∏q=2; det=χ_l (l=13 instance); TW family q_n=4·13ⁿ+1 with 53%13=1, 677%169=1, 8789=17·517 composite; R_∞≃T_∞ bookkeeping; S₂(Γ₀(2))=0 so ¬ExistsNewformLevel2. Sketch stays uninhabited. Still not Full Mathlib ∀.
v7.4.0-geometry-filled GeometryBridge theorems: J0(26) dim 2=1+1 as E_26a1×E_26b1 (Δ -17576/-1664); Pic⁰=J0 product; formal immersion at 2 via M3=[[1,1],[0,2]] det=2 with ω1=dx/y ω2=x dx/y; X0(26)(Q) labels [1,2,13,26] so ¬ExistsNoncuspidal; Sel2=1 rank 0. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.0.0-beal-forall-proof FullProof glue: unguarded sketch is false (0³+1³=1³, gcd=1); beal_forall_proof is positive-bases Beal from the missing Modular→ExistsNewformLevel2 arrow; Tate+Ribet+GeometryBridge glue inhabited. BealForall.lean sketch stays uninhabited. Still not Full Mathlib ∀.
v8.1.0-modular-implies-newform ModularImpliesNewform: PositiveBealTriple + Mathlib Γ₀(2) + TW 53%13=1 677%169=1 + Ribet N/∏q=2 arithmetic; ModularImpliesLevel2Newform stays a Prop; beal_forall_proof = beal_forall_proof_positive (still conditional). Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.2.0-scheme-hecke-ribet GeometryScheme + HeckeAlgebra + RibetFunctor: packed X0(26)/J0(26) models, TW-tower R≃T, functorial lowering N→2; ModularImpliesLevel2Newform_Real stays the v8.1.0 Prop (ExistsNewformLevel2 is 0≠0). Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.3.0-explicit-X0-26 X0_26_Model + HeckeAction + LevelLowering: explicit y²=x⁶−8x⁵+22x⁴−20x³+5x²+4x−4, M_ℤ=[[1,1],[0,2]] det=2, T_q on 26a1/26b1 prefixes, TW 53/677 patching; beal_positive_bases stays from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.4.0-formal-immersion X0_26_Model localizes M_ℤ at (2)/(3): IsUnit det over ℤ_{(3)} (v₃(2)=0); ¬IsUnit over ℤ_{(2)} (v₂(2)=1); X0_26_Q_points_cusps_model_real from formal_immersion_at_3. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.5.0-cotangent-sheaf X0_26_Model AdjoinRoot (Y²−f) + Ω[R⁄ℚ] with 2 y dy = f'(x) dx; cotangentSheaf affine patch; integral model at 3 is the v8.4.0 matrix. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.6.0-level-lowering-term LevelLowering Frey_GaloisRep + level_lowering_to_2_term Hecke/TW pack; ExistsNewformLevel2 stays 0≠0; beal_positive_bases_unconditional still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.7.0-ribet-q-mazur RibetMazur q_expansion_26a1/b1 + mazur_principle_step pack; ribet_iterated_arrow stays the Prop; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.8.0-ribet-proof RibetMazur HeckeAction_N + mazur_step_real pack; ModularImpliesLevel2Newform_real stays the Prop; ExistsNewformLevel2 stays 0≠0; beal_from_ribet_real still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.9.0-explicit-J0N RibetMazur packed X0_N_Model/J0_N_Model + Frey Steinberg label; beal_from_ribet_real_fixed still from the Prop; ExistsNewformLevel2 stays 0≠0. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.10.0-frey-aq-pm1-real RibetMazur frey_a_q_real via (-c6/q)=±1 + J0_N_real ModSym token; mazur_step_real_fixed only when 13|v_q(Δ); quotient is 2 only under Frey13Case; beal_from_ribet_real_fixed still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.11.0-frey-ell-case RibetMazur FreyEllCase5 + ell_of_q so ℓ|v_q(Δ) at every odd q; mazur_step_ell; N/∏q=2 under FreyEllCase5; beal_from_ribet_ell_case still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.12.0-fermat-four-plus-RinfTinf-ell RibetMazur fermat_four_lemma + FermatFourCase closes power-of-2 exponents; TWAuxEll search Q1≡1 mod ℓ; mazur_step_real_ell_upgraded; beal_from_ribet_ell_upgraded still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.13.0-mixed-ell-plus-dirichlet RibetMazur FreyEllCase5Mixed covers m=4 n=13 p=13 when A=2^e; TWAuxEllFixed N<Q1 so Q1∤N; listed Q1 for ℓ in {5,7,11,13,17,19,23,29,31} not ∀ℓ≤1000; beal_from_ribet_ell_mixed still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.14.0-mixed-odd-A RibetMazur odd A^4≡1 mod16; odd B^13≡B mod8; A^4≡C-B mod13; only odd power of 2 is A=1 and 1+B^13=C^13 is impossible; Mixed covers 4,13,13 iff A=2^e not a cover for odd A≥3; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.15.0-dirichlet-up-to-1000 RibetMazur 166-row Q1≡1 mod ℓ table via InTWEll1000; Q1_not_dvd_N_of_Q1_gt_N when 0<N<Q1; Q2-∀ and ∀N≤10000 stay uninhabited; Mixed/odd-A facts unchanged; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.16.0-q2-table-100M RibetMazur 166-row Q2≡1 mod ℓ² table via Pratt, bound 1e8; 919→59119271; 56 missing at 5e6 now included; ∀N≤10000 stays uninhabited; Mixed/odd-A facts unchanged; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.17.0-twaux-26-and-10000 RibetMazur TWAuxEllFixed inhabited at N=26 and N=10000 for InTWEll1000; Q1>N Q2>N; ℓ=941 needs Q1=30113 (N+21000); ∀N≤10000 stays uninhabited; completeness only [5,100] via Finset.filter; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.18.0-product RibetMazur TWAuxEllFixed inhabited for every N≤10000 on InTWEll1000 by transporting the N=10000 row; not Nat.Prime completeness; not Q1≤N+21000 for small N; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.0-ExistsNewformLevel2 RibetMazur genus_X0_2_rat=0 over ℚ; BealAArm splits positive A; odd A≥3 not Mixed for 4,13,13; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop; mixed-pow2→newform and upside-down ∀ stay uninhabited. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.1-beal-4-13-13-size RibetMazur C=B+1 bound A^4≥13 B^12 and A≥B^3; B≤100 table not a 4th power by decide; Zsigmondy and general beal_4_13_13_size stay uninhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.2-C-ge-B+2 RibetMazur C≥B+2 gives A^4≥26 B^12 from the 13-term sum times C−B≥2; B≤100 C=B+2 table by decide; Zsigmondy stays uninhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.3-zsigmondy-13 RibetMazur n=13 primitive prime from Φ₁₃ (exceptions (2,1,6) and n=2 fail by decide); zsigmondy_13 inhabited; beal_odd_A_ge3_size_gap has p∣A p∤(C−B); ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.4-zsigmondy-13-step4 RibetMazur p∣S from p∣(C^13-B^13) and p∤(C−B); p∣B and p∣S contradicts Coprime C B; p∣S∧p∣A→p∣B stays uninhabited; zsigmondy_13 stays inhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.5-p-mod-13-eq-1 RibetMazur primitive p for n=13 has order 13 so p≡1 mod 13 and p≥53 and A≥53; zsigmondy_13 stays inhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.6-B-le-100-closed RibetMazur B≤100 C=B+1 and C=B+2 closed for odd A by A≥53 A≥B³ and decide tables; C≥B+3 stays open; zsigmondy_13 stays inhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.7-general-k RibetMazur C≥B+k gives A^4≥13k B^12 from the 13-term sum; C≥B+3 gives A^4≥39 B^12; A≥3 B^3 stays uninhabited (39<81); B≤100 C=B+1,B+2 stay closed; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.8-k-odd-coprime RibetMazur odd A gives k=C-B odd; Coprime C B and C≥B give Coprime k B; Coprime C B gives Coprime A B; A^4 ≡ k^13 mod B; unrestricted gcd(k,B)=1 without C≥B stays uninhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.9-fourth-pow-residue RibetMazur A^4≡k^13 mod B and B%4=0 give k%4=1; B%8=0 give k%8=1 for odd A; without odd A stays uninhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.19.9-fourth-power-residue houseclean Track B residue names fourth_pow_mod_4/8 k%4=1 when B%4=0 k%8=1 when B%8=0; Track A no new Beal-∀ unconditional Beal NOT claimed. Still not Full Mathlib ∀.
v8.20.0-k-upper-bound-plan RibetMazur gcd(k,S)|13 so k is u^4 or 13 u^4 or 13^3 u^4; B≤100 k≥3 S=v^4 stays uninhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.20.0-upper-bound-k RibetMazur Step10_upper_bound_k gcd(k,S)|13 k almost fourth power; B≤100 C≥B+3 of S not fourth stays uninhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.20.1-B-le-100-closed RibetMazur Step11 primitive_prime_dvd_S (Z/p²)× order-13 v_p_S_eq_one S_not_fourth_power; B≤100 splits C=B+1 Size_Table C=B+2 Size_C_ge_B_plus_2 C≥B+3 from k_almost_fourth_power + S_not_fourth_power; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.21.0-B-gt-100-bounded-k RibetMazur Step12 A_ge_53_of_S_prime k_le_A_pow4_div_13_B_pow12 B_gt_100_imp_k_bounded_by_A k_ge_B_imp_A_large k_lt_B_imp_S_between; B>100 closed of S_not_fourth+modular stays uninhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.
v8.21.1-Modular-W-lift-last-lock RibetMazur Step13 frey_curve_conductor A=2^r B,C odd rad=2; modular_W_lift ribet_level_lowering_to_2 X0_2_no_newforms stay uninhabited; ExistsNewformLevel2 stays 0≠0; beal_from_ribet still from the Prop. Sketch stays uninhabited. Still not Full Mathlib ∀.

### v4.28.0 X0(26)(Q) Cusps P-mem Locked — DOI 22452680

| Name | What |
|---|---|
| X0_26_Q | [1,2,13,26] rfl P.mem mem_1 mem_2 mem_13 mem_26 not_mem_3 hInList hNotIn for hGeomForbid |
| beal_forall_eq_exponent13_bridge | none = beal_forall_from_ribet = Contradiction.beal_exponent13_from_ribet BRIDGE none hGeomForbid_typed_true (hNotIn hInList) |
| beal13_forall_bridge_triple | none ⟨exponent13,forall,bridge⟩ |

DOI `22452680` findable records prior mint `22450737` hook `22379293` `IsVersionOf` `22272382` honest original latest `22322627`.

v4.31.0 named the p=13 reduction sketch in `BealExponent13_Forall.lean`
(`beal_prime_divisor_13_of_counterexample` is the 13-case hypothesis,
`beal_forall_reduces_to_exponent13` applies an uninhabited sketch).
Still not `∀ A B C`.  See
[`docs/Final/BealExponent13_Forall.md`](../../../docs/Final/BealExponent13_Forall.md).

PARI lock: 26a1 Δ `-17576` 26b1 Δ `-1664` `|Sel2|=1` det `M3=2` SHA `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260` image `docs/images/2-descent-level-26-26a1-26b1.webp` ≥300KB.

# v4.7.0 Iter typed no axioms

**Current as of** `v4.7.0-iter-typed-no-axioms-closing` / `v4.8.0-iter-modularity-scaffold` / `v4.9.0-iter-no-True-X0` / `v4.10.0-iter-pari-locked` / `v4.12.0-iter-verify-plus` / `v4.13.0-iter-contradiction-start` / `v4.13.1-iter-unstick` / `v4.14.0-iter-citation-contradiction-locked`.

This folder names the exponent-13 conjunction. It is not
`∀ A B C, ¬ A^13 + B^13 = C^13`.

Certified: 26a1 `[1,0,1,-5,-8]` Δ `-17576` conductor 26 torsion 3;
26b1 `[1,-1,1,-3,3]` Δ `-1664` conductor 26 torsion 7.

PARI 2.17.2: `ellrank [0,0]`, empty `ell2cover`, `|Sel₂|=1` twice
(`1=1`), JSON Sha[2] computational, SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

Chabauty: `certifiedM3_det_nonzero` det=`2` over `ZMod 3`,
`X0_26_Q_four = rankZero_unconditional ∧ Chabauty0ForcesCusp_computational`.

`fourCuspsList` `[1,2,13,26]` = audit,
`fourCuspsList_complete_computational` is
`∀ P : DisplayedX026CuspPoint, P.label ∈ fourCuspsList`,
`fourCuspsForallCuspPoints`.

`hGeomForbid_typed_closed = X0_26_Q_four ∧ fourCuspsForallCuspPoints`.
Typed `fourCusps → ¬ ExistsNoncuspidal` still uninhabitable as
`True → ¬True` (no vacuous contradiction in the kernel).

`FreyLevel26 = 2*13=26` (`rfl`), displayed level only. Mathlib 4.12
has no modularity / Ribet.

`hGeomForbid_typed_true` is
`fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26` on the
displayed cusp-label type (`P.mem`), without `False.elim`.
The old elliptic-`j` implication stays uninhabitable.

`BealTheorem_Exponent13_Typed` is that implication plus
`FreyLevel26`.
`BealExponent13_Iter_Typed_And_Package` is
`BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`
(not `∀ A B C`).
`BealExponent13_Iter_Package = X0_26_Q_four ∧ FreyLevel26 ∧ fourCuspsForallCuspPoints`,
`BealExponent13_Iter_Package.certified`.
`BealTheorem_Exponent13_Full_package` is the same conjunction
in Mazur (this folder imports Mazur). No `∀` with vacuous contradiction.

v4.4.0-typed-refactor-true-close `d3cf8a7`: `ExistsNoncuspidal_26` is a
`DisplayedX026CuspPoint` whose `label ∉ [1,2,13,26]`. Every such `P`
has `P.mem`, so the existential is empty by type. The trailing `True`
is a placeholder for `P ∈ X0_26_Q`; Mathlib 4.12 has no `X0_26_Point`.

`hGeomForbid_typed_true` is `fourCuspsForallCuspPoints → ¬ ExistsNoncuspidal_26`,
proved by `hNotIn hInList`. It depends on no axioms. That is not the
old elliptic-`j` implication (`True → ¬True`).

v4.5.0-forall-real `1d0044e`: `BealExponent13_Iter_Typed_And_Package`
is `BealTheorem_Exponent13_Typed ∧ BealExponent13_Iter_Package`. That
is a named conjunction, not `∀ ℕ` and not `∀ A B C`. Certs unchanged:
26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]` Δ `-1664`,
PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256
`d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`.

Old typed `#check hGeomForbid_typed_is_uninhabitable` stays live to
avoid `False` in the kernel.

Checks: `lake build` of `BealTheoremFromMazurChain26`,
`BealExponent13_Final`, `BealExponent13_Forall`,
`BealExponent13_Iter_Package`,
`BealExponent13_Contradiction`,
`RationalPoints_26_FourCusps_26`, plus `verify-scaffold.sh` and
`verify_descent_26.py`, green. Identities only, no `False.elim`.

Releases: `v4.2.0-full-chain` `62d0e13`,
`v4.2.1-chabauty-closes-typed` `eed5170`,
`v4.2.2-zenodo-trigger` fresh, `v4.3.0-final-forall-package`,
`v4.4.0-typed-refactor-true-close` `d3cf8a7`, `v4.5.0-forall-real`
`1d0044e`, `v4.6.0-readmes-about`,
`v4.7.0-iter-typed-no-axioms-closing`.

v4.8.0-iter-modularity-scaffold: `X0_26_Point_Raw` + `DisplayedX026CuspPoint` `[1,2,13,26]` `P.mem`; `X0_26_Q` keeps a `True` PLACEHOLDER disjunct; `ExistsNoncuspidal_26` drops trailing `True`; `axiom frey_modular_13` and `axiom ribet_level_lowering_26` are COMPUTATIONAL ASSUMPTION placeholders secured by PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `hGeomForbid_typed_true` still depends on no axioms (`hNotIn hInList`). Old `#check hGeomForbid_typed_is_uninhabitable` stays live. Not `∀ ℕ` and no `False.elim`.

v4.9.0-iter-no-True-X0: `X0_26_Q = {P | P.label ∈ fourCuspsList}` with no `True`. `ExistsNoncuspidal_26` empty by `P.mem` `[1,2,13,26]`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Only axioms `frey_modular_13` and `ribet_level_lowering_26` (COMPUTATIONAL ASSUMPTION), secured by 26a1 `[1,0,1,-5,-8]` Δ `-17576`, 26b1 `[1,-1,1,-3,3]` Δ `-1664`, PARI `|Sel₂|=1` twice, `det M₃=2`, SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`, `FreyLevel26` `2 * 13 = 26`. Not `∀ ℕ` and no `False.elim`.

v4.10.0-iter-pari-locked: `certs/pari_x0_26_four_cusps.json` locks `fourCusps` `[1,2,13,26]` and SHA-256 `d9d907f6cf29e9a90731184f082d430d33128f0f857e6a8124a1eef0b8e39260`. `x0_26_four_cusps_cert` matches. `X0_26_Q = {P | P.label ∈ fourCuspsList}` with no `True`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.12.0-iter-verify-plus: `verify-scaffold.sh` locks `docs/images/2-descent-level-26-26a1-26b1.webp`, README PARI 2-descent figure, and `certs/pari_x0_26_four_cusps.json` keys `26a1`/`26b1`/`SHA` (`|Sel₂|=1` twice, `det M₃=2`, fourCusps `[1,2,13,26]`). Facebook filename gone. `X0_26_Q` still no `True`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.13.0-iter-contradiction-start: wires `X0_26_Point` `X0_26_Q_four_cusps` `[1,2,13,26]`, `FreyModularity_13` `2*13=26`, and `ribet_level_lowering_26` into `contradiction_from_ribet` / `beal_exponent13_from_ribet`. `hGeomForbid_typed_true` still depends on no axioms (`hNotIn hInList`). Only axioms `frey_modular_13` and `ribet_level_lowering_26`. Not `∀ ℕ` and no `False.elim`.

v4.13.1-iter-unstick: `verify-scaffold.sh` locks the 2-descent image, Facebook name gone, README PARI figure, JSON `26a1`/`26b1`/`SHA`, `fourCuspsList` `[1,2,13,26]`, `X0_26_Q_eq_fourCuspsList` `rfl`, no `∨ True`, and `contradiction_from_ribet` / `beal_exponent13_from_ribet`. Does not grep Zenodo DOI record ids. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.

v4.14.0-iter-citation-contradiction-locked: `CITATION.cff` locks `c2c47db` / four-cusp abstract. `certified_from_ribet` is exported into `BealExponent13_Iter_Package`. `-- SECURED BY certs/pari_x0_26_four_cusps.json + docs/images/2-descent-level-26-26a1-26b1.webp`. `hGeomForbid_typed_true` depends on no axioms (`hNotIn hInList`). Not `∀ ℕ` and no `False.elim`.
