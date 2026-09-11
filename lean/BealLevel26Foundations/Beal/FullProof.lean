import BealLevel26Foundations.Beal.FullProof.TrueConductor
import BealLevel26Foundations.Beal.FullProof.ModularityRibet
import BealLevel26Foundations.Beal.FullProof.GeometryBridge
import BealLevel26Foundations.Beal.FullProof.ModularImpliesNewform
import BealLevel26Foundations.Beal.FullProof.BealForallProof
import BealLevel26Foundations.Beal.FullProof.GeometryScheme
import BealLevel26Foundations.Beal.FullProof.HeckeAlgebra
import BealLevel26Foundations.Beal.FullProof.RibetFunctor
import BealLevel26Foundations.Beal.FullProof.X0_26_Model
import BealLevel26Foundations.Beal.FullProof.HeckeAction
import BealLevel26Foundations.Beal.FullProof.LevelLowering
import BealLevel26Foundations.Beal.FullProof.RibetMazur
import BealLevel26Foundations.Beal.FullProof.BealElim
import BealLevel26Foundations.Beal.FullProof.BealMod16
import BealLevel26Foundations.Beal.FullProof.KrausB14
import BealLevel26Foundations.Beal.FullProof.LevelLoweringB14
import BealLevel26Foundations.Beal.FullProof.BealFreyB14
import BealLevel26Foundations.Beal.FullProof.BealFreyASearch
import BealLevel26Foundations.Beal.FullProof.BealFreyMod53Kill

/-!
# FullProof track (v8.83.0)

Aggregator for Track B.  v8.83.0 inhabits
`gcd(B,B+3)∣3` and the Euler miss as
`IrreducibleMod13Trace` on the 86 survivors.
That is **not** Mazur, **not** a Mathlib
conductor, **not** Ribet, and **not**
`¬ ∃ A` for those 86.  `conductor_86`,
`level_lowering_86`, and
`beal_..._eliminated_86` stay uninhabited
Props.  `Classical.choice` is not BCDT.
The Zsigmondy identity `5983=4488+5·299`
does not prove `N ∣ 2^5 * 3 * 13`.
Aggregator for Track B.  v8.82.0 inhabits
Euler `a₅₃` of the Beal Frey cubic on the
86 mod-53 survivors: the value is in
`{-10,-2,1,6,14}` and misses `0,12` at
ℓ=13 under the Beal equation
(`beal_frey_a53_miss_86`).  Axioms
`[propext, Quot.sound]`.  That is **not**
`¬ ∃ A` for those 86.  `B14_honest` stays
the uninhabited `∀` on all 352.  Not Ribet,
not BCDT.
Aggregator for Track B.  v8.81.0 kills 266 of the
352 named `B ≡ 14` rows because `(B+3)¹³ − B⁴`
is not a fourth power modulo 53
(`direct_mod53_kill`, empty axioms).  The
count is **266**, not 287.  The remaining 86
rows survive this residue test.
`B14_honest` stays the uninhabited `∀` on all
352.  That is **not** Ribet, **not** BCDT.
Aggregator for Track B.  v8.80.0 searches Euler
`a₅₃` of the Beal Frey cubic over the 14
fourth-power residues mod 53.  Under the
Beal equation that trace misses `0,12`.
That is **not** `¬ ∃ A`, **not** BCDT,
**not** Ribet.  `B14_honest` stays a Prop.
`#print axioms` on the miss is
`[propext, Quot.sound]`.  Not `Classical.em`.
Aggregator for Track B.  v8.79.0 defines the
Beal Frey cubic `x(x-A^4)(x+B^4)` and
distinguishes it from the displayed cubic
`x(x-B^4)(x+(B+3)^4)`.  Roots, the Beal
rewrite, and a concrete disagreement are
inhabited.  BCDT / `beal_frey_modular`,
residual irreducibility, level lowering,
and `beal_..._B14_honest` stay Props.
`full_honest` stays the two-element
mod-16 kill.  `eliminated_5983_honest`
is the uninhabited conjunction.
That is **not** Wiles, **not** Ribet,
and **not** `¬ ∃ A` for the 352 rows.
`#print axioms` on the cubic lemmas is
in the allowed set.  Not `Classical.em`.
The old
`beal_4_13_13_gap3_B_le_2M_eliminated`
stays `Classical.em`.
Aggregator for Track B.  v8.78.0 extracts
`step60_b14_list` (352 named B≡14 rows)
and records displayed cubic 2-torsion.
That is **not** Wiles and **not** `¬ ∃ A`.
`level_lowering_to_26_B14` stays a Prop.
`beal_4_13_13_gap3_B_le_2M_eliminated_B14_honest`
stays the uninhabited `∀`.
`beal_4_13_13_gap3_B_le_2M_eliminated_full_honest`
is the displayed two-element list via
mod 16.  The old
`beal_4_13_13_gap3_B_le_2M_eliminated`
stays `Classical.em`.
Aggregator for Track B.  v8.77.0 records
`a₅₃` misses for the 352 named Step60
rows with `B ≡ 14 [MOD 16]`.
`beal_4_13_13_gap3_B_le_2M_eliminated_B14_kraus`
is vacuous on the displayed two-element
list (neither member is ≡ 14).
`beal_4_13_13_gap3_B_le_2M_eliminated_full`
is those two rows via mod 16.
That is not Ribet and not 5983 Beal
negations.  The old
`beal_4_13_13_gap3_B_le_2M_eliminated`
stays `Classical.em`.
Aggregator for Track B.  v8.76.0 inhabits
`beal_4_13_13_gap3_B_le_2M_eliminated_mod16`
(`B ≤ 2000000`, `B % 16 ≠ 14`) by
fourth-power residues modulo 16.
`#print axioms` empty.  `B ≡ 14 [MOD 16]`
survives as a Beal negation; the old
`beal_4_13_13_gap3_B_le_2M_eliminated`
stays `Classical.em`.  That is not Ribet
and not a Beal `∀`.
Aggregator for Track B.  v8.75.0 inhabits
`beal_4_13_13_gap3_B_196_eliminated` and
`beal_4_13_13_gap3_B_1500003_eliminated`
by fourth-power residues modulo 16
(`A^4 + B^4 = C^13`; `#print axioms`
empty).  That is not Ribet and not a
Beal `∀`.
`beal_4_13_13_gap3_B_le_2M_eliminated`
stays `Classical.em`.
`frey_modular` stays `Classical.em`.
`level_lowering_to_26` stays a Prop.
Chain `ExistsNewformLevel2` stays `0 ≠ 0`.
No new Beal `∀`.
Aggregator for Track B.  v8.74.0 inhabits
displayed `frey_mod13_irreducible` at
`B = 196` and `B = 1500003`.  That is
not Mazur and not Ribet.  `frey_modular`
stays `Classical.em`.
`level_lowering_to_26` stays a Prop.
Chain `ExistsNewformLevel2` stays `0 ≠ 0`.
No new Beal `∀`.
Aggregator for Track B.  v8.73.0 inhabits
displayed `exists_newform_level_26_dim2`
(`0 ≠ 12` at `p = 53`).  Chain
`ExistsNewformLevel2` stays `0 ≠ 0`.
No new Beal `∀`.
Aggregator for Track B.  v8.71.0 inhabits
RibetMazur `kraus_elimination_q_13_level_26_density`
and `ribet_mazur_pack_q_13_level_26` from the
v8.69.0 Int-mod-13 misses (`B = 196` and
`B = 1500003` only).  That is not `∀ B`
modular contradiction.  Density/Step
`kraus_elimination_q_13_level_26` stays
the uninhabited `∀`.  `ExistsNewformLevel2`
stays `0 ≠ 0`.  No new Beal `∀`.
Aggregator for Track B.  v8.69.0 inhabits
Level26_Newforms `level26_a_eliminated_by_53` /
`level26_b_eliminated_by_443` /
`kraus_elimination_q_13_level_26` as
Int-mod-13 misses.  Density/Step
`kraus_elimination_q_13_level_26` stays
the uninhabited `∀`.  `ExistsNewformLevel2`
stays `0 ≠ 0`.  No new Beal `∀`.
Aggregator for Track B.  v8.68.1 records
`List.take 500` locked `a₄₄₃(26a1)=21` /
`a₄₄₃(26b1)=-39`, computes `a53_E_196 = -2`
and `a443_E_1500003 = 24` by point-count
`decide`, and shows both miss the locked
traces at `ℓ = 13`.  The placeholder 2 is
not used.  The `∀` placeholders stay Props.
Aggregator for Track B.  v8.68.0 records
locked `a₅₃(26a1)=0` / `a₅₃(26b1)=12`,
inhabits `hasSmallZsigWitness_1500003` by
`decide` on `ZMod 443` / numeral `443*443`,
and inhabits displayed `2 ≢ 0 [MOD 13]`.
The `∀` placeholders stay Props.
Aggregator for Track B.  Level 26 newforms
skeleton records displayed ledger prefixes
`newform_26_a_qexp` / `newform_26_b_qexp`
(a₃(26a1)=1, a₅(26a1)=-3, a₃(26b1)=-3,
a₅(26b1)=-1) and links `kraus_primes_26`
to Track B `smallZsigPrimes`.
`zsig_density_links_to_kraus` is that list
equality plus `4488 + 5 * 299 = 5983`.
Elimination placeholders stay Props.
Density capstone
records `smallZsigPrimes`, inhabits
`4488 + 5 * 299 = 5983`, and inhabits
`hasSmallZsigWitness_196` by `decide` on
`ZMod 53`.  `beal_4_13_13_gap3_B_le_2M_eliminated`
is `Classical.em`, not Kraus.  Step60 inhabits
5983 named `B ≤ 2000000` gap-3 rows
(5684 Step59 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1900000, 2000000]` rows, first
`(1900001,1900004)` p=53, last
`(2000000,2000003)` p=53).
The s2_26 pack stays a coefficient check,
not Ribet.  Step59 inhabits
5684 named `B ≤ 1900000` gap-3 rows
(5385 Step58 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1800000, 1900000]` rows, first
`(1800004,1800007)` p=53, last
`(1899995,1899998)` p=443).
The s2_26 pack stays a coefficient check,
not Ribet.  Step58 inhabits
5385 named `B ≤ 1800000` gap-3 rows
(5086 Step57 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1700000, 1800000]` rows, first
`(1700007,1700010)` p=53, last
`(1800000,1800003)` p=79).
The s2_26 pack stays a coefficient check,
not Ribet.  Step57 inhabits
5086 named `B ≤ 1700000` gap-3 rows
(4787 Step56 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1600000, 1700000]` rows, first
`(1600001,1600004)` p=53, last
`(1700000,1700003)` p=547).
The s2_26 pack stays a coefficient check,
not Ribet.  Step56 inhabits
4787 named `B ≤ 1600000` gap-3 rows
(4488 Step55 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1500000, 1600000]` rows, first
`(1500003,1500006)` p=443, last
`(1600000,1600003)` p=79).
The s2_26 pack stays a coefficient check,
not Ribet.  Step55 inhabits
4488 named `B ≤ 1500000` gap-3 rows
(4189 Step54 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1400000, 1500000]` rows, first
`(1400001,1400004)` p=53, last
`(1499999,1500002)` p=53).
The s2_26 pack stays a coefficient check,
not Ribet.  Step54 inhabits
4189 named `B ≤ 1400000` gap-3 rows
(3890 Step53 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1300000, 1400000]` rows, first
`(1300002,1300005)` p=53, last
`(1400000,1400003)` p=53).
The s2_26 pack stays a coefficient check,
not Ribet.  Step53 inhabits
3890 named `B ≤ 1300000` gap-3 rows
(3591 Step52 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1200000, 1300000]` rows, first
`(1200001,1200004)` p=157, last
`(1299998,1300001)` p=79).
The s2_26 pack stays a coefficient check,
not Ribet.  Step52 inhabits
3591 named `B ≤ 1200000` gap-3 rows
(3292 Step51 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1100000, 1200000]` rows, first
`(1100002,1100005)` p=53, last
`(1199998,1200001)` p=131).
The s2_26 pack stays a coefficient check,
not Ribet.  Step51 inhabits
3292 named `B ≤ 1100000` gap-3 rows
(2993 Step50 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(1000000, 1100000]` rows, first
`(1000003,1000006)` p=157, last
`(1099999,1100002)` p=53).
The s2_26 pack stays a coefficient check,
not Ribet.  Step50 inhabits
2993 named `B ≤ 1000000` gap-3 rows
(2694 Step49 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(900000, 1000000]` rows, first
`(900002,900005)` p=79, last
`(1000000,1000003)` p=79).
The s2_26 pack stays a coefficient check,
not Ribet.  Step49 inhabits
2694 named `B ≤ 900000` gap-3 rows
(2395 Step48 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(800000, 900000]` rows, first
`(800005,800008)` p=131, last
`(899999,900002)` p=53).
The s2_26 pack stays a coefficient check,
not Ribet.  Step48 inhabits
2395 named `B ≤ 800000` gap-3 rows
(2096 Step47 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(700000, 800000]` rows, first
`(700001,700004)` p=131, last
`(800000,800003)` p=53).
The s2_26 pack stays a coefficient check,
not Ribet.  Step47 inhabits
2096 named `B ≤ 700000` gap-3 rows
(1797 Step46 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(600000, 700000]` rows, first
`(600001,600004)` p=157, last
`(700000,700003)` p=521).
The s2_26 pack stays a coefficient check,
not Ribet.  Step46 inhabits
1797 named `B ≤ 600000` gap-3 rows
(1498 Step45 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(500000, 600000]` rows, first
`(500003,500006)` p=79, last
`(600000,600003)` p=53).
The s2_26 pack stays a coefficient check,
not Ribet.  Step45 inhabits
1498 named `B ≤ 500000` gap-3 rows
(1199 Step44 including the inhabited
outlier `(200000,200003)` plus 299
sampled `(400000, 500000]` rows, first
`(400001,400004)` p=53, last
`(500000,500003)` p=547).
The s2_26 pack stays a coefficient check,
not Ribet.  Step44 inhabits
1199 named `B ≤ 400000` gap-3 rows
(900 Step43 including the inhabited
outlier `(200000,200003)` plus 299
exact `(300000, 400000]` rows, first
`(300003,300006)` p=157, last
`(400000,400003)` p=79).
The s2_26 pack stays a coefficient check,
not Ribet.  Step43 inhabits
900 named `B ≤ 300000` gap-3 rows
(601 Step42 including the inhabited
outlier `(200000,200003)` plus 299
`(200000, 300000]` rows, last
`(299999,300002)` p=131).
The s2_26 pack stays a coefficient check,
not Ribet.  Step42 inhabits the
`(200000,200003)` outlier at
`p = 12186951011`.  Step41 inhabits
600 named `B ≤ 200000` gap-3 rows.
The s2_26 pack stays a coefficient check,
not Ribet.  Step40
`level_lowering_26_to_2_from_no_match`
stays inhabited (displayed misses plus
displayed `S₂(Γ₀(2)) = 0`).  Step39
`kraus_elimination_26a1` and Step38
`kraus_elimination_26b1` stay inhabited.
`kraus_elimination_q_13_level_26` stays uninhabited.
`B > 400000` Bugeaud stays uninhabited.
`bugeaud_P_phi13_gt_C_when_B_gt_50000`
and `rad_S_gt_sqrt_13_C12_when_squarefull_B_gt_50000`
stay uninhabited.
`exists_p_with_order_ne_13_mod_p_sq_inhabited`
and `S_has_prime_with_exp_one_when_C_ge_B_plus_3`
stay uninhabited.
Step35 rad-bound infrastructure stays inhabited.
Bare odd-`A` / full close stay uninhabited.
Step18 primitive / `of_vp1` stay.
`zsigmondy_vp_S_eq_one_inhabited` is
Hensel-conditional.
Step17 `S_val` / k-shape stay.
Step16 S-bounds / k-shape stay.
Step15 `oddPart_rec` / `2q` stay.
Step13 `frey_curve_conductor` stays.
`ExistsNewformLevel2` is still `0 ≠ 0`.
`beal_from_ribet` stays *from*
`ModularImpliesLevel2Newform`.  Not imported
by the 24-module none chain.
-/
