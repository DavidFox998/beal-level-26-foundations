import Beal.«Beal.General».Minimal
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-!
Preliminary invariant facts at 2. These are inputs to, not a replacement
for, the local minimal-model and Tate-algorithm computations required to
identify a Néron conductor. No conductor formula is asserted here.
-/

namespace Beal.General

/-- Symbols needed to state future Tate-algorithm results. This type is
only a vocabulary: no curve has been assigned a symbol by this definition. -/
inductive KodairaType where
  | I (n : ℕ)
  | II
  | III
  | IV
  | IStar (n : ℕ)
  | IVStar
  | IIIStar
  | IIStar
  deriving DecidableEq, Repr

/-- The unit-discriminant output a future correct Tate classifier must
prove. No classifier satisfying this requirement is supplied here. -/
def TateUnitCriterion
    (typeAtTwo : WeierstrassCurve ℤ_[2] → KodairaType) : Prop :=
  ∀ M, Padic.valuation (M.Δ : ℚ_[2]) = 0 → typeAtTwo M = KodairaType.I 0

/-- The corresponding good-reduction conductor rule. This is an
unsupplied requirement on a future actual local conductor exponent. -/
def ConductorUnitCriterion
    (f2 : WeierstrassCurve ℤ_[2] → ℕ) : Prop :=
  ∀ M, Padic.valuation (M.Δ : ℚ_[2]) = 0 → f2 M = 0

/-- Relative to a correct Tate classifier, a unit discriminant
precludes every positive-index multiplicative symbol. This does not
construct the classifier or assign any Kodaira symbol to a curve. -/
theorem I_positive_incompatible_with_unit
    (typeAtTwo : WeierstrassCurve ℤ_[2] → KodairaType)
    (hTate : TateUnitCriterion typeAtTwo)
    (M : WeierstrassCurve ℤ_[2])
    (hunit : Padic.valuation (M.Δ : ℚ_[2]) = 0)
    (n : ℕ) (hn : 0 < n) :
    typeAtTwo M ≠ KodairaType.I n := by
  have hzero := hTate M hunit
  intro hpositive
  rw [hzero] at hpositive
  cases hpositive
  omega

/-- A threshold scale-2 change has the good-reduction symbol *if*
the classifier's unit criterion has been proved. Its existence and
integrality are premises, not consequences of valuation four. -/
theorem threshold_type_I0_conditional (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 x y z p q r).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1)
    (hthreshold : padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) = 4)
    (typeAtTwo : WeierstrassCurve ℤ_[2] → KodairaType)
    (hTate : TateUnitCriterion typeAtTwo) :
    typeAtTwo M = KodairaType.I 0 := by
  exact hTate M
    ((high_parity_exactly_four x y z p q r hx hy M C hmodel hscale).mpr hthreshold)

/-- The local conductor exponent is zero *if* its genuine good-reduction
rule has been supplied. No general `f₂` is constructed by this theorem. -/
theorem threshold_f2_zero_conditional (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 x y z p q r).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2]))
    (hscale : Padic.valuation (C.u : ℚ_[2]) = 1)
    (hthreshold : padicValNat 2 (x ^ p * y ^ q * (x ^ p + y ^ q)) = 4)
    (f2 : WeierstrassCurve ℤ_[2] → ℕ)
    (hgood : ConductorUnitCriterion f2) :
    f2 M = 0 := by
  exact hgood M
    ((high_parity_exactly_four x y z p q r hx hy M C hmodel hscale).mpr hthreshold)

/-- An actual successful first-step certificate removes the model-
existence premise at valuation four. The Kodaira conclusion still
requires a genuine classifier satisfying its unit-discriminant rule. -/
theorem tate_step_threshold_I0_conditional (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (step : TateScaleTwoStep U V)
    (hthreshold : padicValNat 2 (U * V * (U + V)) = 4)
    (typeAtTwo : WeierstrassCurve ℤ_[2] → KodairaType)
    (hTate : TateUnitCriterion typeAtTwo) :
    ∃ (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2]),
      ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
        M.map (algebraMap ℤ_[2] ℚ_[2]) ∧
      Padic.valuation (C.u : ℚ_[2]) = 1 ∧
      typeAtTwo M = KodairaType.I 0 ∧
      ∀ n : ℕ, 0 < n → typeAtTwo M ≠ KodairaType.I n := by
  obtain ⟨M, C, hmodel, hscale⟩ := tate_step_integral_model U V step
  have hunit : Padic.valuation (M.Δ : ℚ_[2]) = 0 :=
    (high_parity_exactly_four U V 0 1 1 0
      (by simpa using hU) (by simpa using hV) M C hmodel hscale).mpr
      (by simpa using hthreshold)
  refine ⟨M, C, hmodel, hscale, hTate M hunit, ?_⟩
  intro n hn
  exact I_positive_incompatible_with_unit typeAtTwo hTate M hunit n hn

private theorem odd_c4_factor (U V : ℕ) (h : Odd U ∨ Odd V) :
    Odd (U ^ 2 + U * V + V ^ 2) := by
  have hu : U % 2 = 0 ∨ U % 2 = 1 := by omega
  have hv : V % 2 = 0 ∨ V % 2 = 1 := by omega
  have hh : U % 2 = 1 ∨ V % 2 = 1 := by
    rcases h with h | h
    · exact Or.inl (Nat.odd_iff.mp h)
    · exact Or.inr (Nat.odd_iff.mp h)
  apply Nat.odd_iff.mpr
  rcases hu with hu | hu <;> rcases hv with hv | hv
  all_goals simp [Nat.add_mod, Nat.mul_mod, pow_two, hu, hv] at *

/-- Under primitive parity, the displayed integral model has
v₂(c₄)=4. It is not thereby known to be a minimal model. -/
theorem frey_c4_v2_of_parity (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (hparity : Odd (x ^ p) ∨ Odd (y ^ q)) :
    padicValInt 2 (freyWeierstrassGeneral x y z p q r).c₄ = 4 := by
  have hc4Nat :
      (freyWeierstrassGeneral x y z p q r).c₄ =
        ((16 * ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) : ℕ) : ℤ) := by
    rw [frey_c4]
    push_cast
    ring
  rw [hc4Nat]
  simp only [padicValInt, Int.natAbs_ofNat]
  have hS : (x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2 ≠ 0 := by positivity
  have h16 : padicValNat 2 16 = 4 := by
    change padicValNat 2 (2 ^ 4) = 4
    rw [padicValNat.pow 4 (by norm_num : (2 : ℕ) ≠ 0), padicValNat_self]
  have hSval :
      padicValNat 2 ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) = 0 := by
    apply padicValNat.eq_zero_of_not_dvd
    intro hd
    have hmod : ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) % 2 = 0 :=
      Nat.mod_eq_zero_of_dvd hd
    have hodd : ((x ^ p) ^ 2 + x ^ p * y ^ q + (y ^ q) ^ 2) % 2 = 1 :=
      Nat.odd_iff.mp (odd_c4_factor (x ^ p) (y ^ q) hparity)
    rw [hodd] at hmod
    norm_num at hmod
  rw [padicValNat.mul (by norm_num : (16 : ℕ) ≠ 0) hS, h16, hSval]

/-- Coprime powered inputs cannot both be even. This still says
nothing about Kodaira type or the conductor exponent. -/
theorem frey_c4_v2_of_coprime (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (hcop : Nat.Coprime (x ^ p) (y ^ q)) :
    padicValInt 2 (freyWeierstrassGeneral x y z p q r).c₄ = 4 := by
  apply frey_c4_v2_of_parity x y z p q r hx hy
  rcases Nat.even_or_odd (x ^ p) with heU | hoU
  · rcases Nat.even_or_odd (y ^ q) with heV | hoV
    · exfalso
      rcases heU with ⟨u, hu⟩
      rcases heV with ⟨v, hv⟩
      have hdU : 2 ∣ x ^ p := ⟨u, by omega⟩
      have hdV : 2 ∣ y ^ q := ⟨v, by omega⟩
      have hgcd : 2 ∣ Nat.gcd (x ^ p) (y ^ q) := Nat.dvd_gcd hdU hdV
      have hcop' : Nat.gcd (x ^ p) (y ^ q) = 1 := hcop
      rw [hcop'] at hgcd
      norm_num at hgcd
    · exact Or.inr hoV
  · exact Or.inl hoU

/-- For positive coprime inputs, the displayed Z₂ model has nonzero
`c₄` of valuation four. This concerns the displayed model, not yet
its minimal replacement. -/
theorem freyZ2_c4_v2_of_coprime (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (hcop : Nat.Coprime U V) :
    Padic.valuation ((freyZ2 U V 0 1 1 0).c₄ : ℚ_[2]) = 4 ∧
      ((freyZ2 U V 0 1 1 0).c₄ : ℚ_[2]) ≠ 0 := by
  have hraw := frey_c4_v2_of_coprime U V 0 1 1 0
    (by simpa using hU) (by simpa using hV) (by simpa using hcop)
  have hc4Nat :
      (freyWeierstrassGeneral U V 0 1 1 0).c₄ =
        ((16 * (U ^ 2 + U * V + V ^ 2) : ℕ) : ℤ) := by
    rw [frey_c4]
    push_cast
    ring
  rw [hc4Nat] at hraw
  have hc4Z2 :
      (freyZ2 U V 0 1 1 0).c₄ =
        ((16 * (U ^ 2 + U * V + V ^ 2) : ℕ) : ℤ_[2]) := by
    rw [freyZ2, WeierstrassCurve.map_c₄, hc4Nat]
    simp
  have hn : 16 * (U ^ 2 + U * V + V ^ 2) ≠ 0 := by positivity
  rw [hc4Z2, PadicInt.coe_natCast]
  constructor
  · rw [q2_val_nat _ hn]
    exact_mod_cast (show padicValNat 2 (16 * (U ^ 2 + U * V + V ^ 2)) = 4 by
      simpa only [padicValInt, Int.natAbs_ofNat] using hraw)
  · exact Nat.cast_ne_zero.mpr hn

/-- Coprimality of the original bases supplies the powered-input
c₄ hypothesis, provided both exponents are positive. -/
theorem frey_c4_v2_of_base_coprime (x y z p q r : ℕ)
    (hx : 0 < x ^ p) (hy : 0 < y ^ q)
    (hp : 0 < p) (hq : 0 < q) (hcop : Nat.Coprime x y) :
    padicValInt 2 (freyWeierstrassGeneral x y z p q r).c₄ = 4 := by
  apply frey_c4_v2_of_coprime x y z p q r hx hy
  exact (Nat.coprime_pow_right_iff hq (x ^ p) y).mpr
    ((Nat.coprime_pow_left_iff hp x y).mpr hcop)

/-- The factor multiplying 16 in c₄ is coprime to the three factors
of the raw discriminant when the two powered inputs are coprime.
This arithmetic fact alone does not classify reduction at 2. -/
theorem coprime_c4_factor_uvw (U V : ℕ) (hcop : Nat.Coprime U V) :
    Nat.Coprime (U ^ 2 + U * V + V ^ 2) (U * V * (U + V)) := by
  apply Nat.coprime_of_dvd
  intro d hp hdS hdProd
  have hbad (hdU : d ∣ U) (hdV : d ∣ V) : False := by
    have hdg : d ∣ Nat.gcd U V := Nat.dvd_gcd hdU hdV
    have hg : Nat.gcd U V = 1 := hcop
    rw [hg] at hdg
    exact hp.ne_one (Nat.dvd_one.mp hdg)
  have hV_of_U (hdU : d ∣ U) : d ∣ V := by
    have hdU2 : d ∣ U ^ 2 := by simpa [pow_two] using dvd_mul_of_dvd_left hdU U
    have hdUV : d ∣ U * V := dvd_mul_of_dvd_left hdU V
    have hdS' : d ∣ U ^ 2 + U * V := dvd_add hdU2 hdUV
    have hdV2 : d ∣ V ^ 2 := by
      have h := Nat.dvd_sub' hdS hdS'
      simpa only [Nat.add_sub_cancel_left] using h
    exact hp.dvd_of_dvd_pow hdV2
  have hU_of_V (hdV : d ∣ V) : d ∣ U := by
    have hdV2 : d ∣ V ^ 2 := by simpa [pow_two] using dvd_mul_of_dvd_left hdV V
    have hdUV : d ∣ U * V := dvd_mul_of_dvd_right hdV U
    have hdS' : d ∣ U * V + V ^ 2 := dvd_add hdUV hdV2
    have hdU2 : d ∣ U ^ 2 := by
      have h := Nat.dvd_sub' hdS hdS'
      simpa only [Nat.add_assoc, Nat.add_sub_cancel_right] using h
    exact hp.dvd_of_dvd_pow hdU2
  rcases hp.dvd_mul.mp hdProd with hdUV | hdW
  · rcases hp.dvd_mul.mp hdUV with hdU | hdV
    · exact hbad hdU (hV_of_U hdU)
    · exact hbad (hU_of_V hdV) hdV
  · have hdW2 : d ∣ (U + V) ^ 2 := by
      simpa [pow_two] using dvd_mul_of_dvd_left hdW (U + V)
    have hid : (U + V) ^ 2 = (U ^ 2 + U * V + V ^ 2) + U * V := by ring
    have hdSum : d ∣ (U ^ 2 + U * V + V ^ 2) + U * V := hid ▸ hdW2
    have hdUV : d ∣ U * V := by
      have h := Nat.dvd_sub' hdSum hdS
      simpa only [Nat.add_sub_cancel_left] using h
    rcases hp.dvd_mul.mp hdUV with hdU | hdV
    · exact hbad hdU (hV_of_U hdU)
    · exact hbad (hU_of_V hdV) hdV

/-- For positive coprime inputs, an arbitrary Q₂ change leading to an
integral model cannot have scale valuation greater than one. This
uses `v₂(c₄)=4`; it does not normalize a valuation-one change to the
fixed scale `u=2` or supply a Tate classification. -/
theorem frey_integral_change_scale_le_one (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (hcop : Nat.Coprime U V)
    (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2])
    (hmodel : ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
      M.map (algebraMap ℤ_[2] ℚ_[2])) :
    Padic.valuation (C.u : ℚ_[2]) ≤ 1 := by
  obtain ⟨hval, hne⟩ := freyZ2_c4_v2_of_coprime U V hU hV hcop
  have hu : (C.u : ℚ_[2]) ≠ 0 := Units.ne_zero C.u
  have hc := congrArg WeierstrassCurve.c₄ hmodel
  simp only [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.map_c₄,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hc
  have hv := congrArg Padic.valuation hc
  rw [Padic.valuation_map_mul (pow_ne_zero 4 (inv_ne_zero hu)) hne,
    q2_val_pow _ (inv_ne_zero hu) 4, q2_val_inv _ hu, hval] at hv
  have hn : 0 ≤ Padic.valuation (M.c₄ : ℚ_[2]) := PadicInt.valuation_nonneg M.c₄
  omega

/-- The displayed model has singular reduction modulo 2;
this alone cannot determine a Néron conductor. -/
theorem frey_discriminant_even (x y z p q r : ℕ) :
    (2 : ℤ) ∣ (freyWeierstrassGeneral x y z p q r).Δ := by
  rw [frey_delta_raw]
  refine ⟨8 * ((x : ℤ) ^ p) ^ 2 * ((y : ℤ) ^ q) ^ 2 *
    ((x : ℤ) ^ p + (y : ℤ) ^ q) ^ 2, ?_⟩
  ring

/- The positive-scale "second step" is not available for the
coprime first-step models: `c₄` is already a unit, regardless of
whether their discriminant valuation exceeds twelve. -/
theorem tate_step_no_second_scale_of_coprime (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (hcop : Nat.Coprime U V)
    (step : TateScaleTwoStep U V) :
    ∃ (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2]),
      ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
        M.map (algebraMap ℤ_[2] ℚ_[2]) ∧
      Padic.valuation (C.u : ℚ_[2]) = 1 ∧
      Padic.valuation (M.c₄ : ℚ_[2]) = 0 ∧
      ¬ SecondScaleTwoAttempt M := by
  obtain ⟨M, C, hmodel, hscale⟩ := tate_step_integral_model U V step
  obtain ⟨hrawVal, hrawNe⟩ := freyZ2_c4_v2_of_coprime U V hU hV hcop
  have hu : (C.u : ℚ_[2]) ≠ 0 := Units.ne_zero C.u
  have hc := congrArg WeierstrassCurve.c₄ hmodel
  simp only [WeierstrassCurve.variableChange_c₄, WeierstrassCurve.map_c₄,
    PadicInt.algebraMap_apply, Units.val_inv_eq_inv_val] at hc
  have hc4Ne : (M.c₄ : ℚ_[2]) ≠ 0 := by
    rw [← hc]
    exact mul_ne_zero (pow_ne_zero 4 (inv_ne_zero hu)) hrawNe
  have hval :=
    scale_two_c4_valuation_if_integral (freyZ2 U V 0 1 1 0) M C hrawNe hmodel hscale
  have hunitVal : Padic.valuation (M.c₄ : ℚ_[2]) = 0 := by omega
  exact ⟨M, C, hmodel, hscale, hunitVal,
    no_second_scale_two_of_unit_c4 M hc4Ne hunitVal⟩

/-- Conditional local conductor consequence for a *constructed* model
at the threshold. A genuine good-reduction conductor rule remains an
unsupplied premise; no general `f₂` is defined here. -/
theorem tate_step_threshold_f2_zero_conditional (U V : ℕ)
    (hU : 0 < U) (hV : 0 < V) (step : TateScaleTwoStep U V)
    (hthreshold : padicValNat 2 (U * V * (U + V)) = 4)
    (f2 : WeierstrassCurve ℤ_[2] → ℕ)
    (hgood : ConductorUnitCriterion f2) :
    ∃ (M : WeierstrassCurve ℤ_[2]) (C : WeierstrassCurve.VariableChange ℚ_[2]),
      ((freyZ2 U V 0 1 1 0).map (algebraMap ℤ_[2] ℚ_[2])).variableChange C =
        M.map (algebraMap ℤ_[2] ℚ_[2]) ∧
      Padic.valuation (C.u : ℚ_[2]) = 1 ∧ f2 M = 0 := by
  obtain ⟨M, C, hmodel, hscale⟩ := tate_step_integral_model U V step
  have hunit : Padic.valuation (M.Δ : ℚ_[2]) = 0 :=
    (high_parity_exactly_four U V 0 1 1 0
      (by simpa using hU) (by simpa using hV) M C hmodel hscale).mpr
      (by simpa using hthreshold)
  exact ⟨M, C, hmodel, hscale, hgood M hunit⟩

/- TODO tate_classification_general: The three parity witnesses in Minimal have odd discriminant
*after* their particular scale-2 changes. They cannot be assigned
type I_{2*v₂(W)} by a correct classifier: its unit-discriminant rule
would force good reduction (I₀), not positive-index multiplicative Iₙ.
No actual Kodaira classifier, full Tate algorithm, or local conductor
function and its good-reduction rule is constructed here. The three
infinite first-step subfamilies in Minimal have unit models at the exact
threshold, but remaining high-congruence cases and reduction types are open.
Prove the full Tate steps before an unconditional f₂, or any formula
N=2^?*rad(x*y*z), can be claimed. -/

/- TODO full_tate / f2 / conductor: The unit-discriminant criteria above
are only necessary interfaces for a future genuine local classifier
and conductor exponent, not definitions or proofs of either one.
The coprime first-step models cannot be scaled again positively;
compute their reduction types on those models instead. -/

#print axioms I_positive_incompatible_with_unit
#print axioms frey_integral_change_scale_le_one
#print axioms threshold_type_I0_conditional
#print axioms threshold_f2_zero_conditional
#print axioms tate_step_threshold_I0_conditional
#print axioms frey_c4_v2_of_coprime
#print axioms freyZ2_c4_v2_of_coprime
#print axioms tate_step_no_second_scale_of_coprime
#print axioms tate_step_threshold_f2_zero_conditional
#print axioms frey_c4_v2_of_base_coprime
#print axioms coprime_c4_factor_uvw
#print axioms frey_discriminant_even

end Beal.General