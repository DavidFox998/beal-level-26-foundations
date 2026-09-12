# v13.0.0 Level-26 modular elimination

`lean/BealLevel26Foundations/Beal/FullProof/BealLevel26ModularElimination.lean`

Frey curve `Y² = X(X-A⁴)(X+B⁴)` for
`(4,4,13)` gap3.  Reuses `c₄`, `c₆`
from the Tate file.  Conductor is
`tateConductor A B = 2^{f₂}*rad(AB(B+3))*13`
with `f₂ = tateF2 ≤ 5`, **not** `2⁵*3*13`.
Witness `63982 = 2*31991` proves the old
`N ∣ 2⁵*3*13` claim fails; we use
`2⁵*rad*13`.  `conductor_86` stays Prop.

Five cert Props are honest premises,
not inhabited:

- `J0DecompositionSoundness_26`
- `MwrankCertificateSoundness_26`
- `FormalImmersionSoundness_26`
- `FreyCurveExists`
- `LevelLowering_26`

Inhabited:

- `kraus_a53_elimination`: Kraus `a₅₃`
  values `{-10,-2,1,6,14}` miss `S₂(26)`
  traces `{0,12}`, by kernel `decide`
- `beal_44_13_level_26_modular_elimination`:
  the five certs plus `baker_bound_gap3`
  imply there is no `A,B,C` with
  `A⁴+B⁴=(B+3)¹³` and `C=B+3`
  - `B ≤ 1e6` by `allKilled_1e6`
    (25 chunks, `B ≡ 14`) via
    `baker_le_B0_gap3`
  - `B > 1e6` by `matveev_explicit_gap3`

`baker_bound_gap3` stays Prop (explicit
Matveev / BMS Table 1 not in Mathlib 4.12).
`B14_honest` stays Prop.
Tate file stays exactly v11/v12
(0 lines changed).  Baker file stays
exactly v12 (0 lines changed).
Does not import RibetMazur, BealFreyB14,
or FreyModularity_13.  Not BCDT.
Does not use sorry.
