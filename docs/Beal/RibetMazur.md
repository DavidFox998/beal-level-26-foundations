# v8.14.0 RibetMazur odd-A residues + A=1 impossible

`lean/BealLevel26Foundations/Beal/FullProof/RibetMazur.lean`

Elementary modular constraints for `m=4, n=13, p=13`
with odd `A`.  The only odd power of 2 is `A=1`,
and `1 + B¹³ = C¹³` is impossible.  Mixed covers
that exponent triple **iff** `A=2^e`.  Odd `A ≥ 3`
is still none of the three arms.  Does **not**
import `X0_26_Model`.  Does **not** inhabit
`ExistsNewformLevel2` (`0 ≠ 0`).

| Name | Status |
|---|---|
| `mod_pow4_odd` | odd `A` has `A⁴ ≡ 1 [MOD 16]` |
| `mod_pow13_odd` | odd `B` has `B¹³ ≡ B [MOD 8]`; not `∀ B` |
| `beal_4_13_13_mod8` | opposite parity plus residues; not `False` |
| `beal_4_13_13_mod13` | `A⁴ ≡ C − B` in `ZMod 13` |
| `not_beal_4_13_13_of_A_eq_one` | `1 + B¹³ = C¹³` is impossible |
| `FreyEllCase5Mixed_4_13_13_iff_pow2_A` | Mixed iff `A=2^e` |
| `beal_4_13_13_size` | uninhabited Prop; odd `A ≥ 3` not closed |
| `beal_from_ribet_ell_mixed` | still *from* `ModularImpliesLevel2Newform` |

`#print axioms` is `[propext, Classical.choice, Quot.sound]`.
Track A About mint stays `22635221`.
