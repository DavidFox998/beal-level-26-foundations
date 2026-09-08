# certs/ — Size tables for Beal (4,13,13)

These files are **decide tables**, not a Beal `∀` proof.
Track A About mint stays `10.5281/zenodo.22635221`.
Unconditional Beal is **not** claimed.

Compiled theorems live under
`lean/BealLevel26Foundations/`.  The tables here
are the `B ∈ [1, 100]` certificates those theorems
`decide` against.

| File | Slice | What it certifies |
|---|---|---|
| `Beal_4_13_13_Size_Table.lean` | `C = B+1` | 100 rows `(B, C¹³−B¹³, 13 B¹², floor fourth root)`.  Each difference is `≥ 13 B¹²` and is **not** a fourth power.  Used by v8.19.1 / v8.19.6 `C = B+1` close. |
| `Beal_4_13_13_Size_C_ge_B_plus_2_Table.lean` | `C = B+2` | 100 rows `(B, C, C¹³−B¹³, 26 B¹², floor fourth root)`.  Each difference is `≥ 26 B¹²` and is **not** a fourth power.  Used by v8.19.2 / v8.19.6 `C = B+2` close. |
| `pari_x0_26_four_cusps.json` | Track A | PARI lock for `X₀(26)` cusps `[1,2,13,26]`, `26a1` / `26b1` discriminants, `|Sel₂|=1`, `det M₃=2`.  Not a size table. |

`B ≤ 100` with `C ≥ B+3` stays open (`k` unbounded).
`B > 100` stays open.  The tables do **not** inhabit
`ExistsNewformLevel2` (`0 ≠ 0`) and do **not** drop
`ModularImpliesLevel2Newform` from `beal_from_ribet`.
