# lean/Beal/Foundations/

Typed certificate bridges promoted from
[`sagemath/certs/`](../../../sagemath/certs/README.md) and the v1.4.0
ledger. **Current as of** `v4.0.6-rank-zero-fixed`.

| File | What it checks | What it is not |
|---|---|---|
| `J0_26_Decomp.lean` | Two dim-1 newform prefixes `26a1` / `26b1`, Weierstrass `c₄,c₆,Δ` | Not a scheme-theoretic `J₀(26)` |
| `J0DecompositionCertificate.lean` | Sage `certified_mwrank = 0` as stored data | Not a Mordell--Weil theorem |
| `FormalImmersionM3.lean` | `M₃ = [[1,1],[0,2]]`, `det = 2`, matches `ledgerM3` | Not a geometric formal immersion |
| `FormalImmersionM3Certificate.lean` | Same matrix facts under a certificate name | Same boundary |
| `LevelLowering_26.lean` | Re-export of typed `(ℓ, N, p, M)` data | Not a Ribet theorem |
| `EndgameScaffold.lean` | Re-export of the four Mazur premises | Not an unconditional `BealTheorem` |

`Beal.Foundations.release` remains `"v1.4.0"`. Later tags (v2--v4.0.6)
add modules elsewhere; they do not bump this cert-bridge version or
change the ledger SHA
`0259fe957cc348b7286e233ce717fac47c30ad174b05e8e1c5fb70626f511151`.
