# Bounded gap-3 search: kernel-checked million

The Lean 4.12.0 theorem
`BealMatveevBeal.BealMatveevBealV25B0Search.Full10e6.full10e6_no_solution_forward`
proves

> For every natural number `B ≤ 1,000,000` and every natural number `A`,
> `A^4 + B^4 ≠ (B + 3)^13`.

This is a bounded statement about one equation. It is **not** a proof of the
general Beal conjecture, of level lowering, or of the other conditional
mathematical premises in this repository.

## Proof and dependencies

- `MaskSound.lean` proves ten modular-mask soundness lemmas. Each mask is
  checked by ordinary kernel reduction (`by decide`), without
  `native_decide` or `Lean.ofReduceBool`.
- `Chunked10e6.lean` proves that a true Boolean interval check excludes any
  natural-number solution at every `B` in that interval.
- `scripts/generate_chunked10e6.py` emits 2,000 individual Lean source files,
  each with one `by decide` theorem for a 500-value interval. The first is
  `[0, 500)` and the last is `[999500, 1000000)`. The 200 group and 20 block
  modules dispatch to these independent theorems. Running the Python script
  does not prove anything: the generated declarations must compile in Lean.
- `Full10e6.lean` dispatches by quotient and remainder to all 2,000
  certificates, applies the interval soundness theorem, and checks
  `B = 1,000,000` separately with `by decide`.

The JSON checkpoint and its SHA-256 digests are independent external
cross-checks, never hypotheses or proof inputs. The printed axiom set for
`full10e6_no_solution_forward` is
`[propext, Classical.choice, Quot.sound]`. Other, older repository theorems
may have different axiom sets; this statement concerns the new bounded
theorem.

## Verification

After an incremental build of `BealMatveevBealV25B0Search.Full10e6`, the
following clean sequence completed successfully:

```sh
lake clean
lake exe cache get
lake build BealMatveevBealV25B0Search.Full10e6 BealFinal.Main
```

The clean build reported 7,434 steps, rather than the earlier estimate of
5,216, because it includes the generated certificate modules.
`BealFinal.Main` builds, but its general-Beal forward statements still take
their documented inputs; the bounded theorem does not discharge them.

## Published version

- GitHub release and annotated tag:
  [`v25.0.2-10e6-kernel-checked`](https://github.com/DavidFox998/beal-level-26-foundations/releases/tag/v25.0.2-10e6-kernel-checked).
- Version DOI: [10.5281/zenodo.22927972](https://doi.org/10.5281/zenodo.22927972).
- Previous version: [10.5281/zenodo.22922473](https://doi.org/10.5281/zenodo.22922473).
  Both are in the same Zenodo version series (concept DOI
  [10.5281/zenodo.22379293](https://doi.org/10.5281/zenodo.22379293)).

The archived source is the tagged GitHub tree
`23b76deda5f830fc5412a37df5deda13ce48725d` at commit
`99ac1f6a459e9f9e1300ea29dcacafc34c471ce3`. The published ZIP has
SHA-256 `961b24583a6b0b74de2eab501809c13e07e21ee8f3d513cffb629c50c7e05186`
and contains all 2,000 interval certificates. The version DOI identifies
only the bounded theorem and its supporting source, not a general-Beal proof.