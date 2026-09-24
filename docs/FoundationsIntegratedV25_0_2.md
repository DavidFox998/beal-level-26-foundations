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