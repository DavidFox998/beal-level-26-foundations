# MCOM manuscript source

`beal_scaffold.tex` is the LaTeX source (AMS `amsart` class) for the
manuscript *An Auditable Lean 4 Scaffold for Beal's Conjecture: A
Conditional Reduction and Its Level-26 Computational Evidence Base*,
targeted at *Mathematics of Computation* (MCOM).

The rendered `beal_scaffold.pdf` is committed alongside the source for
convenience; regenerate it after any edit rather than hand-patching the
binary.

## What the paper does and does not claim

The paper does not claim a proof of Beal's conjecture. It documents two
things:

1. `beal-conjecture`'s `ConditionalBealTheorem`, which reduces the
   conjecture to five explicit, named mathematical hypotheses (a genuine
   conditional result), and
2. the audit architecture (Core/Wrapper/named-hypothesis layering plus
   automated `#print axioms` enforcement) used across both repositories,
   which is the paper's main methodological contribution.

Section 3.3 of the paper is a required-reading disclaimer distinguishing
this repository's `none`/`propext only` axiom-footprint bookkeeping
labels (e.g. `BealForall_real_witness_none`) from the literal, still-
uninhabited, universally quantified Beal statement
(`beal_forall_from_Is13Case_sketch`, locked by
`original_beal_forall_sketch_type_eq`). Any edit to the paper must
preserve that distinction; do not soften or remove it.

Every substantive mathematical/computational claim in the paper is
anchored to a specific, versioned, Zenodo-DOI-archived release (see
Table 1 in the manuscript) rather than re-derived inline, per the
project's existing documentation convention.

See `../docs/MCOM_MANUSCRIPT_PLAN.md` for the planning notes this draft
is built from.

## Building

Requires a standard TeX Live installation (`amsart`, `amsmath`,
`amssymb`, `amsthm`, `hyperref`, `booktabs`, `array`, `microtype`,
`seqsplit` — all in `texlive-latex-extra`/`texlive-science` on Debian/
Ubuntu).

```bash
cd paper
pdflatex beal_scaffold.tex
pdflatex beal_scaffold.tex   # second pass resolves cross-references
```

Output is `beal_scaffold.pdf` (6 pages). Intermediate build files
(`.aux`, `.log`, `.out`, `.toc`) are git-ignored.
