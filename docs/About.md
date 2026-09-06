# About — Beal Level 26 Foundations

Latest tag / HEAD: `v4.59.0-iter-about-roadmap-catchup-before-v5`.

Catch-up of previous HEAD `4c027c3` /
`v4.58.0-iter-taylor-wiles-scaffold`.  Latest parallel mint
is now [10.5281/zenodo.22551298](https://doi.org/10.5281/zenodo.22551298)
(v4.58.0, DataCite findable) until a new mint.  Hook
[10.5281/zenodo.22379293](https://doi.org/10.5281/zenodo.22379293).
`IsVersionOf` [10.5281/zenodo.22272382](https://doi.org/10.5281/zenodo.22272382)
is metadata only.  Original-family latest remains
[10.5281/zenodo.22322627](https://doi.org/10.5281/zenodo.22322627).

Chain:
`… → 22550229` (v4.55.0) → `22550771` (v4.56.0) →
`22551051` (v4.57.0) → `22551298` (v4.58.0).

Still not `∀ A B C` unconditionally.  Still not Mathlib
`X₀(26)(ℚ)` + Ribet + Tate + Taylor–Wiles.  Conditional
Beal `∀` propext-only is the ceiling:
`is13Case_false_implies_Beal_of_tate_ribet_disc_propext_only`
takes `hTate → hRibet → hWeierstrass → hComp + hΔ` and
returns Beal `∀` (**propext only**).  It builds a *local*
`Is13Case → False` via `is13Case_implies_False_of_tate_ribet_disc`
and applies `beal_forall_from_Is13Case_false_sketch`
`(∀ w, Is13Case → False) → Beal ∀` (valid type, Path 2,
not Path 1).  Neither inhabits unconditional
`Is13CaseForcesFalseSketchViaLevel2`.  No `False.elim`.
Path 1 is false: `⟨13, 2, 1⟩` is primitive with `gcd = 1`
by `rfl`.

`docs/Final/ROADMAP.md` locks v5 without waiting for
Mathlib: v5.0.0 Tate inhabit, v5.1.0 Ribet inhabit,
v5.2.0 `R = T` inhabit, v5.3.0 Beal `∀` in kernel.
Those slices are **not** done.  10 modules green.
`NO_SORRY_OK`.

This is the in-repo About lock for GitHub About / topics /
homepage wording.  README badges stay on `22452680`.
