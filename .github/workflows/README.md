# .github/workflows/ — v30

Current: `v0.30-mcom-structural-verification — Level 26 Structural Verification — Tate 928=2⁵·29 Neron I0* I8 c4 Δ v2=6 v29=8 Mazur 2184 48<2184 13=2²+3² 288/48=6 card 2 genus 0 infinite vs 2 Ribet 928/29=32 ∅ card 0 full=1 new=1 LMFDB 32a1 Kolyvagin |Sel2|=1 3·7=21 L/Ω=1/3 1/7 rank0 26a1 26b1`. Concept DOI `10.5281/zenodo.22379293`.

GitHub Actions workflow for
[DavidFox998/beal-level-26-foundations](https://github.com/DavidFox998/beal-level-26-foundations).

[`main.yml`](main.yml) is the historical Beal job:
`lake exe cache get`, `lake build BealMatveevBeal`, and
`./scripts/verify-matveev-beal.sh` on `main`,
`phase-darmon-merel-4413`, and the four v27 working
branches. Not on the v28 working branches.

[`build.yml`](build.yml) is the incremental job on
`phase-darmon-merel-4413`, the four v28 slices, and
the four v29 final slices (`tate-neron-final-v29`,
`mazur-no-isogeny-final-v29`,
`ribet-928-to-32-final-v29`,
`kolyvagin-rank0-final-v29`): `lean-action@v1` with
Mathlib cache, `.lake` cache key `lake-…-v27-6ccafbf`,
`lake exe cache get`, then the HonestB0Search modules,
`lake build HonestB0Search`, `lake build Level26`. No
`lake build` of default `BealMatveevBeal`. Do **not** add
v29 working branches to historical `main.yml`.

This is a Lean 4.12 theorem library, not a web app.
Concept DOI `10.5281/zenodo.22379293`.
