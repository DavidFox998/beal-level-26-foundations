# .github/workflows/

GitHub Actions workflow for
[DavidFox998/beal-level-26-foundations](https://github.com/DavidFox998/beal-level-26-foundations).

[`main.yml`](main.yml) is the historical Beal job:
`lake exe cache get`, `lake build BealMatveevBeal`, and
`./scripts/verify-matveev-beal.sh` on `main`,
`phase-darmon-merel-4413`, and the four v27 working
branches. Not on `tate-neron-v28`, `mazur-cusps-v28`,
`ribet-no-newforms-v28`, or
`kolyvagin-fintype-subsingleton-v28`.

[`build.yml`](build.yml) is the v28 incremental job:
`lean-action@v1` with Mathlib cache, `.lake` cache key
`lake-…-v27-6ccafbf`, `lake exe cache get`, then
`lake build +Kolyvagin_Fintype_Subsingleton_inhabited`,
`lake build HonestB0Search`, `lake build Level26`.
No `lake build` of default `BealMatveevBeal`.

This is a Lean 4.12 theorem library, not a web app.
Concept DOI `10.5281/zenodo.22379293`.
