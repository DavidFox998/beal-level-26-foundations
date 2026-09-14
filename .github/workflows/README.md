# .github/workflows/

GitHub Actions workflow for
[DavidFox998/beal-level-26-foundations](https://github.com/DavidFox998/beal-level-26-foundations).

[`main.yml`](main.yml) runs `lake exe cache get`, `lake build
BealMatveevBeal`, and `./scripts/verify-matveev-beal.sh` on
pushes and pull requests to `main`.

This is a Lean 4.12 theorem library, not a web app.
Concept DOI `10.5281/zenodo.22379293`.
