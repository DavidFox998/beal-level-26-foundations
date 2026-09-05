# .github/

GitHub Actions for
[DavidFox998/beal-level-26-foundations](https://github.com/DavidFox998/beal-level-26-foundations).

[`workflows/main.yml`](workflows/main.yml) runs on pushes and pull
requests to **`main`**:

1. `lake build BealLevel26Foundations`
2. `lake build BealLevel26FoundationsScaffold`
3. `lake build BealLevel26FoundationsReal`
4. `bash scripts/verify-scaffold.sh`

A green CI run is a Lean 4.12 / Mathlib 4.12 build plus the scaffold
script. It is not a DOI and not an unconditional `BealTheorem`.
Current Foundations tag `v4.0.14-coleman-integral-no-doi` does not change this
workflow.
