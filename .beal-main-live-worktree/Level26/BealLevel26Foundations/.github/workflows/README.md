[![DOI Foundations Concept](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
[![DOI v30.1.7](https://zenodo.org/badge/DOI/10.5281/zenodo.22912430.svg)](https://doi.org/10.5281/zenodo.22912430)
[![DOI v25.0.1](https://zenodo.org/badge/DOI/10.5281/zenodo.22922473.svg)](https://doi.org/10.5281/zenodo.22922473)
[![DOI v25.0.2](https://zenodo.org/badge/DOI/10.5281/zenodo.22927972.svg)](https://doi.org/10.5281/zenodo.22927972)
[![DOI Beal-Conjecture](https://zenodo.org/badge/DOI/10.5281/zenodo.22884873.svg)](https://doi.org/10.5281/zenodo.22884873)

# Vendor workflows

[`main.yml`](main.yml) is the historical CI file from the
relocated `beal-level-26-foundations` kernel (`db7a556` /
`fea0c393`). It names foundations targets
(`BealLevel26Foundations`, scaffold). In this monorepo the
live parent CI is [`.github/workflows/main.yml`](../../../../.github/workflows/main.yml)
on `beal-conjecture`.

Do not run this vendor workflow as if it were the v26 mint
gate. Local parent checks:

```
lake build Level26
lake build HonestB0Search
```
