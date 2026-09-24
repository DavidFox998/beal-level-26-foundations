[![DOI Foundations Concept](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
[![DOI v30.1.7](https://zenodo.org/badge/DOI/10.5281/zenodo.22912430.svg)](https://doi.org/10.5281/zenodo.22912430)
[![DOI v25.0.1](https://zenodo.org/badge/DOI/10.5281/zenodo.22922473.svg)](https://doi.org/10.5281/zenodo.22922473)
[![DOI v25.0.2](https://zenodo.org/badge/DOI/10.5281/zenodo.22927972.svg)](https://doi.org/10.5281/zenodo.22927972)

# Ten-interval dispatchers

`scripts/generate_chunked10e6.py` generates 200 `Group###.lean` files. Each
imports ten individual certificates from `../Chunks/` and selects the correct
one by a bounded case split. It performs no million-value computation.

The block modules import ten groups apiece. All intervals remain half-open
and are proved only after their imported `by decide` declarations compile.