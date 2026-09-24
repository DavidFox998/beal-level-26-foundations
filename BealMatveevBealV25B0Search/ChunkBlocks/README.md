[![DOI Foundations Concept](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
[![DOI v30.1.7](https://zenodo.org/badge/DOI/10.5281/zenodo.22912430.svg)](https://doi.org/10.5281/zenodo.22912430)
[![DOI v25.0.1](https://zenodo.org/badge/DOI/10.5281/zenodo.22922473.svg)](https://doi.org/10.5281/zenodo.22922473)
[![DOI v25.0.2](https://zenodo.org/badge/DOI/10.5281/zenodo.22927972.svg)](https://doi.org/10.5281/zenodo.22927972)

# Hundred-interval dispatchers

`scripts/generate_chunked10e6.py` generates 20 `Block##.lean` files. Each
imports ten group modules and dispatches to their individual certificates.
`Full10e6.lean` imports these blocks and uses quotient/remainder arithmetic
to cover every `B < 1,000,000`, then checks `B = 1,000,000` separately.

This layout keeps certificate elaboration in independent modules rather
than forming a memory-intensive Boolean conjunction.