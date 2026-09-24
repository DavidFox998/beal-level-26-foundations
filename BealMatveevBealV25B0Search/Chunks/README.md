[![DOI Foundations Concept](https://zenodo.org/badge/DOI/10.5281/zenodo.22379293.svg)](https://doi.org/10.5281/zenodo.22379293)
[![DOI v30.1.7](https://zenodo.org/badge/DOI/10.5281/zenodo.22912430.svg)](https://doi.org/10.5281/zenodo.22912430)
[![DOI v25.0.1](https://zenodo.org/badge/DOI/10.5281/zenodo.22922473.svg)](https://doi.org/10.5281/zenodo.22922473)
[![DOI v25.0.2](https://zenodo.org/badge/DOI/10.5281/zenodo.22927972.svg)](https://doi.org/10.5281/zenodo.22927972)

# Individual interval certificates

`scripts/generate_chunked10e6.py` generates the 2,000 `Chunked10e6_####.lean`
files here. Each imports `Chunked10e6`, then kernel-checks one interval
`[500·n, 500·(n+1))` with ordinary `by decide`. Generation alone is not a
proof: Lean must compile every file. The final interval ends at 1,000,000
exclusively; `Full10e6.lean` handles the inclusive endpoint separately.

The group modules import these files in sets of ten. Regenerate rather than
hand-editing the numbered certificates so the indices and bounds stay aligned.