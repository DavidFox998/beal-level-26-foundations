# Individual interval certificates

`scripts/generate_chunked10e6.py` generates the 2,000 `Chunked10e6_####.lean`
files here. Each imports `Chunked10e6`, then kernel-checks one interval
`[500·n, 500·(n+1))` with ordinary `by decide`. Generation alone is not a
proof: Lean must compile every file. The final interval ends at 1,000,000
exclusively; `Full10e6.lean` handles the inclusive endpoint separately.

The group modules import these files in sets of ten. Regenerate rather than
hand-editing the numbered certificates so the indices and bounds stay aligned.