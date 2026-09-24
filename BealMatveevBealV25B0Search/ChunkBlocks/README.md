# Hundred-interval dispatchers

`scripts/generate_chunked10e6.py` generates 20 `Block##.lean` files. Each
imports ten group modules and dispatches to their individual certificates.
`Full10e6.lean` imports these blocks and uses quotient/remainder arithmetic
to cover every `B < 1,000,000`, then checks `B = 1,000,000` separately.

This layout keeps certificate elaboration in independent modules rather
than forming a memory-intensive Boolean conjunction.