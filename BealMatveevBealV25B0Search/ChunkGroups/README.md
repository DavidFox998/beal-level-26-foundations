# Ten-interval dispatchers

`scripts/generate_chunked10e6.py` generates 200 `Group###.lean` files. Each
imports ten individual certificates from `../Chunks/` and selects the correct
one by a bounded case split. It performs no million-value computation.

The block modules import ten groups apiece. All intervals remain half-open
and are proved only after their imported `by decide` declarations compile.