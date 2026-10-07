# Range index endpoint ownership

Source: `test/01_unit/compiler/frontend/open_range_slice_endpoint_spec.spl`.

- Parse `arr[1..]`: assert Index over Range, missing end node ID -1, and tree Range end nil with present start.
- Parse `arr[1..(-1)]`: assert authored endpoint has a nonnegative node ID and remains present in the tree Range.

This pins parser and flat-to-tree ownership only. It does not assert executable array-tail slicing. Before/after seed-hosted evaluator probes both reject these two forms as noninteger array indexes. Native MIR currently rejects array range indexes explicitly. That pre-existing execution gap is tracked separately.
