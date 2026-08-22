# MC/DC cross-engine vector gate

The fail-closed gate is `scripts/check/check-mcdc-cross-engine-vectors.shs`.
It compares the same frozen decision IDs, condition-evaluated masks, condition-
true masks, and outcomes over nine lanes: interpreter, JIT, and native, each in
static-off, direct static-on, and aspect-dynamic MC/DC mode. These map to the
compiler's `off`, `static`, and `dynamic` policy values respectively.

Every invocation uses `SIMPLE_NO_STUB_FALLBACK=1`. Evidence records the exact
SHA-256 identity of the admitted compiler, its admission receipt, the fixture,
the frozen manifest, and each native executable. Native executables additionally
require a sibling `<binary>.compiler.sha256` provenance file matching the
admitted compiler. Interpreter/JIT rows identify the exact compiler and source
rather than pretending that they have a standalone binary.

An unavailable or unadmitted engine is `BLOCKED`, never PASS or SKIP. The gate
retains `status.sdn`, per-lane stdout/stderr/identity files, and an exact
`resume.sh` command under `build/mcdc-cross-engine-vectors/` (or
`MCDC_XENGINE_OUT`). It does not synthesize missing engine receipts.

Current source review: the matrix is O(1) in lane count and uses bounded fixture
vectors. Each lane executes once and is compared by streaming `cmp`; there is no
quadratic lookup, full-tree scan, retry, or hot-path allocation introduced.
