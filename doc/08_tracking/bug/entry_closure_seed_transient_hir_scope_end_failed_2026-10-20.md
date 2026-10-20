# native-build --entry-closure on the seed: `transient HIR scope end failed`

Found 2026-10-20 while fixing `cannot cast object to i64` (same lane).

Fixed here: `driver as i64` (HIR production controller and cache owners) failed in
the seed interpreter. `cast_to_numeric` now returns the object's identity word
for `Object`/`ClassInstance` -> `i64`/`u64`. Caveat: the interpreter carries
`class` values as `Object` whose field map is copy-on-write, so the word is
stable only until the value is mutated through a copy. A stable
`CompilerDriver` id field would remove the dependence on addresses.

Next layer, NOT fixed: hello world with the coverage-wrapper flags
(`--backend llvm --refresh-source-authority --entry-closure --runtime-bundle
core-c-bootstrap`, `SIMPLE_SCV_INVENTORY_COLD_INIT=1`, MemoryMax=8G; 4G is
OOM-killed) now reaches phase3 HIR of `main`, then fails in
`driver_hir_pipeline_lowering.spl:549`: `driver_publish_reverse_reference_parse_scope_v1`
returns false (seal / `driver_end_transient_parse_scope` / publish; which step is
not yet isolated). Those paths assume native transient-arena runtime semantics.
`test --coverage` therefore still reports Files tracked: 0.
