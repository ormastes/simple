# native-build --entry-closure on the seed: `transient HIR scope end failed`

Found 2026-10-20 while fixing `cannot cast object to i64` (same lane).

Root cause of `cannot cast object to i64`: `driver as i64` (production controller
`driver_hir_archive_production_controller_v1.spl:48,65,195,223,238-240`, plus
`driver_hir_pipeline_lowering.spl`, `cache/*_v1.spl` pin owners, ~30 sites) casts a
`class` to its address word. The seed interpreter has no such cast
(`interpreter/expr/casting.rs` `cast_to_numeric`). NOT fixed: an experiment mapping
`Object -> Arc::as_ptr(fields)` got past the cast (hello then reached phase3 HIR)
but Opus review showed it is wrong: the word is the field map address, and every
field write does `Arc::make_mut`, which moves it, so the driver's
`_hir_production_holds_v1[word]` lookups would miss after
`driver.x = nil`. Proper fix: a stable identity (a `CompilerDriver.identity_id`
from a global counter replacing `driver as i64`, or an interpreter object id kept
across make_mut), and arguably gate address casts to `unsafe`.

Next layer, NOT fixed: hello world with the coverage-wrapper flags
(`--backend llvm --refresh-source-authority --entry-closure --runtime-bundle
core-c-bootstrap`, `SIMPLE_SCV_INVENTORY_COLD_INIT=1`, MemoryMax=8G; 4G is
OOM-killed) now reaches phase3 HIR of `main`, then fails in
`driver_hir_pipeline_lowering.spl:549`: `driver_publish_reverse_reference_parse_scope_v1`
returns false (seal / `driver_end_transient_parse_scope` / publish; which step is
not yet isolated). Those paths assume native transient-arena runtime semantics.
`test --coverage` therefore still reports Files tracked: 0.
