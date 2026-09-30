# Windows Phase 3 missing facade exports

Status: isolated source repair and regression coverage prepared; runtime qualification pending.

Publication scope: fresh `origin/main` at
`5eb63efa451298e05201c06934f64b76ead7a8f8` already restores
`imported_symbol_local_name` in `_Items/lowering_helpers.spl` and uses it in
import registration. The draft PR therefore omits that duplicate source repair,
retains the additional inactive-alias regression, and restores only the two
missing I/O APIs described below. The original frozen-source diagnosis remains
applicable to its recorded revision.

The retained Phase 3 terminal log at
`D:/dev/simple-windows-corrected-early-phases-20260930-producer-hir-attempt1/stage3/compile.stderr.log`
contains 1,619 printed fatal diagnostics (the producer caps diagnostics per module).
Of these, 105 are not unresolved types. Three concrete missing public surfaces
remain on frozen source `b37de82bc50143c633379b276bbe750c0433d0e8`:

- `compiler.hir.hir_lowering.items.imported_symbol_local_name`: both HIR
  facades export it and existing compiler alias specs call it, but its body was
  removed while named import registration retained equivalent inline logic.
- `std.nogc_sync_mut.io.file_ops.file_read_bytes_i64`: the app I/O facade and
  existing SCV/render specs require it, but the canonical runtime only supplies
  the unsigned byte reader.
- `app.io.mod.dir_exists`: `std.scv.compile_snapshot` imports and calls it,
  while the app facade omitted the already implemented runtime predicate.

Restore alias selection in the owning import-resolution module and call it
from production named-import registration. Restore the i64 compatibility reader
in the canonical runtime by widening each unsigned byte, then route both I/O
facades to that owner. Re-export the existing directory predicate. No new raw
runtime boundary or consumer workaround is needed.

## Bounded regression plan

Run with a refreshed admitted self-hosted producer, once each:

1. `test/03_system/compiler/compiler_import_alias_resolution_spec.spl`: existing
   alias/no-alias cases plus an inactive nonempty alias payload.
2. `test/02_integration/app/io/restored_facade_exports_spec.spl`: actual facade
   imports, binary roundtrip across all 256 byte values, missing-file behavior,
   and existing/missing directory results. The temporary file is deleted before
   checking returned bytes.
3. Existing `test/03_system/stdlib/io/scv_render_file_read_contract_spec.spl`
   remains the broader byte compatibility contract; run only when its fixture
   prerequisites and runner are available.

Source checks: whitespace clean; executable-spec count under `doc/06_spec` is
zero. These checks are not runtime PASS. Full compiler/core/MCP qualification
belongs to the coordinated producer lane and was not rerun here.

## Remaining independent diagnostics

The earlier generic-field and static-owner changes do not directly repair the
90 printed invalid export origins through `compiler.frontend.core.__init__`,
the `std.io` missing exports, unresolved `HwFrontendRowFragment`, or the three
unresolved `_` binders. Those need separate reproduction after refreshing the
producer; this patch does not claim to clear all Phase 3 failures.
