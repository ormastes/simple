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

## Corrected-producer component attempt

On 2026-09-30, the immutable Windows producer with SHA-256
`cbe4a8df41e14287005e258cf57f8e16bd096dee0c09954b39495446e5ab19cc`
compiled the new `test/fixtures/native_io_facade_exports/main.spl` entry against
this PR's real source modules. The fixture checks every byte value 0..255,
missing-file behavior, and existing/missing directories through `app.io.mod`.

Qualification status: **BLOCKED, no fixture execution and no runtime PASS**.
The pure-Simple positional route processed 75 HIR modules, then exited 1 after
40.10 seconds with four `unresolved type: SdnSpan` diagnostics in
`src/lib/common/sdn/value.spl`. That module declares `pub class SdnSpan` itself;
the failure is not evidence that the new I/O facade imports are missing.
The HIR cache recorded 0 hits, 75 misses and 74 stores.

Evidence root (local, retained):
`D:/dev/simple-windows-stale-facades-20260930/build/native_probe/phase2/cbe4a8df41e14287005e258cf57f8e16bd096dee0c09954b39495446e5ab19cc/facade-entry/`.
`build3.started.json` records the pure positional arguments; `build3.result.json`
records terminal exit; `build3.stdout.log` and `build3.stderr.log` retain the
diagnostics. The runtime authority is the reviewed retained
`stage2-runtime-authority` under `simple-windows-hir-shared-fixes-20260930`.

The preceding `build` and `build2` attempts used explicit `--entry` and `--source`.
Route review established that those arguments select the embedded Rust
coordinator when `SIMPLE_BOOTSTRAP_STAGE3` is unset, despite
`SIMPLE_NO_BOOTSTRAP_DELEGATE=1`. Their compile/link diagnostics are unqualified
Rust-backed observations and **must not be counted as self-hosted evidence**.
The positional attempt used a separate `cache-pure` directory and no explicit
entry/source flags. No Rust seed binary was invoked. Work stopped at the
three-attempt limit without further fixture builds.
