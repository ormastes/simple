# `std.file_system` write functions are mocks that return `true` without writing

- **Filed:** 2026-09-06
- **Severity:** blocker (release critical path — `native-build` could not build a three-line hello world)
- **Status:** call site in `driver_aot_native_output.spl` FIXED; the stdlib mock itself and 11 other product-code importers remain OPEN
- **Host:** aarch64-unknown-linux-gnu, Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`

## Symptom

```
bin/simple native-build hw.spl -o hw     # three-line hello world
```

exits 1. Every lowering checkpoint reports zero errors
(`[bootstrap-error-count] point=entry|post-lowering|post-diagnostics|post-store count=0`),
the object file is produced correctly, and then the post-compile capsule
receipt check rejects it:

```
reason: native-capsule-receipt-invalid:.tmp.<...>.hw
error: build failed: 1 failed, 0 unverified, 0 not run, 0 ok of 1 unit(s)
```

## Which condition fired

`driver_native_capsule_result_valid_v1`
(`src/compiler/80.driver/driver_aot_native_output.spl`) has five independent
failure modes. **Condition 3 fired: `<object_path>.capsule-receipt` does not
exist.**

The two values, measured with temporary instrumentation on both sides of the
same build (instrumentation since removed):

```
[DBG-W] path=build/native_cache/s635.../object..tmp....hw.o.capsule-receipt
        wrote=true  len=1451  exists_after=false
[DBG-C] path=build/native_cache/s635.../object..tmp....hw.o.capsule-receipt
        exists=false  obj_exists=true  identity_valid=true
```

So the writer's `_sffi_file_write_text` returned **`true`** and
`_sffi_file_exists` on the very same path immediately afterwards returned
**`false`**. Nothing else was wrong: the object existed, the capsule identity
was valid, the paths on both sides were byte-identical.

## Root cause

`driver_aot_native_output.spl:10` imported
`use std.file_system.{file_write_text, file_read_text}`.

`std.file_system` resolves into `nogc_async_mut.file_system.file_ops`, whose
header says outright "Mock implementations for pure Simple demonstration"
(`src/lib/nogc_async_mut/file_system/file_ops.spl:5`). Its `file_write_text`
(`:58-68`) performs **no I/O at all**:

```
fn file_write_text(path: text, content: text) -> bool:
    if path == "" or content == nil:
        return false
    true
```

Reproduced in isolation, independent of the compiler driver:

```
use std.file_system.{file_write_text}
use std.io_runtime.{file_exists, file_write_exact}
...
MOCK write ok=true exists=false      # std.file_system.file_write_text
REAL write ok=true exists=true       # std.io_runtime.file_write_exact
```

This is the **second instance of a hazard the same file's own header already
documents** at `:34-40`, where `file_read_bytes` was removed for exactly this
reason: *"the flat function registry is keyed on NAME ALONE, so it could hijack
any call site in an import closure that included this module"*. The compiler
itself warns about the live collision during the build:

```
warning: public function `file_write_text` has 3 co-compiled definitions with
2 differing signatures ((text,text)->() vs (text,text)->bool); JIT call sites
resolve by exact arg-type match ... falling back to the last definition when
types are ambiguous [compiler_cross_module_private_symbol_collision]
```

### Second silent breakage from the same cause

The receipt was not the only casualty. Two other writes in the same driver used
the same mock and also vanished while reporting success:

- `phase.marker` (`:977`) — the codegen-phase forensic marker.
- `.cache_scope` (`:987`) — the lane-ownership marker that
  `scripts/check/check-cache-scope-ownership.shs` reads **fail-closed**. A
  fail-closed gate was reading a file that was never being written.

Both are present again after the fix.

## Fix applied (this change)

`src/compiler/80.driver/driver_aot_native_output.spl` only:

- dropped `use std.file_system.{file_write_text, file_read_text}`;
- `_sffi_file_write_text` now calls `std.io_runtime.file_write_exact`
  (`io_runtime.spl:250`) — the one-call honest runtime status, correct here
  because every caller writes into `cache_scope_root`, which
  `_sffi_dir_create(cache_scope_root, true)` has already created, and every
  caller treats `false` as a hard build error;
- `_sffi_file_read_text` now calls `std.io_runtime.file_read_nullable`
  (`io_runtime.spl:181`). Note: measured 2026-09-06 the real definition
  happened to win for **reads**, so the read side was fragile-by-luck, not
  observed-broken; it is moved for the same reason, and that is stated in the
  code comment rather than claimed as a fixed break.

The capsule receipt check itself was **not** weakened. It is an authenticated
cache checkpoint and still verifies identity, object existence, source
identity, fingerprint, and exact receipt text.

## Still open

1. **The mock itself.** `src/lib/nogc_async_mut/file_system/file_ops.spl` still
   exports `file_write_text`, `file_write_bytes`, `file_write_lines`,
   `file_append_text`, `file_append_lines`, `file_create`, `file_delete`,
   `file_rename`, `file_copy`, `file_move` and `file_exists` as mocks that
   report success without doing anything (`file_exists_mock` claims any path
   starting with `/` or `.` exists). Making them real changes stdlib semantics
   for every caller and needs its own reviewed change; deleting them, as was
   done for `file_read_bytes`, breaks the `use std.file_system.{...}` imports
   below. Either route is out of scope for a release-blocker fix.

2. **11 other product-code importers of the mock writers**, each a potential
   silent no-op with a `true` return (not investigated, not fixed):

   ```
   src/compiler/80.driver/driver_riscv_gen2_product.spl:9        file_write_text
   src/compiler/80.driver/driver_public_headers.spl:2            file_write_text, file_read_text
   src/compiler/80.driver/driver_api_project_build.spl:9         file_write_text
   src/compiler/80.driver/driver_vhdl_artifacts.spl:5            file_write_text
   src/compiler/80.driver/driver_compile_vhdl_source_map.spl:11  file_write_text
   src/compiler/80.driver/shb/shb_writer.spl:8                   file_move
   src/compiler/80.driver/cache/lease/lease.spl:23               file_write_text
   src/compiler/80.driver/cache/gc/fast_gc.spl:74                file_move
   src/compiler/80.driver/cache/gc/mark_sweep.spl:28             file_move
   src/compiler/80.driver/watcher/smf_manifest.spl:14            file_write_text
   ```

   `cache/lease/lease.spl` and `watcher/smf_manifest.spl` are the two worth
   looking at first: a lease file and a cache manifest that are never written
   but always report written are the same failure shape as the receipt.

3. **No gate covers this class.** Nothing fails when a stdlib function reports
   success without performing its effect. A `check-` guard that asserts
   post-conditions for the `std.file_system` write API would have caught both
   this and the `file_read_bytes` precedent.
