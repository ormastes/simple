# `--native` link fails on `rt_file_atomic_write`, so `std.enterprise_store` cannot be AOT-compiled

**Status:** RESOLVED 2026-08-17, lane W13-A of `.spipe/simple_enterprise_suite`.
**Severity:** blocked end-to-end native measurement of the enterprise store.

## Root cause (lane W13-A, with link-line evidence)

The archive W12-A inspected was never on the link line. With
`SIMPLE_LINKER_DEBUG=1` the failing single-file `--native` link is:

```
ld.lld ... main.o _main_shim.o build/simple-sqlite/runtime_sqlite.o crtn.o \
  -L <seed target>/release/deps ... -Bstatic -lsimple_runtime -Bdynamic -lc ... -lsqlite3
```

`-lsimple_runtime` resolves from the seed's cargo `deps/` directory — the
**Rust** `libsimple_runtime.a` staticlib built from
`src/compiler_rust/runtime`, chosen because
`NativeBinaryOptions::find_runtime_library_path_for_target` prefers
`exe_dir/deps` (the seed's own cargo dir) over `build/simple-core`. That
crate never defined `rt_file_atomic_write` — measured:
`nm -g --defined-only <target>/release/deps/libsimple_runtime.a` shows
`T rt_file_write_text_at` (3 defs) and **zero** `rt_file_atomic_write`. The C
`build/simple-core/libsimple_runtime.a` (from `runtime_native.c`) does define
it, but that archive is only used when the cargo dirs are absent — so W12-A's
"present in the archive" check looked at the wrong archive. Not gc-sections,
not name mangling, not link order.

**Fix (Rust seed edit, no pure-Simple path exists — the missing symbol lives
in the Rust runtime crate the seed links):** implement
`rt_file_atomic_write(path: i64, content: i64) -> i64` in
`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs`, mirroring the
C semantics (parent-dir creation, unix mode preservation, temp+fsync+rename,
1/0 return). Gate extended: `scripts/check/check-store-open-acid.shs` now has
a second stage that AOT-compiles
`test/fixture/enterprise_store/store_native_acid_probe.spl` (which imports
`std.enterprise_store` itself) and requires `store_acid=true` from the native
binary.

## Symptom

Any single-file `compile --native` of a program that imports
`std.nogc_sync_mut.enterprise_store.store` fails:

```
error: codegen: undefined symbol: rt_file_atomic_write
```

The store module imports `enterprise_store/file_backend.spl` (the SimpleOS
in-guest fallback), which calls `rt_file_atomic_write`. The import is
unconditional, so the symbol is required even when the program only ever uses
the sqlite backend.

## What is NOT the cause (checked)

- The symbol is **defined**: `src/runtime/runtime_native.c:9374`, declared in
  `src/runtime/runtime.h:836`.
- It is **present in the archive the failing link builds**:
  `ar t build/simple-core/libsimple_runtime.a` lists `runtime_native.o`, and
  `nm -g --defined-only build/simple-core/libsimple_runtime.a` shows one
  `T rt_file_atomic_write`. There is exactly one `.a` under `build/`.
- Registering a `RuntimeFuncSpec` for it in
  `compiler/src/codegen/runtime_sffi.rs` does **not** fix it — tried, rebuilt
  the seed, identical failure, change reverted rather than left in unverified.
  The message text comes from `linker/native.rs:628` parsing real linker
  stderr (`LinkerError::UndefinedSymbol`, `linker/error.rs:46`), not from a
  codegen symbol table, despite the `codegen:` prefix the driver prints.

So the remaining suspect is the **link line** — order/`--as-needed`/which
archive is actually passed for the single-file `--native` path
(`build_core_c_runtime_library`, `include_stage4_hosted = false`) — the same
family of defect as the `rt_sqlite_open` blocker fixed at `1f4121930a8`. Not
diagnosed further; lane W12-A was out of budget and this is not its frontier.

## Consequence

`store_backend_acid()` cannot be read from a real AOT-native binary today. Lane
W12-A therefore proved the layer underneath instead: the fixture
`test/fixture/enterprise_store/store_open_acid_probe.spl` replays
`store_open()`'s exact prologue and probe against `sqlite_sffi` directly, and
`scripts/check/check-store-open-acid.shs` reports
`PASS — 8 stage(s) checked, probe_backend_acid true at every stage`. What
remains unmeasured is only the last hop: the `EnterpriseStore` struct field
itself, natively.

## Repro

Any `.spl` with `use std.nogc_sync_mut.enterprise_store.store` reproduces it:

```sh
rm -rf build/simple-core
<seed>/simple compile <that file> --native -o /tmp/x
```
