# `--native` link fails on `rt_file_atomic_write`, so `std.enterprise_store` cannot be AOT-compiled

**Status:** RESOLVED in source 2026-08-17 (pending seed redeploy). Filed 2026-08-17, lane W12-A of `.spipe/simple_enterprise_suite`.

## RESOLVED (2026-08-17)

Root cause confirmed: the link-line suspicion was right, but it is the
**archive selection**, not ordering. `run_link_pass`
(`linker/native_binary/linker.rs`) resolves the runtime dir via
`NativeBinaryOptions::find_runtime_library_path_for_target`
(`linker/native_binary/options.rs:339`), which walks the exe dir /
`repo_release_artifact_path_from_dir` and the `cargo_target_paths` list —
`src/compiler_rust/target/release/deps/libsimple_runtime.a` (the **Rust**
runtime staticlib) wins before `build/simple-core`. Verified directly:
`nm -g --defined-only src/compiler_rust/target/release/deps/libsimple_runtime.a`
has **zero** `rt_file_atomic_write`, while `build/simple-core/libsimple_runtime.a`
has one — the filed "present in the archive" check inspected the archive the
link never used.

Fix: implemented `rt_file_atomic_write(path: RuntimeValue, content: RuntimeValue) -> i64`
in the Rust runtime staticlib
(`src/compiler_rust/runtime/src/value/sffi/file_io/file_ops.rs`), mirroring
the C definition's semantics exactly (empty/NUL-path rejection, parent-dir
creation, same-dir `path.tmp.<pid>.<seq>` temp file, fsync, mode preservation
on Unix, rename). Verified with `cargo check --release --bin simple` — clean.

Tests: two Rust unit tests added beside the implementation
(`test_rt_file_atomic_write_writes_and_overwrites` — the reproducing test:
symbol defined, write + overwrite, no `.tmp.*` residue — and
`test_rt_file_atomic_write_creates_parents_and_rejects_empty_path` — the
similar-problem edges shared with the C definition). Compile-verified via
`cargo check --release -p simple-runtime --tests` (check only; bootstrap owned
build resources). An end-to-end `.spl` native-link spec is **deploy-gated**:
the deployed seed predates this fix and `1f4121930a8`, so any `compile
--native` repro fails earlier at `rt_sqlite_open` until the seed is redeployed.

**Caveat (same as `1f4121930a8`):** the deployed seed
(`bin/release/x86_64-unknown-linux-gnu/simple`, mtime 2026-08-16 22:59)
predates BOTH this fix and the sqlite on-demand link fix — the repro today
fails earlier, at `rt_sqlite_open`, on that binary. End-to-end native
`store_backend_acid` measurement still awaits a seed rebuild + redeploy
(bootstrap owned the build resources when this landed).
**Severity:** blocks end-to-end native measurement of the enterprise store.

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
