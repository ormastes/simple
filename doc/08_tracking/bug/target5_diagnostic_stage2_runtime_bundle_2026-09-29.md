# Target 5 diagnostic compiler cannot link with staged core runtime bundle

Status: partially resolved. A current-source diagnostic compiler now links and
passes a hello `--check` smoke; full CLI Stage4 qualification remains open. The
focused 48-unit declaration accessor regression passes.

Using the staged pure-Simple compiler with `--entry-closure`, `--threads 8`,
`--source src/compiler`, `--source src/lib`, and entry
`src/compiler/80.driver/main.spl` got past source compilation but failed at
native link. The linker reported 122 generated-code runtime references without
definitions, including `rt_cranelift_*`, `rt_file_view_*`,
`rt_pinned_archive_*`, `rt_driver_*`, and `rt_process_run_with_limits`. The
bounded run ended after 133.36 seconds with 3,558,148 KiB peak RSS. No
diagnostic compiler binary was produced, so the full CLI was not run.

An earlier eight-thread compile stopped in `pipeline_fn.spl` because the
staged LLVM compiler could not materialize `OptimizationConfig` through the
`compiler.mir_opt` facade. Importing the enum from its defining
`mir_opt_integration.spl` module got compilation to the link boundary. A
four-thread attempt timed out at 180 seconds before link; it did not yield a
verdict on the enum or runtime bundle.

Next step: select or build an admitted runtime bundle that actually defines
the listed symbols for this compiler entry, then rebuild with entry closure
and run the full CLI parse, Stage4 symbol, size, and startup checks. Do not
use `SIMPLE_ALLOW_UNRESOLVED_RUNTIME=1`: that would leave NULL GOT entries and
could crash at first use. Keep the PR draft until the end-to-end run passes.

## Bundle-path check

The available `libsimple_native_all.a` defines 108 of the 122 missing names,
but passing its directory with `--runtime-bundle host-gpu --runtime-path` to
the September 8 staged compiler still produced exactly the same 122-symbol
link failure (17.22 seconds, 1,369,464 KiB peak RSS). The staged tool did not
admit that archive as a provider for this entry. A newer September 27 Rust
seed was used only for bootstrap of a current-source diagnostic compiler; it
passed JIT setup but timed out at 240 seconds before native output, with RSS
near 1.3 GiB. Neither run produced a diagnostic compiler or full CLI proof.

The next build route needs a current, admitted pure-Simple bootstrap compiler
and an explicitly verified runtime provider binding. Merely supplying a path
to the old staged tool does not fix the link.

## Dynamic-runtime adapter mismatch

The September 8 direct pure-Simple compiler artifact rejected
`--runtime-bundle dynamic-runtime` at argument admission, before compilation.
Its `rt_native_build` adapter listed only `auto`, `simple-core`,
`core-c-bootstrap`, `host-gpu`, and `runtime`. The Rust native-project CLI
already accepts `dynamic-runtime` and restricts its use to the authorized
Stage4 compiler entry. The source FFI adapter now accepts the same names and
delegates entry authorization to that existing link check. This source change
does not update the deployed September 8 binary; a new pure-Simple bootstrap
candidate is still required before rerunning the diagnostic compiler build.

A separate probe through the main checkout's `bin/release` binary is excluded
from qualification: that binary identifies itself as a Rust bootstrap seed and
its JIT could not resolve `rt_file_read_regular_no_follow_bounded_bytes` from
this newer source tree. It timed out after 220 seconds without producing a
compiler. A focused Cargo unit test for the adapter is currently blocked at
dependency resolution: the locked `inkwell 0.9.0` lacks the requested
`llvm23-1-force-static` feature. Do not treat this as a test PASS.

A static owner comparison against that September 27 bootstrap directory finds
107 of the 122 previously reported undefined names in its shared runtime or
compiler backfill archive. Fifteen have no definition in either: ten
`rt_net_*` names, `rt_tcp_connect`, `rt_execute_native`, and three
`spl_cranelift_*_v2` names. `rt_execute_native` exists in `native_all`, which
the Stage4 core lane must not absorb. The prior 122-name scan is object-wide;
strict section-GC linking must determine which of these fifteen are live.
This static comparison does not claim a successful link.

## Current-source dynamic lane retry (2026-09-29)

The immutable Stage2 pure-Simple compiler capsule
`d57b8ff1c676c0e250f76f713a5e8e5b0bbf3d91fd72741698e8fe0f26ad033c`
also rejects `--runtime-bundle dynamic-runtime` during argument parsing. The
rejection is immediate and therefore says nothing about the selected shared
runtime's ABI or link completeness.

To exercise the updated source, a separate, cache-backed Rust bootstrap driver
was built from this worktree (`simple` SHA-256
`23c1f72f4436dd03a879fa54c893e8474fd964b9cd55dd5006e3511a19c13a45`).
The bootstrap driver build completed in 82.61 seconds with 3,832,192 KiB peak
RSS. It is bootstrap tooling, not the final pure-Simple runtime candidate.

That driver accepts the named dynamic lane. Its first Stage4 attempt required
`SIMPLE_SCV_INVENTORY_COLD_INIT=1` for a new checkout. The cold-initialized,
no-stub attempt used `--entry-closure`, eight threads, the explicit shared
runtime path, and a cache scoped to the driver hash. It timed out at 360 seconds
during parsing, at 87 of 821 files; the reported parse phase had reached
278,604 ms. It never reached runtime selection or link, and produced no Stage4
compiler. Logs are under `build/mini_builds/target5_stage4_dynamic_compiler*`.

The next attempt must keep the hash-scoped cache and cold inventory state, and
address the Stage4 parse throughput or use an admitted current pure-Simple
producer before an end-to-end link/size/startup claim can be made. A stale
Stage2 binary cannot test the dynamic lane. No size or startup result is
implied by this retry.

## Current-source provider and lane dispatch (2026-09-29)

The same worktree's Rust bootstrap build produced a current-source shared
runtime (`libsimple_runtime.so`, 10,072,672 bytes) and compiler backfill
archive (`libsimple_compiler_backfill.a`, 41,370,356 bytes). Both Cargo builds
passed. The backfill archive defines the three previously absent
`spl_cranelift_*_v2` names. This is provider availability evidence, not a
Stage4 link or runtime size result. The object-wide missing-symbol list still
includes `rt_net_*`, `rt_tcp_connect`, and `rt_execute_native`; section-GC
linking must determine whether any are live.

The Stage4 compiler entry additionally requires
`SIMPLE_COMPILER_ENTRY_STAGE4=1` and an explicit runtime path containing
`libsimple_compiler_backfill.a`. The previous long parse attempt omitted that
authorization variable, so even completion of parsing would not have proved
the intended lane. The next compiler attempt must include it.

The lane dispatch guard now accepts `SIMPLE_LANE_CHECK_BACKEND=cranelift` for
diagnosis while retaining `llvm-lib` as its default. With the current Rust
bootstrap driver, the Cranelift check passed all three assertions: bundle
name accepted, non-Stage4 use rejected, and the core-C control fixture built.
The default LLVM check remains unqualified on this host: `llvm-config-23`
reports 23.1.0, while `aya-llvm-sys` admits 23.1.1 or native Linux/FreeBSD
23.1.2. The LLVM-enabled seed build stopped at that pinned-version check.
This does not qualify a Stage4 compiler binary, startup, or size gate.

## Current-source pure-Simple Stage4 compiler (2026-09-29)

A September 27 pure-Simple Stage2 capsule built the current-source
`src/app/cli/bootstrap_main.spl` with a diagnostic `simple-core` link to the
current `libsimple_native_all.a`. The resulting 42,163,336-byte intermediate
bootstrap tool passed the Cranelift dynamic-lane dispatch check: three
assertions, including denial outside Stage4. The archive was used only to
construct this bootstrap tool; its size is not a Stage4 product result.

That tool compiled the current `src/compiler/80.driver/main.spl` entry closure
with `--runtime-bundle dynamic-runtime`, explicit shared runtime/backfill
provider path, `SIMPLE_COMPILER_ENTRY_STAGE4=1`, no-stub mode, and the host
`aarch64-unknown-linux-gnu` target. It compiled 860 units with no source
failures and linked in 60.58 seconds at 1,761,976 KiB peak build RSS. The
unstripped executable is 23,067,424 bytes. It depends on
`libsimple_runtime.so.0`; the current shared runtime is 10,072,672 bytes
unstripped. The executable's `--version` and a hello-source `--check` both
exit zero. The first attempt supplied an x86_64 target on this ARM64 host and
failed at the expected incompatible-object link boundary; it is not a source
or ABI failure.

The same entry closure was built with `--runtime-bundle simple-core` and the
current `libsimple_native_all.a` as a **diagnostic** static comparator. That
archive is hosted bootstrap material, not an admitted production core. A
stripped deployment comparison and 30 paired startup/RSS samples are in
`doc/09_report/compiler/target5_stage4_dynamic_vs_static_diagnostic_2026-09-29.md`.
This resolves the missing diagnostic compiler but does not qualify the full
CLI, zero optional-provider startup, matched hello size, an admitted runtime
baseline, or Phase 7 release receipts. Keep the PR draft.
