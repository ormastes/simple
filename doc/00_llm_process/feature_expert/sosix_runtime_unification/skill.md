# SOSIX runtime unification feature expert

## Role

Own the lane knowledge for the unified SOSIX runtime library: one operation
lifecycle, one frozen ID table, one hosted capsule, SimpleOS binding the same
contracts. This is an LLM wiki entry, not authority to add providers or grammar.

## Current status (2026-09-05, HEAD `56d032e` + this lane, Rust-seed binary)

Done and green: contract lift (`src/os/sosix/core/*` + `fs/operation_adapter`
-> `src/lib/common/contracts/sosix/*` with shims; 56 importers untouched),
`service_ids_v1`, `error_v1`, generation exhaustion fail-closed, hosted
`fs.spl`/`sync.spl`/`time.spl` with specs (interpreter and native modes), dead
Future chain deleted (`*/src/future.spl`), dead `src/os/sosix/io.spl` deleted,
boundary gate `scripts/check/check-sosix-capsule-boundaries.shs`, reference
file provider `file_driver.spl` (real positioned I/O on this host through the
typed `std.nogc_async_mut.io` aliases), perf spec + H2 report
(`doc/10_metrics/runtime/sosix_unification_perf_report_2026-09-05.md`).
Exact POSIX leg: `rt_fd_pread`/`rt_fd_pwrite` landed in the seed source
(Rust runtime + interpreter wrappers + registry + security + C twin) with real
interpreter `rt_file_open`/`rt_file_close`; `posix.spl` + `posix_spec` 3/3 on a
privately built seed (`~/dev/.sosix-seed-lane/release/simple`), 0/3 on the
deployed seed by design. Deploying that seed is the user's decision.
Blocked (owner + resume in `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md`): exact POSIX leg (runtime externs),
Linux io_uring / macOS / Windows providers, GPU G1 proxy, SimpleOS device
queues, QEMU serial-bytes-observed row (needs pure-Simple deploy).

## Ownership and paths

| Concern | Owner/path |
|---|---|
| Lifecycle, completions, waits, descriptors, IDs, errors | `src/lib/common/contracts/sosix/{operation,completion,wait,file_operation,service_ids,error}_v1.spl` |
| SimpleOS shims | `src/os/sosix/core/*.spl`, `src/os/sosix/fs/operation_adapter.spl` |
| Hosted capsule | `src/lib/nogc_async_mut/sosix/{__init__,host_facade,fs,sync,time,file_driver,posix}.spl` (`posix` not re-exported until a deployed binary backs it) |
| Seed externs | `src/compiler_rust/runtime/src/value/sffi/file_io/descriptor.rs`, `compiler/src/interpreter_extern/{file_io,mod}.rs`, `common/src/runtime_symbols.rs`, `runtime/src/security_runtime.rs`; C twin `src/runtime/runtime_native.c`; typed aliases `src/lib/nogc_sync_mut/sffi/fs.spl` |
| Perf spec | `test/05_perf/lib/sosix_hosted_fs_perf_spec.spl` (mechanism assertions; prints ns/op) |
| Specs | `test/01_unit/lib/common/contracts/sosix/*_spec.spl`, `test/01_unit/lib/nogc_async_mut/sosix/*_spec.spl`, `test/01_unit/os/sosix/operation_core_spec.spl` |
| Gate | `scripts/check/check-sosix-capsule-boundaries.shs` (R1–R5, `--selftest`) |
| Baseline | `doc/10_metrics/runtime/sosix_unification_baseline_2026-09-05.md` |
| Lane state | `.spipe/sosix_runtime_unification/state.md` |

## Traps recorded this lane

- **Seed `u32` does not wrap**: `generation + 1` at `0xFFFFFFFF` produced
  `4294967296`, so the old wrap-to-1 branch was dead; the fix checks
  `>= SOSIX_OPERATION_GENERATION_MAX` and refuses release.
- **Class field passed as argument is a copy** in the interpreter
  (`provider.take_one(self.ring)` mutated a copy; locals/params are shared).
  Drive `self.ring` directly.
- **`ring.reserve` needs a nonzero `task_key`** (`InvalidOperationMetadata`).
- **A synchronous call must `release` on return.** The sync leg returned the
  completion value but kept the lease; a capacity-1 ring then served one call.
  Timed-out/canceled outcomes keep ownership on purpose (buffer still in flight).
- **Deployed seed facts (aarch64, 2026-09-04 build):** no fd-level pread/pwrite
  extern; `rt_driver_*` unbacked (returns nil/0); `check-startup-size-performance-audit.shs`
  Simple probe rows exit 127 here. `bin/simple run` on a top-level script that
  imports the capsule can exceed 300 s — use the test runner for probes.
- **Interpreter `rt_file_open`/`rt_file_close` were stubs** (-1/false) until
  2026-09-05; the linked C-ABI functions were real. Interpreter externs live in
  `interpreter_extern/*.rs`, separate from the `extern "C"` bodies.
- **Private seed rebuild is cheap:** `cp -a src/compiler_rust/target/release`
  to a private `CARGO_TARGET_DIR`, then `cargo build --release --bin simple`
  finished in 2 min; never build into the shared target dir or deploy unasked.
- **`native-build` needs the source inside the repo tree** ("missing importing
  module surface" from /tmp), cannot import `pub val` constants natively, and
  fails the `std.nogc_sync_mut.sffi.fs` unit at HEAD on this seed.
- **Interpreter tax:** ~640 µs per full ring cycle on the seed interpreter, ~40
  interpreted calls; no linear scan on the hot path. Ratio unified/direct read 38×.
- **A ring `cancel` on a committed slot only sets `cancel_requested`**; the
  provider must answer with `complete_cancelled`, or `SimpleRing` refuses the
  terminal (`CancellationRequired`) and the lease never retires. `service_one`
  honors the flag; `pump` retires a locally CANCELED slot without publishing.
- **`std.future` does not resolve**; the `*/src/future.spl` chain had no
  importer and was deleted, not migrated.
- Two pre-existing reds (`completion_wait_set_spec`, `io_spec`) were filed in
  `doc/08_tracking/bug/sosix_*_2026-09-05.md` and both closed the same day:
  the wait set now remembers consumed generations (bounded) so a re-watched
  generation cannot be re-notified; the io_spec grep-a-spec examples became
  behavior examples on the `io_rw` route.
- Still red and pre-existing, outside this lane's edits: `fs_service_vfs_backend_v1_spec`
  (seed parse error), `fs_service_adapter_v1_spec` (indexed field receiver), `fs_ipc_codec_v1_spec`.
