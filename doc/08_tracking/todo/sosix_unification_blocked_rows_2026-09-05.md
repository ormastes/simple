# TODO: SOSIX runtime unification — blocked rows (resume conditions)

**Date:** 2026-09-05
**Status:** BLOCKED rows of an otherwise current-host-complete lane
**Lane:** `.spipe/sosix_runtime_unification/state.md` (authoritative log)
**Plan:** `doc/03_plan/agent_tasks/sosix_runtime_unification_parallel_plan_2026-09-05.md`
**Host:** aarch64 Linux, `bin/simple` = Rust seed `bin/release/aarch64-unknown-linux-gnu/simple`

Each row below stays open until fresh native PASS evidence exists. None is
excluded, skipped, or counted as PASS; the umbrella goal is incomplete while any
row is open.

| Row | Owner | Missing prerequisite (measured) | Resume command | Retained artifacts |
|---|---|---|---|---|
| C1 `rt_fd_pread`/`rt_fd_pwrite` externs | runtime lane | LANDED IN SOURCE 2026-09-05 (uncommitted): Rust seed runtime + interpreter wrappers + registry + security list + C twin; proved on a privately built seed at `~/dev/.sosix-seed-lane/release/simple` (never copied to `bin/release`). Open decision: deploy the rebuilt seed (user's call; touches every session on this box) | after deploy: `bin/simple test test/01_unit/lib/nogc_async_mut/sosix/posix_spec.spl --no-session-daemon` must be 3/3 on `bin/simple` | private seed binary; `posix_spec` 3/3 private / 0/3 deployed; bug record `interpreter_rt_file_open_close_stubs_2026-09-05.md` |
| C2 `posix.spl` exact alias | stream C | DONE 2026-09-05 (`src/lib/nogc_async_mut/sosix/posix.spl`; not re-exported from the capsule `__init__` until a deployed binary backs the pair) | same as C1 | manual `doc/06_spec/01_unit/lib/nogc_async_mut/sosix/posix_spec.md` |
| C3 disassembly gate (`pread@plt`, no wrapper symbol) | native pipeline lane | `native-build` on the private seed fails the `std.nogc_sync_mut.sffi.fs` unit even at HEAD (probe importing only `file_open`/`file_close`); worker stderr truncated, no per-unit diagnostic | once that unit native-builds: native-build a probe calling `sosix_posix_pread`, `objdump -d` for `bl <pread@plt>` and absence of `sosix_posix_pread`/`file_pread_fd` symbols; sabotage by removing `@always_inline` | `/tmp/native-build-stderr-2446270.log` (this host) |
| C4 Linux io_uring provider | runtime lane | the seed has no io_uring at all: `async_driver_sffi.rs` is a thread pool over `libc::pread` whose backend name is `rust-syscall`, and its `rt_driver_*` are not registered for the interpreter or JIT (`rt_driver_create(8)` -> 0 in both modes, 2026-09-05); the C runtime's `async_linux_uring.c` serves native builds only | after runtime io_uring externs exist and are registered: `SIMPLE_SOSIX_PROVIDER=io_uring bin/simple test test/01_unit/lib/nogc_async_mut/sosix/fs_async_spec.spl --no-session-daemon` | scratch probe `drv_probe.spl` output recorded in lane state |
| C5 macOS / Windows providers | stream C | no such host with a deployed pure-Simple binary | same specs on that host | — |
| F1 GPU G1 proxy | GPU lane | host with a real GPU + pure-Simple deploy | `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md` lanes B/C | — |
| G2 QEMU level (AC-3b) serial bytes observed | stream G | pure-Simple compiler accepted by `simple_binary_is_valid` (stage binaries SEGV, `.claude/rules/vcs.md`) | `sh scripts/check/check-sosix-qemu-matrix.shs` serial row, publish via `produce-sosix-qemu-native-pass-bundle.shs`, import via `collect-sosix-qemu-evidence.shs` | `test/01_unit/os/sosix/io_spec.spl` 9/9 unit level |
| G3 retire `io_rw.spl` onto the v1 positioned stack | stream G | AC-3b | after AC-3b PASS: rewrite + `bin/simple test test/01_unit/os/sosix/io_spec.spl --no-session-daemon` | — |
| G4 SimpleOS device-initiated queues (GQ-001..012) | SimpleOS driver lane | GQ-001 native capability report on real hardware | per `doc/01_research/runtime/sosix_unification/simple_os_gpu_queue_feature_requests_2026-09-05.md` | — |
| A5 `export use ... as` compiler fix | compiler lane | parser support | `bin/simple test test/01_unit/lib/common/contracts/sosix/service_ids_spec.spl --no-session-daemon` after the fix | shims use one-line `export use` without aliases meanwhile |
| Stage binaries (prerequisite for AC-3b, G3, F1, startup A/B) | bootstrap lane | `check-stage-binaries-runnable.shs`: FAIL — 0 executed, all tracked stage binaries are Mach-O (wrong architecture for this aarch64 Linux host, deploy-clobber) | redeploy Linux/aarch64 stage binaries, then the rows below | gate output 2026-09-05 |
| Startup audit A/B | perf lane | `check-startup-size-performance-audit.shs` Simple probe rows exit 127 on this aarch64 host (no pure-Simple binary); the tracked report is an x86_64 run | rerun on a host with a deployed pure-Simple binary, diff against `doc/09_report/startup_size_performance_audit_2026-05-27.md` | aarch64 rerun kept out of git (scratch copy) |

**Final reviewer:** a normal/highest-capability reviewer other than the author
accepts each row's PASS when it resumes.
