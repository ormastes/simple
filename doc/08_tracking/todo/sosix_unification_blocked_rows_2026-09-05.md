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
| C1 `rt_fd_pread`/`rt_fd_pwrite` externs | runtime lane | LANDED IN SOURCE 2026-09-05 (uncommitted): Rust seed runtime + interpreter wrappers + registry + security list + C twin; proved on a privately built seed, then DEPLOYED 2026-09-05 20:07 after the user said "go": `bin/release/aarch64-unknown-linux-gnu/simple` rebuilt with `--features llvm,oauth` (the deployed feature set); previous binary kept beside it as `simple.pre-sosix-2026-09-05` | after deploy: `bin/simple test test/01_unit/lib/nogc_async_mut/sosix/posix_spec.spl --no-session-daemon` must be 3/3 on `bin/simple` | private seed binary; `posix_spec` 3/3 private / 0/3 deployed; bug record `interpreter_rt_file_open_close_stubs_2026-09-05.md` |
| C2 `posix.spl` exact alias | stream C | DONE 2026-09-05; the deployed binary now backs the pair, so the `__init__` re-export can follow in a later change | same as C1 | manual `doc/06_spec/01_unit/lib/nogc_async_mut/sosix/posix_spec.md` |
| C3 disassembly gate (`pread@plt`, no wrapper symbol) | native pipeline lane | `native-build` fails on this host for ANY input — a two-line `fn main() -> i64: 42` with no imports fails identically (control run 2026-09-06). The earlier "the sffi.fs unit fails" reading was too narrow. Record: `doc/08_tracking/bug/native_build_fails_on_hello_world_aarch64_2026-09-06.md` | once that unit native-builds: native-build a probe calling `sosix_posix_pread`, `objdump -d` for `bl <pread@plt>` and absence of `sosix_posix_pread`/`file_pread_fd` symbols; sabotage by removing `@always_inline` | `/tmp/native-build-stderr-2446270.log` (this host) |
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

## Todo DB rows

`bin/simple todo-scan` picks these up, so every blocked row below becomes a Todo
DB row. The regenerated `doc/08_tracking/todo/todo_db.sdn` is deliberately NOT
part of this change: measured 2026-09-06, regenerating it moves ~170 rows that
have nothing to do with this lane, because origin's committed copy has drifted
from origin's own sources. Sweeping that into a feature change would bury it.
Whoever owns the tracking files should re-run the scan on its own.

These five rows have no natural source site, so they are recorded here for
`bin/simple todo-scan`. The other four (C3, C4, C5, G3) carry their `# TODO:`
at the code site where the work lands.

# TODO: (sosix F1) land the GPU G1 proxy storage slice on a host with a real GPU and a deployed pure-Simple binary; resume via doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md lanes B/C

# TODO: (sosix AC-3b) prove the QEMU serial row with observed bytes once a pure-Simple compiler accepted by simple_binary_is_valid is deployed; publish via produce-sosix-qemu-native-pass-bundle.shs and import via collect-sosix-qemu-evidence.shs

# TODO: (sosix G4) implement the SimpleOS device-initiated queues GQ-001..012 after the GQ-001 native capability report on real hardware

# TODO: (sosix startup-ab) re-run check-startup-size-performance-audit.shs on a host where its Simple probe rows do not exit 127, and diff against doc/09_report/startup_size_performance_audit_2026-05-27.md

# TODO: (sosix A5) drop the one-line `export use` shims for aliased re-exports once the compiler accepts `export use ... as`; until then every shim in src/os/sosix/core re-exports without renaming
