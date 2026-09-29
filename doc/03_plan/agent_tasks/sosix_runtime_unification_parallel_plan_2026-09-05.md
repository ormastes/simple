# SOSIX Runtime Library Unification — Parallel Implementation Plan

**Date:** 2026-09-05
**Status:** In progress (research verified against `56d032e6f0d`; paths checked 2026-09-05). **Done 2026-09-05:** H0, A1, A2, A3, A4, B1 (by deletion), B2, B3, B4, D1, G1, G2 unit level (AC-3a), H1 script (manifest row pending), E1 (no edit needed: `screen_host.spl` carries no host calls). **Done 2026-09-05 (late):** B5 hosted file provider (`file_driver.spl`, real positioned I/O on this host over the typed `std.nogc_async_mut.io` aliases; 3/3 interpreter + native), H1 manifest row (advisory), H2 perf report (`doc/10_metrics/runtime/sosix_unification_perf_report_2026-09-05.md`), two defects fixed (sync-leg slot leak, cancel lease leak; bug records). **Done 2026-09-05 (evening):** C1 (`rt_fd_pread`/`rt_fd_pwrite` in the seed runtime + interpreter + C twin, plus real interpreter `rt_file_open`/`rt_file_close`; proved on a privately built seed, NOT deployed), C2 (`posix.spl`, `posix_spec` 3/3 on the private seed, 0/3 on the deployed seed by design). **Blocked (measured, resume rows in `doc/08_tracking/todo/sosix_unification_blocked_rows_2026-09-05.md`):** A5, C3 (native-build of the `std.nogc_sync_mut.sffi.fs` unit fails at HEAD on this seed), C4 (no io_uring in the seed; driver backend is `rust-syscall`), C5, F1, G2 QEMU level (AC-3b), G3, G4, startup-audit A/B. Deploying the rebuilt seed is the user's decision. Current-host scope complete; umbrella goal open on those rows. Authoritative progress log: `.spipe/sosix_runtime_unification/state.md`.
**Design:** `doc/05_design/runtime/sosix_runtime_unification_design.md` (§ numbers refer to it)
**Research:** `doc/01_research/runtime/sosix_unification/README_tldr.md` (+ three verbatim passes)
**Lane:** `.spipe/sosix_runtime_unification/state.md`
**Audience:** written so Sonnet- or Haiku-class agents can execute each task independently.

## 0. How to read this plan

- **Streams A–H** are independent workspaces; tasks inside a stream are ordered, tasks across streams depend only on what `deps:` names. Anything with no unmet deps starts now, in parallel.
- Every task states: files touched, exact steps, a **budget** (perf/structure, design §7), and a **verify** command whose output is pasted into the task report (`doc/09_report/`). Single-file `bin/simple test <spec> --no-session-daemon`; read the `Results:` line; never a directory run; never `tail -1`.
- Bracket every measurement with `readlink -f bin/simple && stat -c '%s %y' "$(readlink -f bin/simple)"` before and after. `bin/simple` is currently the Rust **seed** (aarch64); attribute evidence accordingly and never switch a lane to the seed as a workaround.
- **Model routing:** `[haiku-ok]` mechanical/spec-following, small blast radius. `[sonnet]` design judgment or multi-file reasoning. Escalate when unsure.
- Repo rules: no placeholder bodies, no `pass_todo`, no new `extern fn rt_*` outside owner modules (record `runtime_need/facade_checked/chosen_path/rejected_shortcuts` in the lane state first), file gaps in `doc/08_tracking/bug/` with file:line, specs are executable SSpec under `test/` with generated manuals under `doc/06_spec/`. New `.spl` files ≤ 300 lines. Lint one file at a time.
- **Path drift:** if a path below has moved, grep the named symbol first, record the correction in the task report, do not create a parallel copy.
- **Blob-first landing:** `git hash-object -w <file>` immediately after writing; a concurrent session's reconcile can wipe an unstaged file (spipe skill § shared working tree).

## 1. Dependency graph

```
H0 (baseline B0) ──────────────────────────────────────────────┐
A1 (lift core -> common/contracts/sosix + shims) ─► A2 (ids) ─► A3 (error) ─► A4 (exhaustion fail-closed)
A1 ─► B1 (canonical Future + shims) ─► B2 (fs.spl async) ─► B3 (sync.spl) ─► B4 (time.spl)
A2,A3 ─► B2
B2,B3 ─► D1 (interp/native parity) ─► D2 (compiler host I/O consumer slice)
A1 ─► G1 (delete io.spl dup) ─► G2 (io_rw onto wait_v1 + v1 stack) ─► G3 (retire io_rw)
A2 ─► E1 (screen_host -> host service IDs) ─► E2 (draw_ir submit/drain split)
C1 (runtime rt_fd_pread/pwrite, runtime-owned) ─► C2 (posix.spl) ─► C3 (disassembly gate)
A5 (export use ... as fix, compiler lane) independent; unblocks C2 zero-wrapper form
H1 (ratchet + closure gates) after A1; H2 (perf report) after B3,C3,G3
F* (GPU proxy), C4 (io_uring), C5 (macOS/Windows), G4 (device queues) = BLOCKED rows, §6
```

## 2. Stream A — Contract capsule (schema owner; other streams build against A1's names)

**A1. Lift `src/os/sosix/core/` into `src/lib/common/contracts/sosix/`** `[sonnet]` `deps: none`
- Files: new `src/lib/common/contracts/sosix/{operation_v1,capability_ref_v1,completion_v1,wait_v1,file_operation_v1,__init__}.spl`; rewrite `src/os/sosix/core/{operation,capability_ref,completion,completion_queue,wait_set,sync_wait_adapter}.spl` and `src/os/sosix/fs/operation_adapter.spl` to one-line `export use std.common.contracts.sosix.<x>.*` shims; `src/os/sosix/core/__init__.spl` keeps its current explicit export list but sources it from the shims (it is the hub the 56 importers use).
- Steps: `operation.spl` and `capability_ref.spl` import nothing and move verbatim. `completion.spl`, `completion_queue.spl`, `wait_set.spl`, `sync_wait_adapter.spl`, and `fs/operation_adapter.spl` import sibling `os.sosix.core.*` modules only: move the bodies and rewrite those `use` lines to `std.common.contracts.sosix.<x>` (verify the import set first with `grep -n '^use ' src/os/sosix/core/*.spl src/os/sosix/fs/operation_adapter.spl`; anything importing `os.kernel.*` stops the task). `completion_v1` = `completion.spl` + `completion_queue.spl`; `wait_v1` = `wait_set.spl` + `sync_wait_adapter.spl` (if a merged file exceeds 300 lines keep them separate and say so). Keep every `pub`/`export` name identical. Pure move commit, separate from any behavior change.
- Budget: `bin/simple deps normal src/lib/common/contracts/sosix/__init__.spl` exclusive ≤ 8 files; 56 importers of `os.sosix.core.*` unchanged.
- Verify: `bin/simple test test/01_unit/os/sosix/operation_core_spec.spl --no-session-daemon` and `bin/simple test test/01_unit/os/sosix/completion_wait_set_spec.spl --no-session-daemon` (unchanged specs, still green through the shims) and `bin/simple deps fast src/os/sosix/fs/registered_buffer_client_v1.spl` (no new cycles).

**A2. Frozen service-ID table** `[haiku-ok]` `deps: A1`
- Files: new `src/lib/common/contracts/sosix/service_ids_v1.spl`; new spec `test/01_unit/lib/common/contracts/sosix/service_ids_spec.spl`.
- Steps: constants exactly as design §4.4 (`0x0001..0x0003`, `0x0101..0x0103`, `0x0201..0x0204`, `0x0301..0x0302`, `0x1001`, `0x1002`, `0x1101`, `0x1201`), `sosix_service_id_is_known(id) -> bool`, `sosix_service_ids_all() -> [u32]`. Then try to make `file_operation_v1.spl` and `src/os/sosix/host/service_contract.spl` import their IDs from here instead of redeclaring. E0410 caveat: re-exporting an imported `pub val` needs `export use ...` and the wildcard-import gap is documented; probe with a 5-line fixture first. If the re-export does not bind, keep the redeclarations and rely on the equality spec below as the gate (values must not change either way).
- Spec: table is duplicate-free; every literal in the two `src/os` files equals the table; `is_known(0x0104)` is false. Sabotage arm: duplicate an ID, spec goes red.
- Verify: `bin/simple test test/01_unit/lib/common/contracts/sosix/service_ids_spec.spl --no-session-daemon`.

**A3. `SosixError` vocabulary** `[haiku-ok]` `deps: A1`
- Files: new `src/lib/common/contracts/sosix/error_v1.spl` + `test/01_unit/lib/common/contracts/sosix/error_spec.spl`.
- Steps: `enum SosixErrorKind { Unsupported, InvalidCapability, InvalidBuffer, QueueFull, Canceled, TimedOut, Native }`, `struct SosixError { kind, native_domain: u8, native_code: i32, transferred: u64 }`, `sosix_error_from_status(status: i32) -> SosixError` mapping `-11 -> QueueFull`, `-125 -> Canceled`, `-110 -> TimedOut`, other negatives -> `Native` (the one mapping G2's `-11` relies on), `sosix_error_describe(e) -> text` (only formatter; no `text` field). Generics `<>`, no inheritance.
- Spec: round trip of every kind; `describe` never called on the constructor path (assert struct has no text field by construction).
- Verify: `bin/simple test test/01_unit/lib/common/contracts/sosix/error_spec.spl --no-session-daemon`.

**A4. Generation exhaustion fails closed** `[sonnet]` `deps: A1`
- Files: `src/lib/common/contracts/sosix/operation_v1.spl`; extend `test/01_unit/os/sosix/operation_core_spec.spl`.
- Steps: replace the wrap-to-1 branch in `sosix_operation_release` with `accepted: false, reason: "generation-exhausted"` when `slot.generation == 0xFFFFFFFF`; slot remains terminal. Write the spec FIRST, watch it fail with the current wrap, then fix (reproduce-first rule).
- Verify: `bin/simple test test/01_unit/os/sosix/operation_core_spec.spl --no-session-daemon` reporting both the new example and the pre-existing count.

**A5. Renaming re-export (`export use m.f as g`) resolver fix** `[sonnet]` `deps: none` — compiler lane
- Files: pure-Simple resolver first (`src/compiler/10.frontend/core/interpreter/module_loader_core.spl`, locate by grepping `export use`); Rust seed only if evidence shows the pure layer delegates correctly. Bug record: `doc/08_tracking/bug/no_renaming_re_export_blocks_zero_cost_facade_alias_2026-09-03.md` (claim it before editing).
- Steps: reproduce with the 30-second fixture in the bug record (`E1002`); bind alias to the same declaration identity, no wrapper emitted; cover ordinary import, public re-export, chained alias, interpreter and native.
- Verify: fixture prints `2` under `bin/simple run` in interpreter and native modes; new spec under `test/01_unit/compiler/module_system/renaming_reexport_spec.spl`. Until green, C2 uses `@always_inline` and this row stays open.

## 3. Stream B — Library capsule (`std.nogc_async_mut.sosix`)

**B1. One canonical Future** `[sonnet]` `deps: A1`
- Files: `src/lib/nogc_async_mut/async/future.spl` (canonical), `src/lib/nogc_async_mut/async_host/future.spl` (executor variant, keep), `src/lib/nogc_sync_mut/src/future.spl` (159 lines, third real implementation: synchronous, type-erased `fn(Any)` callbacks), `src/lib/nogc_async_mut/src/future.spl` and `src/lib/gc_async_mut/src/future.spl` (re-export the canonical `std.async.future`, not `nogc_sync_mut.src.future`), `future_compat_adapter.spl` (unchanged).
- Steps: list every exported name of `nogc_sync_mut/src/future.spl` and every importer (`/usr/bin/grep -rn 'nogc_sync_mut.src.future\|std.src.future' src test --include=*.spl`); fold what the canonical lacks into the canonical, migrate importers, then make the file a re-export shim or delete it. Three real implementations become one canonical plus one executor variant. Record the tier-rule wrapper direction in the file headers.
- Budget: `deps normal` on any importer of `std.async.future` shows no closure growth.
- Verify: `bin/simple test test/01_unit/lib/nogc_async_mut/async_ring/simple_ring_spec.spl --no-session-daemon` plus the existing future spec (locate: `find test/01_unit -name '*future*_spec.spl'`), both unchanged and green.

**B2. `fs.spl` async positioned I/O over `SimpleRing`** `[sonnet]` `deps: A2, A3, B1`
- Files: new `src/lib/nogc_async_mut/sosix/{fs,provider,__init__}.spl`; new spec `test/01_unit/lib/nogc_async_mut/sosix/fs_async_spec.spl`.
- Steps: `sosix_fs_read_at(file: SosixCapabilityRef, buffer: SosixBufferRef, file_offset, buffer_offset, length, deadline_ns) -> Future<Result<SosixCompletion, SosixError>>`; body = validate via `sosix_file_operation_create` from `std.common.contracts.sosix.file_operation_v1` (lifted in A1; `length == 0` rejected as today; never re-implement the rules), `SimpleRing` reserve+commit on `SosixHostedProvider` (= `SoftwareRingProvider`), store `RingToken` in the operation record, `poll` via `poll_future_compat`. Rejection returns a value; no slot, no allocation. Completion path: `RingCompletion` -> `sosix_operation_complete` -> `SosixCompletionQueue`. Lease release before `sosix_operation_release` (design §4.1).
- Spec (all with the software provider): completion-before-poll is not lost; stale generation cannot complete; queue-full -> `QueueFull`; timeout then late completion cannot release the lease; sibling task keeps progressing while one op is pending. Sabotage: release the lease before completion, spec red.
- Budget: `SoftwareProviderCounters` shows 1 reserve/1 commit per op; allocation counter zero after ring creation; file ≤ 300 lines.
- Verify: `bin/simple test test/01_unit/lib/nogc_async_mut/sosix/fs_async_spec.spl --no-session-daemon`.

**B3. `sync.spl` typed synchronous adapter** `[sonnet]` `deps: B2`
- Files: new `src/lib/nogc_async_mut/sosix/sync.spl`; spec `test/01_unit/lib/nogc_async_mut/sosix/fs_sync_spec.spl`.
- Steps: `sosix_sync_fs_read_at(...) -> Result<SosixCompletion, SosixError>`: same reserve/commit as B2, then `SosixSyncWaitAdapter` (`wait_v1`) drives exactly one native wait per `should_wait`; hosted native wait = the condition primitive already used by `std.nogc_async_mut.async_host` (locate: grep `fn wait` there). No `while ... continue`.
- Spec: pending read blocks the caller without spinning (wait count == 1 per completion), returns the completion; `QueueFull` and `InvalidCapability` returned before any wait. Sabotage: swap the wait for a spin loop, wait-count assertion red.
- Verify: `bin/simple test test/01_unit/lib/nogc_async_mut/sosix/fs_sync_spec.spl --no-session-daemon`.

**B4. `time.spl`** `[haiku-ok]` `deps: B2`
- Files: new `src/lib/nogc_async_mut/sosix/time.spl`; spec `test/01_unit/lib/nogc_async_mut/sosix/time_spec.spl`.
- Steps: `sosix_time_monotonic_now() -> u64` = `@always_inline` over `std.nogc_sync_mut.io.time_ops` (sync leaf, no Future); `sosix_time_deadline(deadline_ns) -> Future<Result<SosixCompletion, SosixError>>` = op with `api_id 0x1201` over the same ring/provider. Software provider completes deadlines from a test clock, not wall time.
- Verify: `bin/simple test test/01_unit/lib/nogc_async_mut/sosix/time_spec.spl --no-session-daemon`.

**B5. Hosted file provider (reference provider on this host)** `[haiku-ok]` `deps: B2, B3` — DONE 2026-09-05
- `src/lib/nogc_async_mut/sosix/file_driver.spl`: `SosixHostedFileDriver` implements `SosixSyncWaitDriver`; capability table (slot -> path) and buffer table (slot -> text); `service(fs)` = `fs.take_next()` -> typed alias (`file_read_text_at` / `file_write_text_at`, owner module `std.nogc_async_mut.io`, zero new `rt_*` sites) -> `fs.complete_taken`.
- Not C1/C2: the alias is path-positioned (open + pread/pwrite + close) and reports no errno (`SOSIX_FILE_DRIVER_STATUS_IO = -5` stand-in, `# ponytail:` ceiling named in the file). The exact fd-level leg stays C1–C3.
- Verify: `bin/simple test test/01_unit/lib/nogc_async_mut/sosix/file_driver_spec.spl --no-session-daemon` 3/3 (interpreter and `--mode=native`); sabotage (drop the read bytes) 1/3.

## 4. Stream C — Exact POSIX leg (runtime-owned; blocked until C1)

**C1. `rt_fd_pread` / `rt_fd_pwrite` runtime externs** `[sonnet]` `deps: none` — runtime-owned change, record in lane state first
- Files: `src/runtime/` C owner for fd I/O (locate: `grep -rn 'rt_fd_read_until' src/runtime/*.c`), `src/compiler_rust/common/src/runtime_symbols.rs` (register at `Sys` tier), Simple twin per `doc/07_guide/os/hal/pure_simple_hal.md`, `scripts/check/no_direct_rt_allowlist.txt` (allow only `src/lib/nogc_async_mut/sosix/posix.spl`).
- Steps (as landed 2026-09-05, uncommitted): `rt_fd_pread(fd, buffer_addr, len, offset) -> i64` / `rt_fd_pwrite(...)` return bytes transferred or **`-errno`** — the earlier "-1 + thread errno" wording was wrong for an interpreted caller, which cannot read errno before the interpreter clobbers it; `-errno` is also the io_uring CQE convention the completion status already uses. Rust: `runtime/src/value/sffi/file_io/descriptor.rs` (extern "C"), interpreter wrappers in `compiler/src/interpreter_extern/file_io.rs` (`rt_file_open`/`rt_file_close` were interpreter stubs returning -1/false and now do real work), `insert_simple!` in `interpreter_extern/mod.rs`, `common/src/runtime_symbols.rs`, `security_runtime.rs` ReadFile/WriteFile groups. C twin in `src/runtime/runtime_native.c` next to `rt_file_read_at_fd`. Gates: `cargo check` green on a private target copy, `check-c-runtime-compiles-push.shs` PASS 126, `check-rt-dual-implementation-ratchet.shs` flags 4 pre-existing single-lane symbols from other lanes (`rt_phase_profile_record`, `rt_to_int_dynamic`, `rt_vulkan_*`), not this pair. Typed aliases `file_pread_fd`/`file_pwrite_fd` in the provider module `src/lib/nogc_sync_mut/sffi/fs.spl` (no allowlist edit needed). Seed built privately into `~/dev/.sosix-seed-lane` (never deployed to `bin/release`): specs run on that binary only; **deploying it is the user's decision.**
- Verify: `sh scripts/check/check-c-runtime-compiles-push.shs` PASS; `sh scripts/check/check-runtime-api-regression-push.shs` PASS; `sh scripts/check/check-no-direct-rt.shs` baseline not exceeded (7776).

**C2. `posix.spl`** `[haiku-ok]` `deps: C1 landed and deployed` — written 2026-09-05 (`src/lib/nogc_async_mut/sosix/posix.spl`, `@always_inline` over the sffi aliases, not re-exported from `__init__` until a deployed binary backs the pair); `posix_spec.spl` is red on the deployed 2026-09-04 seed by design
- Files: new `src/lib/nogc_async_mut/sosix/posix.spl`; spec `test/01_unit/lib/nogc_async_mut/sosix/posix_spec.spl`.
- Steps: `sosix_posix_pread/pwrite/read/write/close` as `@always_inline` pass-throughs (or `export use ... as` once A5 is green). No typed result, no capability. Spec: partial read at EOF, zero count returns 0, `pread` does not move the shared offset (read after pread sees the original offset), bad fd returns -1.
- Verify: `bin/simple test test/01_unit/lib/nogc_async_mut/sosix/posix_spec.spl --no-session-daemon`.

**C3. Zero-wrapper disassembly gate** `[sonnet]` `deps: C2` — BLOCKED 2026-09-05: `native-build` on the private seed fails the `std.nogc_sync_mut.sffi.fs` unit with the HEAD version of that file too (probe importing only `file_open`/`file_close`: `2 failed ... ERROR: ..., std.nogc_sync_mut.sffi.fs`; worker stderr truncated, no per-unit diagnostic). Owner: native pipeline lane. Resume: once that unit native-builds, `native-build` a probe calling `sosix_posix_pread` and `objdump -d` for `bl <pread@plt>` with no `sosix_posix_pread`/`file_pread_fd` symbol; sabotage by removing `@always_inline`.
- Files: new `scripts/check/check-sosix-posix-alias-direct.shs` (+ `--selftest`); probe `test/03_system/lib/sosix/probe_posix_alias_native.spl`.
- Steps: native-build the probe, `objdump -d`, require a direct `pread@plt` (or `bl pread`) call from the probe's function with no `sosix_posix_pread` symbol in between; verdict line `PASS — 1 alias(es) checked, 0 wrappers` / `FAIL` / `ERROR — nothing was checked`. Selftest: a fixture WITHOUT `@always_inline` must FAIL.
- Verify: `sh scripts/check/check-sosix-posix-alias-direct.shs` prints PASS; selftest fixture prints FAIL.

**C4. Linux io_uring provider** — BLOCKED. Owner: stream C. Unblock (measured 2026-09-05): the deployed seed does not back `rt_driver_*` (`rt_driver_create(8)` -> 0, `rt_driver_backend_name` -> ""); needs a seed that registers `async_driver_sffi.rs`, then `RingMappingGrade` for native completions agreed with stream A. Resume: `bin/simple test test/01_unit/lib/nogc_async_mut/sosix/fs_async_spec.spl --no-session-daemon` with `SIMPLE_SOSIX_PROVIDER=io_uring`.
**C5. macOS / Windows providers** — BLOCKED. Owner: stream C. Unblock: native host with a deployed pure-Simple binary. Resume: same spec on that host; unavailable hosts stay `blocked`, never `skip`.

## 5. Streams D, E, G — Consumers

**D1. Interpreter/native parity for `fs.read_at`** `[haiku-ok]` `deps: B2, B3`
- Steps: run `fs_async_spec.spl` and `fs_sync_spec.spl` under `--mode=interpreter` and `--mode=native`; record both `Results:` lines and the binary identity brackets. Any divergence is a bug record, not a spec change.
- Verify: `for m in interpreter native; do bin/simple test test/01_unit/lib/nogc_async_mut/sosix/fs_async_spec.spl --no-session-daemon --mode=$m; done`.

**D2. First compiler consumer slice** `[sonnet]` `deps: D1`
- Files: one compiler host-I/O call site that today uses `file_read_text_at` via `std.nogc_sync_mut.io_runtime` (locate: `grep -rn 'file_read_text_at' src/compiler | head`); switch it to `std.nogc_async_mut.sosix.sync` read_at on a capability obtained from the existing facade. Host provider selection must not depend on the compile target (design §2.3 of research pass 2).
- Budget: `bin/simple deps normal <that file>` exclusive growth ≤ 25; `--help` closure does not gain `sosix`.
- Verify: the call site's existing spec green; `sh scripts/check/check-startup-size-performance-audit.shs` unchanged within noise vs H0.

**E1. `screen_host.spl` onto host service IDs** `[sonnet]` `deps: A2`
- Files: `src/lib/common/ui/screen_host.spl` (46 lines), `src/os/sosix/host/service_contract.spl`, existing screen_host spec (locate: `find test -name '*screen_host*'`).
- Steps: present/readback/input-next/timer-deadline calls carry `0x1001/0x1002/0x1101/0x1201` from `service_ids_v1`; no renderer type crosses the boundary. Wire, do not redesign.
- Verify: existing screen_host spec green; `bin/simple test test/01_unit/os/sosix/host_service_contract_spec.spl --no-session-daemon` green.

**E2. DrawIR submit/drain split** `[sonnet]` `deps: E1`
- Files: `src/lib/nogc_async_mut/gpu/engine2d/draw_ir_runtime_queue.spl:101-131`.
- Steps: return the submit receipt without draining; drain/dispatch becomes a separate call observed by the caller; SDN text payload stays for evidence only, not the production path. Rendering-lane change; no SOSIX contract edit.
- Verify: the engine2d runtime-queue spec (locate: `grep -rln draw_ir_runtime_queue test/`) green plus one new example proving a submit with no drain leaves `submitted_count == 1, completed_count == 0`.

**G1. Remove the dead divergent copy in `io.spl`** `[sonnet]` `deps: A1`
- Files: `src/os/sosix/io.spl:83-293` (divergent copy of `io_rw.spl`'s function set: 219-line diff, no `fd_type == 6` branch, no `export` lines).
- Steps: confirm zero importers (`/usr/bin/grep -rn 'os.sosix.io\.' src test --include=*.spl` must be empty — pair with a control grep for `os.sosix.io_rw` that MUST hit); `diff <(sed -n 83,293p src/os/sosix/io.spl) <(sed -n 21,236p src/os/sosix/io_rw.spl)` and read it: any behavior `io.spl` has that `io_rw.spl` lacks (a real serial emit, a different error code, a zero-length rule) is recorded in the task report and handed to G2's scope before deletion. Then delete the copy (keep any non-duplicate content in `io.spl`). If an importer appears, stop and record.
- Verify: `bin/simple deps fast src/os/kernel/async_io_rw.spl` clean; `bin/simple test test/01_unit/os/sosix/io_spec.spl --no-session-daemon` green.

**G2. `io_rw.spl` onto `wait_v1` + v1 positioned stack** `[sonnet]` `deps: G1, A3`
- Files: `src/os/sosix/io_rw.spl`, `src/os/kernel/async_io_rw.spl`; extend `test/01_unit/os/sosix/` io spec; QEMU system spec under `test/03_system/os/qemu/`.
- Steps: replace the 128-slot table and `while not complete: continue` with `SosixOperationSlot` + `SosixSyncWaitAdapter` over the kernel wait; route VFS reads through the positioned stack (`positioned_syscall_provider_v1`); serial write (`fd_type == 6`) must emit bytes to the UART (use the existing serial owner, locate: `grep -rn 'fn serial_write' src/os`) and return the emitted count; slot exhaustion returns `QueueFull` (`-11`, EAGAIN) not `-9`. Write the serial-write spec first; it must fail on the current fabricated `count`.
- Budget: idle-loop iterations while a read is pending == 0 (QEMU counter); no allocation in the completion path.
- Verify, two levels. Unit (this host, closes AC-3a): `bin/simple test test/01_unit/os/sosix/io_spec.spl --no-session-daemon` green with the new examples (no spin, `-11` on exhaustion, serial branch calls the UART owner — assert the call, not the bytes). QEMU (AC-3b): `sh scripts/check/check-sosix-qemu-matrix.shs` serial row PASS with observed bytes in the retained serial log, published only through `scripts/check/check-produce-sosix-qemu-native-pass-bundle.shs` and imported through `scripts/check/check-collect-sosix-qemu-evidence.shs`; row ownership and resume commands in `doc/03_plan/sys_test/sosix_qemu_matrix_evidence_status_2026-08-13.md`. This level needs a pure-Simple compiler accepted by `simple_binary_is_valid`; `bin/simple` is the seed here, so AC-3b is BLOCKED until a pure-Simple deploy, owner stream G, and stays out of exclusions.

**G3. Retire `io_rw.spl`** `[haiku-ok]` `deps: G2 unit level green; G2 QEMU level (AC-3b) green or explicitly BLOCKED with the deploy named`
- Steps: point `async_io_rw.spl` at the v1 stack directly; delete `io_rw.spl`; record removal in the lane.
- Verify: G2's specs still green; `bin/simple deps fast src/os/kernel/async_io_rw.spl` clean.

**G4. SimpleOS device-initiated queues (GQ-001..012)** — BLOCKED. Owner: SimpleOS driver lane. Unblock: GQ-001 native capability report on real hardware. Resume: per `simple_os_gpu_queue_feature_requests_2026-09-05.md` first demonstration.

## 6. Streams F and H — GPU (blocked) and verification/perf

**F1. G1 proxy storage slice** — BLOCKED. Owner: GPU lane. Unblock: B2 + C1 green and a host with a deployed pure-Simple binary and a real GPU (CUDA or Vulkan). Resume: `doc/03_plan/agent_tasks/gpu_remote_interpreter_parallel_plan_2026-08-07.md` lanes B/C for the transport, request/result schema from `sosix_gpu_api_extension_final_report.md` §8.

**H0. Baseline B0** `[haiku-ok]` `deps: none` — runs FIRST
- Files: new `doc/10_metrics/runtime/sosix_unification_baseline_2026-09-05.md`.
- Steps: record binary identity; `sh scripts/check/check-startup-size-performance-audit.shs`; `bin/simple deps normal src/lib/nogc_async_mut/sosix/host_facade.spl`; `sh scripts/check/check-no-direct-rt.shs` verdict (expect 7776); wall p50/p95 of 10k `file_read_text_at` 4 KiB reads via `bin/simple run` on a fixed fixture file (interpreter) — this is the pre-change reference for D2. Exact commands in the doc.
- Verify: the metrics file exists with every command, its output, and both identity brackets.

**H1. Ratchet and closure gates** `[sonnet]` `deps: A1`
- Files: new `scripts/check/check-sosix-capsule-boundaries.shs` (+ `--selftest`).
- Steps: fail if `src/lib/common/contracts/sosix/**` imports `os.` or declares `extern fn rt_`; fail if `src/lib/nogc_async_mut/sosix/**` imports `os.`; fail if `src/os/**` imports `std.nogc_async_mut.sosix`; fail if any new `.spl` under the two capsules exceeds 300 lines; fail if `check-no-direct-rt.shs` forbidden count rises above 7776. Verdict line convention (`PASS — n file(s) checked` / `FAIL` / `ERROR — nothing was checked`), selftest with a violating fixture. Add a `push`-tier row in `config/check/must_check_gates.sdn` with an exact-match dispatch case in `check-push-must-pass.shs` (a manifest row alone is not wiring, vcs.md).
- Verify: `sh scripts/check/check-sosix-capsule-boundaries.shs` PASS; `--selftest` shows the fixture FAIL.

**H2. Perf report** `[sonnet]` `deps: B3, C3 (or C3 BLOCKED noted), G3`
- Files: `doc/10_metrics/runtime/sosix_unification_<date>.md`.
- Steps: same binary, same tree: p50/p95 of 10k 4 KiB reads for direct `file_read_text_at`, `sosix_sync_fs_read_at` (software provider), `await sosix_fs_read_at`, and `sosix_posix_pread` if C2 landed; `SoftwareProviderCounters` per op; allocation counts; startup audit vs H0; QEMU idle-spin counter from G2. State which rows are seed-attributed. No speedup claims; budgets from design §7 pass/fail per row.
- Verify: report cites H0, both identity brackets per measurement, and every design §7 row with PASS/FAIL/BLOCKED.

## 7. Cooperative review and landing

- Stream A owns every name in `src/lib/common/contracts/sosix/`; B/C/D/E/G build against A1's exports and open a request to A for any new symbol. A5 and C1 are separate lanes (compiler, runtime) and may land at any time; nothing else edits `src/compiler_rust` or `src/runtime`.
- One worktree per stream on `/mnt/data`, `build` symlinked to the main tree's `build` before the first build (spipe skill worktree trap). Commit pure moves (A1, B1 shims, G1) separately from behavior changes.
- Every task report: files, verify output, budget receipt, identity brackets, sabotage result (green→red→green), and any bug record filed.
- Final reviewer (normal/highest-capability, not the author) accepts done marks, BLOCKED rows, and generated-manual quality (`bin/simple spipe-docgen <spec> --output doc/06_spec --no-index`, `0 stubs`).
