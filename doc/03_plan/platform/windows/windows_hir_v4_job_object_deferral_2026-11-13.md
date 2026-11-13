# Windows HIR V4 Job Object owner: deferral and resume plan (2026-11-13)

- **Status:** deferred by the user on 2026-11-13. On Windows, only the per-file
  worker pool is supported for now.
- **Owner:** unassigned (deferred by user 2026-11-13)
- **Base read:** `origin/release/1.0.0` at `ded2f387961`. Line numbers refer to that tree.
- **Source:** the platform-port Windows lane, `work/plat-windows-20261113`. That lane
  also produced include fix `d15142f7a02`, which is landing separately.

## 1. Gap (P0, deferred)

HIR shard workers cannot start on Windows.

- `run_ledger_shards` (`src/app/cli/native_build_main.spl:1143`) starts every
  `hir-shard` worker through `worker_hir_owner_start_v1`
  (`src/app/cli/worker_hir_owner_v1.spl:201`, call site `native_build_main.spl:1261`).
- That function asks `process_observation_capabilities_v4()`. On every
  non-POSIX host, the C provider is the stub at
  `src/runtime/runtime_process_owned.c:7020` (`pov4_unavailable_tuple`).
  Its capabilities at `:7051` return
  `{version 4, 8 fields, available 0, bits 0, ..., ENOTSUP}`.
- The seed interpreter's V4 adapter is
  `#![cfg(target_os = "macos")]` only
  (`src/compiler_rust/compiler/src/interpreter_extern/process_observation_v4.rs:9`).
- The owner records `"HIR worker process observation unavailable: <gap>"`
  (`worker_hir_owner_v1.spl:219`) and holds no reservation.
  `tick_observed_v1` then waits out the cleanup deadline and ends with
  `done=true stopped=false`. Every HIR slot fails, so the two-pass HIR warm-up
  cannot run on Windows.

The per-file pool (`run_file_worker_pool_v1`, label `file-worker`) does not use
V4. It spawns through `process_spawn_async`, so it is the supported Windows route
until this plan resumes. Its own containment gap is in section 5.

## 2. Existing pure-Simple Job Object owner (reuse it)

`src/lib/nogc_sync_mut/io/windows_process_owner.spl` already implements the
Windows mechanics end to end. It is not wired into the V4 facade:

- Process creation:
  - suspended `CreateProcessW`;
  - exact Unicode environment;
  - `PROC_THREAD_ATTRIBUTE_HANDLE_LIST` allowlist;
  - executable and cwd pins (`_windows_process_pin_v1`,
    `windows_process_directory_no_follow_v1`).
- Job setup:
  - `CreateJobObjectW` + `SetInformationJobObject(JobObjectExtendedLimitInformation)`;
  - `LimitFlags = 8192` (`JOB_OBJECT_LIMIT_KILL_ON_JOB_CLOSE`), or
    `8704` (`| JOB_OBJECT_LIMIT_JOB_MEMORY`) with `JobMemoryLimit` at offset 120;
  - the limits are read back and checked (`:404-419`);
  - `AssignProcessToJobObject` runs **before** `ResumeThread`.
- Lifecycle:
  - deadline action: `TerminateJobObject(124)`;
  - cancel: `TerminateJobObject(125)`.
- Empty-tree proof: `_windows_process_empty_v1` (`:265`) polls
  `QueryInformationJobObject(JobObjectBasicAccountingInformation)` until
  `ActiveProcesses` (accounting + 40) reaches 0.
- Peak memory: `windows_process_peak_memory_v1`.
- Token wrapper: `src/lib/nogc_sync_mut/io/windows_redirected_process.spl`
  (`windows_redirected_spawn_with_memory`, `windows_redirected_kill`).

The C runtime has a parallel job-owned sync owner in
`runtime_process_owned.c` (`RT_OWNED_WIN32_SYNC_IMPLEMENTED` block). It can be
the C half of the dual implementation.

## 3. Design to resume with

### 3.1 Capability bits

`process_observation_monitor_group_gap_v4`
(`src/lib/common/process/observation_v4.spl:119`) requires POSIX-named bits.
The Windows mapping:

| V4 bit | Windows primitive |
|---|---|
| `PINNED_EXEC` (1) | exe handle opened without `FILE_SHARE_WRITE`/`FILE_SHARE_DELETE`, plus digest |
| `PINNED_CWD` (2) | no-follow directory handle |
| `PTRACE_EXEC` (4) / `DARWIN_SPAWN_EXEC_PROOF` (1024) | **new bit `WIN32_SUSPENDED_EXEC_PROOF`**: synchronous `CreateProcessW(CREATE_SUSPENDED)`, then assign to the job, then resume |
| `EXACT_ENV` (8) | `CREATE_UNICODE_ENVIRONMENT` block |
| `ABSOLUTE_DEADLINE` (16) | `GetTickCount64` deadline + `TerminateJobObject` |
| `WAIT4` (32) | `WaitForSingleObject(leader)` + `GetExitCodeProcess` + job accounting |
| `TWO_PHASE_COLLECT` (128) | leader and job handles retained until ack |
| `PROCESS_GROUP_RETIRE` (2048) | **new bit `JOB_OBJECT_RETIRE`**: a Job Object with `KILL_ON_JOB_CLOSE` |

The gap function must accept `JOB_OBJECT_RETIRE` in place of
`PROCESS_GROUP_RETIRE`, and `WIN32_SUSPENDED_EXEC_PROOF` in place of
`PTRACE_EXEC`/`DARWIN_SPAWN_EXEC_PROOF`. Keep that change pure, and spec it on
Linux by injecting bit sets.

### 3.2 Retirement receipt mapping

- `tree_empty` = (`JOBOBJECT_BASIC_ACCOUNTING_INFORMATION.ActiveProcesses == 0`)
- `leader_reaped` = (leader handle signalled) AND (`GetExitCodeProcess` != `STILL_ACTIVE` (259))
- `signal_number` = 0, and `exit_code` = the leader's exit code.

`KILL_ON_JOB_CLOSE` guarantees that closing the last job handle kills every
descendant. The receipt is only issued after `ActiveProcesses == 0` is observed.
A closed handle alone never counts as proof.

Factor this as a pure function so it is testable off-Windows:
`windows_job_retire_receipt_v1(active_processes, leader_signalled, exit_code)`.

### 3.3 Implementation lanes (dual implementation)

1. **C:** add a Windows arm for
   `rt_process_observation_v4_{capabilities,start_pinned,poll,cancel,collect,ack_collect}_value`
   in `runtime_process_owned.c`, replacing the stub for `_WIN32`.
2. **Seed:** widen `process_observation_v4.rs` to `cfg(windows)`.
3. **Pure-Simple twin:** the `windows_process_owner.spl` functions above.

## 4. Job Object memory limit decode (cgroup analogue; also deferred)

`shard_cgroup_memory_max_kb()` returns a constant `0` on Windows
(`src/app/cli/shard_mem_clamp.spl:644`). An enclosing job's memory limit is
therefore invisible. `GlobalMemoryStatusEx` does not reflect job limits outside
silos, so this is the same out-of-memory class that the Linux cgroup probe fixed.

### 4.1 Probe

1. `IsProcessInJob(GetCurrentProcess(), NULL, &in)`.
2. `QueryInformationJobObject(NULL, JobObjectExtendedLimitInformation /*9*/, buf, 144)`.

This needs an rt_ wrapper with C and seed lanes: a raw kernel32 extern is a hard
abort under the seed interpreter.

### 4.2 Pure decode

Signature: `(in_job, limit_flags: u32 @16, process_limit: u64 @112, job_limit: u64 @120) -> tree cap kB`

- **Tree cap:** `job_limit / 1024`, used only when `limit_flags & 0x200`
  (`JOB_OBJECT_LIMIT_JOB_MEMORY`).
- **Per-process bound:** `0x100` (`JOB_OBJECT_LIMIT_PROCESS_MEMORY`) bounds the
  per-worker estimate only. It is never the tree cap.
- **Unknown (0, never treated as a limit of 0):**
  - the process is not in a job;
  - the relevant flag is clear;
  - the limit is 0;
  - the value is above `INT64_MAX`.
- **Nested jobs:** a NULL handle reports only the **immediate** job, and the
  outer chain cannot be walked from inside. Document this; never guess.

### 4.3 Related decode rules

These belong to the FreeBSD lane, which owns the shard_mem_clamp parsers:

- **Headroom:** `min(ullAvailPhys @16, ullAvailPageFile @32) / 1024`.
- **Installed RAM:** `ullTotalPhys @8` / 1024.
- **PowerShell `TotalVisibleMemorySize`:** already in kB. Do not divide by 1024
  again. Trim CRLF; a non-digit means unknown.

## 5. P1 (not deferred by name, still open): file-worker and MIR children are not in a job

`process_spawn_async` resolves to `rt_process_spawn_async_owned_windows`
(`src/runtime/runtime_process.c:4041`):

- a plain `CreateProcessW`;
- no Job Object, and the process is not created suspended.

`rt_process_kill` (`runtime_process.c:136`) is
`OpenProcess(pid)` + `TerminateProcess` on the leader only. That leaves two holes:

- a PID-reuse window;
- surviving grandchildren such as clang, lld and nested `simple`.

There is no tree-empty receipt. This is the per-file pool that Windows keeps,
so this gap is live.

**Fix shape:** create suspended, use a `KILL_ON_JOB_CLOSE` job, and assign before
resume. Kill with `TerminateJobObject`; retire on `ActiveProcesses == 0`.
Alternatively, route the pool through `windows_redirected_spawn_with_memory`
behind `@when(os="windows")`.

## 6. Prerequisites

1. **A real Windows x86_64 host** (aarch64 Windows for the ARM64 rows) with
   llvm-mingw UCRT and MSYS2. None is provisioned, and Wine is not evidence.
2. **The V4 receipt schema settled.** The retirement-receipt fix
   (`work/r26-hir-retire-receipt-20261113`, the `tree_empty=false` bug) must land
   first. Adding new capability bits to the frozen V4 schema is a schema
   decision for the owner of `src/lib/common/process/observation_v4.spl`.
3. **The dual-implementation ratchet** (`scripts/check/rt_dual_implementation_baseline.txt`):
   new rt_ symbols need both the C and the seed lane.

## 7. Resume commands

Off-Windows static checks (runnable on Linux):

```sh
sh scripts/setup/bootstrap-prereqs.shs install-llvm-mingw      # pinned 20260922, checksummed
M=~/.simple/toolchains/llvm-mingw-20260922-ucrt-x86_64
for t in x86_64-w64-mingw32 aarch64-w64-mingw32; do
  clang --target=$t --sysroot=$M -fsyntax-only -Isrc/runtime -Isrc/runtime/platform \
    src/runtime/runtime_process_owned.c src/runtime/runtime_process.c src/runtime/runtime_memory_headroom.c
done
SIMPLE_COVERAGE=1 SIMPLE_COVERAGE_OUTPUT=cov.sdn bin/simple run test/01_unit/app/cli/shard_mem_clamp_spec.spl
```

Native rows (a Windows host, PowerShell, repo root):

```powershell
powershell -NoProfile -File scripts/check/check-owned-process-windows-adapter.ps1
powershell -NoProfile -File scripts/check/check-owned-process-windows-async.ps1
powershell -NoProfile -File scripts/check/check-bootstrap-stage3-windows-process-inventory.ps1   # -WorkerLabel sleeper = retirement fixture
python scripts/check/check-windows-host-capacity.py
bin/simple run test/01_unit/app/bootstrap_builder/windows_capacity_headroom_spec.spl
```

End-to-end acceptance, once implemented:

- `SIMPLE_HIR_SHARDING=1 bin/simple native-build ...` on Windows reports
  `peak_live_workers >= 2`.
- Every HIR retirement receipt shows `tree_empty=true leader_reaped=true`.
- A killed worker leaves no surviving descendant. Check this with the
  stage3 process-inventory script.
