# BuildRunner worker cannot run on macOS: process observation V4 is Linux-only
## Resolved for the positional route 2026-10-31

- Severity: blocks every BuildRunner task on macOS, including the Phase 2 BuildRunner Hello
  (`--memory-policy monitor`).
- Measured 2026-10-31 with stage2 sha256 `adef5db249e4…` (Phase 3 rev8), runs `mon-1..4`: the
  worker (`src/app/bootstrap_builder/worker.spl`) refused before starting the compiler with
  `exact process observation V4 unavailable`, wrote `compiler.not-started.sdn`
  (`SIMPLE-NO-CHILD-STARTED-1`), and the manager exited 2. Same refusal as 2026-10-29.

## Root cause
`runtime_process_owned.c` compiled its POSIX owner only under `__unix__`, which clang does not
define on macOS, so every owned-process family on Darwin was an ENOTSUP stub. The executable
pin (`rt_process_pin_executable_owned*`) was Linux-only (sealed memfd + `fexecve`), and the Rust
seed lane stubbed it to -1.

Also found: the worker's monitor request uses `descendant_policy: ProcessGroup` and requires
`tree_empty`, but Linux V4 rejects every non-LeaderOnly policy and never sets `tree_empty`. The
worker's V4 path was therefore dead on Linux too; Darwin is the first provider that satisfies it.

## Fix (owner-approved partial Darwin V4, 2026-10-31)
C only, in `runtime_process_owned.c` (Darwin arms gated by `RT_OWNED_DARWIN_V4`):
- **Capability mask** (`POV4_DARWIN_CAPABILITIES`): PINNED_CWD, EXACT_ENV, ABSOLUTE_DEADLINE,
  WAIT4, TWO_PHASE_COLLECT, LEADER_ONLY, plus new `DARWIN_SNAPSHOT_EXEC` (1<<9),
  `DARWIN_SPAWN_EXEC_PROOF` (1<<10), `PROCESS_GROUP_RETIRE` (1<<11). PINNED_EXEC, PTRACE_EXEC
  and RLIMIT_AS are clear. Any memory limit or enforcement is refused (`REASON_MEMORY`,
  ENOTSUP); monitor policy (no enforcement, zero limit) is admitted.
- **Executable pin**: a private snapshot (mkdtemp 0700 directory, 0500 single-link file owned by
  the euid), launched by pathname. Every acquisition re-validates dev/ino, mode, link count and
  owner of file and directory. Weaker than the sealed memfd: same-UID processes are trusted.
  Lives in `runtime_process_owned.c` so the seed runtime links it; the Rust stubs are
  `cfg(not(target_os = "macos"))`.
- **Exec proof**: `posix_spawn` with `POSIX_SPAWN_START_SUSPENDED | CLOEXEC_DEFAULT | SETPGROUP`;
  before the child runs an instruction, its lowest file-backed mapping
  (`PROC_PIDREGIONPATHINFO`) must be the snapshot dev/ino and the snapshot bytes must still match
  the bound digest; only then `SIGCONT`. Owner-accepted 2026-10-31 as the Darwin exec proof,
  with its own capability bit (`DARWIN_SPAWN_EXEC_PROOF`); kqueue `NOTE_EXEC` cannot observe a
  `posix_spawn` exec because the pid exists only after it.
- **ProcessGroup retirement**: the exited leader stays unreaped (it pins the group id); every
  live non-zombie member is sent SIGKILL until a zero-live `KERN_PROC_PGRP` sample, then the
  leader is reaped and the packet reports `tree_control_available`, `tree_empty` and
  `tree_empty_ns == leader_waited_ns`. Members that leave the group (setsid/setpgid) are not
  contained — the same limit as Linux process-group cleanup. If members survive to the cleanup
  deadline (unsignalable, or joined the group), the leader is reaped anyway with
  `runtime_error = ETIMEDOUT` and `tree_empty` is never claimed.
- **RSS**: only `wait4` direct-child peak RSS (`VALID_DIRECT_RSS`); no tree metric is published.
- Inspection V1 (atomic stdin) stays ENOTSUP on Darwin; it is outside the approved scope.
- Every other owned-process family (V2, V3, bounded run) keeps its exact ENOTSUP answer on
  Darwin. FreeBSD, Windows and SimpleOS keep their refusal.
- Rewriting a snapshot that already executed invalidates the vnode's code-signing state and the
  next exec is SIGKILLed (observed in the live selfcheck): denial on tamper, not a seal.

- A launched child keeps its snapshot alive: closing the pin right after start (as the worker
  does) retires only the handle; the files are removed when the last child's lease is collected.
  Unlinking earlier got the child SIGKILLed at launch — amfid evaluates the ad-hoc image after
  exec (`exit reason namespace EXEC, code SECURITY_POLICY`; amfid: "adhoc signed" not valid).
- Seed interpreter (`interpreter_extern/process_observation_v4.rs`, macOS only): marshals the V4
  and pin externs to the C owner (integer arrays rebuilt as plain runtime ints; results freed).
  JIT text ABI: `rt_process_observation_v4_pin_cwd_value` now expands to (ptr, len) like the
  pure-Simple table already did; it was refused for every path under JIT on every host.
- The V4 ABI caps wall budget at 3600 s; the hello BuildRunner task requests
  `timeout_seconds * 8 + 30` (7230 s at the 900 s default), which V4 rejects (EINVAL,
  InvalidSchema) on every host. The hello runs use `--timeout-seconds 440` (3550 s).

Worker (`src/app/bootstrap_builder/worker.spl`): admission now requires the specific bits of the
monitor ProcessGroup request (`process_observation_monitor_group_gap_v4`), not just `available`.

## Evidence
- `sh scripts/check/check-sosix-v4-darwin-foundation.shs` (macOS, `-Werror`): darwin, interrupted
  wait, live (LeaderOnly, ProcessGroup with a surviving grandchild, deadline TERM/KILL, memory
  refusal, startup-cleanup authority, tamper refusal, descriptor hygiene over 18 leases) and real
  pin selfchecks PASS; live selfcheck also PASS under ASan+UBSan.
- Linux (alpine clang 17 container): `runtime_process_observation_v4_selfcheck` PASS before and
  after; zero new warnings in `runtime_process_owned.c` / `runtime_process.c`.

- Known limit: a lease that is never collected keeps a retired snapshot's files until the
  process exits (the worker always collects).

## Hello BuildRunner status after this change (2026-10-31, seed rebuilt from this change)
The compiler task now starts under Darwin V4: the snapshot pin, cwd pin, suspended-spawn exec
proof, group retirement, reap and `compiler.process` / `compiler.memory` evidence all work. The
lane still does not reach FUNCTIONAL, for reasons outside the V4 owner:
1. FIXED: the task budget `timeout_seconds * 8 + 30` exceeded the V4 wall cap (3600 s) at the
   default 900 s. `hello-sanity-buildrunner.py` now clamps the task total to 3600 s
   (`task_budget_seconds`), and the worker refuses an over-cap task before start with an exact
   reason instead of the opaque InvalidSchema rejection.
2. The producer (`hello-sanity-buildrunner-worker.py`) runs a nested hello lane whose watchdog
   uses `--session-mode=new`; the manager's outer watchdog reports
   `exit_status=90 unexpected_session_pids=...` (bootstrap-session-escaped). FIXED: the contract
   (`SIMPLE_BOOTSTRAP_SESSION_ID/EXEC`) does reach the producer; `hello-sanity-matrix.py` dropped
   it in its `SIMPLE_*` sanitization. It now keeps exactly those two keys (validated) and a lane
   holding them runs its watchdog with `--session-mode=inherit` and no new session
   (`nested_session`). Owner decision 2026-10-31: join the outer session.
3. This lane was never runnable on Linux either (leader-only V4 rejects ProcessGroup).
4. FIXED: the isolated attempt had no `src/runtime`, but the compiler builds core C runtime objects
   from it. The lane now stages it plus `RUNTIME_EXTERNAL_HEADERS`.

## Verified 2026-10-31
Four sequential monitor runs, stage2 `adef5db2…`: `buildrunner_status: "FUNCTIONAL"`, stdout
`Hello, World!\n`. Run conditions: `--compile-route positional`, and a local uncommitted matrix
edit keeping `SIMPLE_LLVM_BIN`, because that stage2 predates the llc PATH fix.

## Open
- The default `coordinator` route still fails in the attempt:
  `SCV-E-ADMISSION: git-event-source-unavailable` (no git repository in the staged tree).
