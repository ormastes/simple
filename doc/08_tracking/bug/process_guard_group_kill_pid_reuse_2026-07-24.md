# `simple-guard` post-reap group-kill murders unrelated process groups under PID reuse

- **Date:** 2026-07-24
- **Severity:** critical (repeatedly killed unrelated long-running builds
  machine-wide; four consecutive bootstrap stage-4 builds SIGTERM'd)
- **Status:** root fix in Rust source (sentinel PGID pin); interim binary patch
  applied to all deployed/seed binaries on this host

## Symptom

Long-running processes (observed: bootstrap stage-4 `native-build`, ~5–10 min
in) die from an externally delivered SIGTERM with no earlyoom log, no OOM, no
harness timeout, plenty of free RAM, and the parent shell surviving. Four
consecutive isolated-bootstrap stage-4 runs died this way at varying elapsed
times (533 s, 590 s, ~300 s, ~530 s) — a name-based `pkill` shield (running the
compiler under a scratch binary name) did NOT help.

## Forensics

A 4 Hz process sampler (`killcatcher`) caught the killer class in the act: the
`simple-guard` wrapper that `process_run_bounded` emits around every bounded
subprocess (spec runs, tool invocations):

```sh
child=; stop(){ [ -z "$child" ] || { kill -TERM -- "-$child" ...; kill -KILL -- "-$child" ...; }; }
...
setsid "$@" & child=$!; wait "$child"; code=$?; stop; ...
```

Wrappers with this text were live seconds before each death, spawned by
parallel sessions' test runners (e.g. `timeout 300s .../simple run ...
<spec>.spl` from other worktrees).

## Mechanism

1. `setsid "$@" &` makes the child a fresh process-group leader
   (PGID == child PID).
2. `wait "$child"` **reaps** the child → its PID number becomes allocatable
   again (a PID is only pinned while it is in use; after the group's last
   member is gone and the leader is reaped, the number is free).
3. `stop()` then fires `kill -TERM -- "-$child"` — addressing the PGID **by
   number** after the number may already have been recycled.
4. This host's PID counter wrapped this morning (heavy churn incl. a fork
   bomb); PID allocation is sequential, so a *new* process-group leader (the
   stage-4 compiler chain) is allocated exactly the recently-freed numbers
   that guards then group-kill. Every bounded-process completion fires two
   such kills; spec-running sessions produce thousands per hour, which made
   the collision effectively deterministic for any long-running build.

## Interim mitigation (applied on this host, 2026-07-24)

Same-length binary patch of the guard string in every deployed binary, seed,
and static lib across all live worktrees (~75 files): group-kill
`"-$child"` → bare-PID kill `"$child" `. A post-reap bare-PID kill is almost
always ESRCH; worst case it hits one recycled process instead of a whole
group. Alive-child (timeout) kills still work. Orphan-group sweeping is
temporarily lost until rebuilt binaries ship.

## Root fix (in source)

`src/compiler_rust/runtime/src/value/sffi/env_process.rs` and
`compiler/src/interpreter_extern/system.rs`: pin the PGID with an unreaped
sentinel member so the kernel cannot recycle the group id while it is still
addressable:

```sh
setsid /bin/sh -c 'sleep 3600 & exec "$@"' simple-guard-grp "$@" &
```

The `sleep` lives in the new group; after the real command exits and is
reaped, the group still exists (sleeper alive), so the PGID number cannot be
reallocated — `stop()`'s group-kill then targets only the true group (and
reaps the sleeper as part of cleanup). The 3600 s cap bounds sentinel leakage
if a guard is SIGKILL'd.

## Follow-ups

- Rebuild + redeploy binaries so the source fix replaces the binary patch.
- The same post-reap-kill-by-number idiom should be audited anywhere else it
  appears (`kill -- "-$pid"` after `wait`).
