# lane-boot-s6 — evidence log (2026-08-25)

Worktree: /mnt/data/worktrees/lane-boot-s6
HEAD: 684fadabcae (origin/main at fetch time), `git status --porcelain` = 0 before and after.
Isolation verified twice; HEAD did not move. No Stage 2 was started (coordinator hold).

## 1. Seed cargo build died without a verdict — UNEXPLAINED

Launched setsid-detached at ~03:41:
  sh -c 'cd src/compiler_rust && cargo build --release --bin simple > evidence/seed_build.log 2>&1; echo "SEED_RC=$?" >> ...'

Outcome: NO `SEED_RC` line was ever written, no `target/release/simple` binary,
0 cargo/rustc processes. The wrapper's unconditional `echo SEED_RC` never ran,
so the wrapping `sh` itself died — this is an external kill, not a cargo failure.
Last observed alive 04:29 (rustc compiling `simple_compiler_backfill`);
found dead by 04:31. target/ 810M, log frozen at 03:46 (cargo block-buffers to a
non-tty, so a static log is NOT evidence of a stall).

### Candidate mechanisms, none proven

(a) **Harness task cleanup — strongest correlation, UNPROVEN.**
    Three `TaskStop` calls on my polling watchers landed at ~04:30, inside the
    2-minute window in which the build died. If the harness reaps by process
    tree or cgroup rather than by session, `setsid` would not protect a child.
    Correlation only; no kill site observed.

(b) **earlyoom — plausible mechanism, NOT a proven cause.**
    Host runs: earlyoom -r 3600 --prefer ^(simple|rustc|cc1|cc1plus|lto1|collect2|qemu-system|ld)
    --avoid ^(claude|codex|gemini|node|sshd|dockerd|containerd|...)
    It preferentially SIGTERMs exactly the binaries a bootstrap runs and spares
    agent processes. BUT it fires on MEMORY pressure and free RAM measured
    104-110 GB throughout, including at load 133 (110 GB free at 04:31). So it
    fits only if a transient spike occurred. `journalctl -u earlyoom` returns
    nothing on this host and `dmesg` shows 0 OOM/"Killed process" lines, so
    neither confirmation nor refutation is available. Record as open.

(c) **scripts/check/reap-orphan-resource-hogs.shs — LARGELY REFUTED, do not cite.**
    Superficially it fits (a setsid'd build is ppid=1 by construction, which is
    the reaper's own criterion, and cargo/rustc are absent from its PROTECTED
    list). Two facts refute it as the cause here:
      - it reaps with `kill -9` (rc 137), which CANNOT produce the RC=143 seen
        in the earlier incident; and
      - line ~147: only a FLEET (>50 orphaned siblings sharing one comm) is
        reapable. A single high-CPU/high-RSS ppid=1 process is REPORTED, never
        killed.
    No reaper instance was running at the time of death.
    Worth noting anyway as a live tension: the brief mandates setsid-detachment
    to survive SIGTERM, and setsid is exactly what makes a process ppid=1 and
    thus a reaper candidate. If the reaper's fleet threshold ever loosens, every
    correctly-detached bootstrap becomes reapable.

### Consequence for the next run
A long bootstrap here has now been observed to die silently twice with no
in-script kill site (this build; the earlier Stage 2 RC=143). Before burning
hours on the full Stage 4 run, the wrapper should record its own PID and have an
independent, non-`setsid`, low-cost observer log liveness, so the next death is
attributable rather than another open question.

## 2. Attribution harness built and PROVEN (evidence/run-attributable.sh)

Approved after two silent deaths. Usage:
    sh evidence/run-attributable.sh <tag> <command...>

Records next to the command log: `<tag>.meta` (cmd_pid/pgid/sid/start — so an
outside observer can NAME the process), `<tag>.beat` (heartbeat every 30s with
load/free-RAM/RSS/child-count, independent of the command writing anything —
cargo block-buffers to a non-tty, so a static command log is NOT evidence of a
stall), and `<tag>.rc` (the ONLY authoritative verdict).

Reading the outcome:
  RC=<n>            real exit status. RC=124 is a TIMEOUT, not a pass, not a crash.
  SIGNAL=TERM/...   a CATCHABLE external kill, named by signal
  neither line      SIGKILL, or the process group was reaped. The last .beat
                    sample brackets time of death to 30s.

Selftested against three real fixtures before use (a harness never exercised is
not insurance):
  clean exit 7          -> `RC=7`                      OK
  SIGTERM to wrapper    -> `SIGNAL=TERM at 04:33:00`   OK (this is the 143 shape)
  SIGKILL to wrapper    -> no verdict line at all      OK (correct by design;
                           SIGKILL is uncatchable, so its signature is ABSENCE)
Selftest found and fixed one real defect: `ps -o sid=` returned empty on this
host; now read from field 6 of /proc/<pid>/stat (verified sid=868584).

## 3. TaskStop by the coordinator is a live hazard to detached builds

Agreed protocol: the coordinator will NOT call TaskStop on any watcher while a
build of mine is running. If a future build dies with no verdict, the first
question is what the harness was doing at that moment — `setsid` may not be
sufficient isolation if the harness reaps by process tree or cgroup, and that
boundary is invisible from inside. Cause of the 04:31 death remains OPEN.
