# Stage 3 transaction supervisor v2 handoff

Status: **HOLD / verified first component only**. Nothing in this directory has
been applied to the authoritative lane, and no real systemd service, Stage 3
compiler, private Rust build, Git operation, or heavy build was started.

## Tested first component (independent review HOLD)

`scripts/check/lib/bootstrap-stage3-unit-supervisor.pl` is the isolated unit
supervision primitive for the later outer transaction coordinator. It owns one
direct `O_CLOEXEC` heavy flock and has no output flock. Only after the lock is
held does it recover a stable owner/cgroup journal, reject quarantine, create
evidence, snapshot executable roles, and start a deterministic systemd service.

The service is blocked behind a one-byte pre-exec gate until the parent has
opened and retained the cgroup directory plus required controller files,
verified the exact memory/swap/OOM-group policy, recorded zero event baselines,
and durably published its cgroup journal and launch plan. The service is run
under `env -i`; loader/interpreter injection variables are rejected. Executable
roles are copied to a private evidence directory, opened, retained, and invoked
through `/proc/<supervisor-pid>/fd/<n>`. `systemd-run` and `systemctl` are
likewise executed through retained descriptors.

The terminal rejects any positive delta for `max`, `oom`, `oom_kill`, or
`oom_group_kill`, nonzero swap, a peak reaching the cap, a nonzero/signaled
service status, a live unit, or a populated held cgroup. Owner journals and
held descriptors are cleaned before the create-exclusive terminal publication.
The heavy lock is released last. The parent-only `END` path performs bounded
stop/kill/reap and quarantines under the still-held heavy lock if zero cannot be
proved.

Focused fake-systemd contract:
`test/01_unit/scripts/bootstrap_stage3_unit_supervisor_test.shs`.
Final cycle result: `bootstrap_stage3_unit_supervisor=true`. It covers the green
path and lock non-inheritance, exact 3900-second property, all four memory event
deltas, positive-event rejection without PASS, missing-ControlGroup quarantine,
and loader-injection rejection before evidence creation. Perl syntax also
passed. The three-cycle cap is exhausted (one fixture-path correction, then two
green runs), so this lane must not rerun the test.

## Dependency-ordered remaining patches

1. Expand the fake-systemd contract with stale-journal owner-death recovery,
   direct-signal status, helper timeout, terminal collision/no-replace rollback,
   symlink replacement, and concurrent-winner cases. A fresh verifier must own
   those runs.
2. Add the shared Stage 3 runner that binds the admitted compiler, sampler,
   analyzer, exact descriptor/identity/argv/environment streams, compiler wall
   timeout, and zero-survivor raw terminal to this unit primitive.
3. Add a private Rust authority producer that builds seed/native-all/backfill
   only beneath the absent transaction output and proves global generation,
   markers, compatibility links, and target trees unchanged before/after.
4. Add the outer fresh/resume coordinator: Stage 2 (16 jobs/50 GiB), fresh
   planner admission, Stage 3 (1 job/8 GiB), strict root-GO/analyzer/planner/
   provenance-v4/resume-parent schema and run correlation, compatibility marker
   `authority=false`, and collision-safe rollback.
5. Publish `simple-stage3-transaction-admission-v1` only after every unit is
   inactive, every held cgroup is empty, all fallible cleanup is complete, and
   provenance-v4 verifies in external scratch. Then wire fresh/resume entrypoints
   and obtain independent orchestration, correlation, cleanup, and preflight
   reviews before any heavy launch.

Independent high-effort review is **HOLD**. Four code blockers remain for a
fresh implementation cycle: acquire the heavy lock atomically with
`O_CLOEXEC`; validate every stale owner/cgroup field (including deterministic
lane identity) before any `stop`; guarantee helper TERM/KILL/wait on exceptional
capture output; and move every fallible unlock/close before durable PASS
publication. The reviewer also found missing fault evidence for stale recovery,
helper overflow/timeout, direct signal status, publication collision, and role
replacement. The passing focused test therefore establishes useful behavior,
not component GO.

This first component does **not** implement provenance-v4, compatibility-marker
publication, private Rust authority, the shared compiler/sampler runner, or the
final transaction admission. It must not be described as root GO.

## Fresh four-blocker continuation (2026-08-20)

Status remains **HOLD pending final independent review**. The continuation started
from `stage3-unit-supervisor-v2.HOLD.apply_patch` SHA-256
`c15bb9095f54082e84e3c9ea88b61a467c3569b6b8dd2809c30c02c346eaa026`
in a new isolated copy. It did not touch an authoritative lane, Git, Stage 3,
or any heavy build.

The supervisor parent remains the sole canonical owner. Systemctl helpers are
bounded child domains whose output is copied into the parent and whose terminal
status must be reaped before commit. Owner/cgroup journals are frozen recovery
claims; neither may authorize a stop until the complete pair and the held
cgroup identity validate against the deterministic lane unit.

The isolated candidate fixes the four review blockers:

1. The heavy lock is opened atomically with Linux `O_CLOEXEC`, and the resulting
   descriptor flag is checked before `flock` can authorize work.
2. Stale owner and cgroup receipts require exact schemas/keys, architecture,
   phase, run correlation, deterministic unit, dead supervisor, cgroup path,
   canonical path, exact live `ControlGroup`, and device/inode identity before
   any `systemctl stop`.
3. Output overflow, read/close/wait failure, and helper timeout all enter one
   bounded TERM, KILL, and wait-to-terminal cleanup path.
4. Canonical PASS uses a prepared, fsynced inode plus a separately durable,
   exact non-PASS commit receipt binding its SHA-256 and device/inode. After
   zero proof, journal removal, descriptor closes, heavy-lock unlock, and
   heavy-lock close, one no-replace hard link is the final fallible operation.
   Acceptance requires the exact canonical terminal and durable receipt to
   match; either artifact alone is HOLD. Collision leaves the existing terminal
   unchanged and cannot satisfy the receipt.

Focused cycle 1 failed at Perl syntax because this host's `Fcntl` does not
export `O_CLOEXEC`. The Linux asm-generic value shared by the three admitted
architectures replaced that import and is guarded by an immediate `F_GETFD`
assertion. Cycle 2 passed syntax and the expanded focused contract in 10.26 s
with 11,008 KiB maximum RSS. The contract now covers valid stale recovery,
malformed stale cgroup no-stop behavior, helper overflow and timeout with no
survivor, service and supervisor signals, post-snapshot role replacement,
terminal collision/no-replace, lock release, and all prior cases. Do not rerun
the green criteria unless an independent reviewer requires a code change.

That review found three remaining in-scope publication/recovery defects: the
canonical hardlink lacked durable commit evidence, the stale cgroup path
accepted dot/empty components without checking the live `ControlGroup`, and
helper cleanup abandoned a child if `waitpid` was interrupted. Reserved cycle
3 fixed all three. Its single syntax/contract run passed in 14.64 s with 11,008
KiB maximum RSS. New deterministic cases cover commit-receipt parent-fsync
failure, SIGKILL after a durable non-PASS receipt but before canonical link,
lock release after that crash, path traversal, live-ControlGroup mismatch,
read failure plus injected `waitpid(EINTR)`, and stopped/populated-zero proof
after supervisor TERM. The three-cycle cap is now exhausted; freeze these bytes
and do not rerun the focused suite.

The final helper-only correction makes the pre-TERM waitpid observation
strictly one-shot: reaped returns, non-EINTR errors fail, and EINTR proceeds
immediately to TERM. The existing TERM and KILL observation windows retain
their absolute monotonic deadlines. A focused mutation injects EINTR for every
pre-TERM observation, records that TERM was delivered, and independently
fails after four seconds unless cleanup returns nonzero with no helper survivor
and no canonical terminal.

The final syntax and focused fake-systemd contract passed in 16.89 seconds
with 11,008 KiB maximum RSS. Its watchdog owns explicit recorded supervisor and
helper cleanup, so restoring the old unbounded retry cannot orphan the mutation
process tree.
