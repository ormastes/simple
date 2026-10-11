# Windows bootstrap loses a live authority lock after successful Cargo builds

Date: 2026-10-11. Status: repair under verification; Phase3 qualification pending.

Frozen source `20f619fe31baa4decbe40f6d367fb5e4f115bbd8`, Windows-MSVC,
LLVM 23.1.1. Attempt output:
`C:/dev/simple-bootstrap-storage/item2-phase3-verify-20261011`.

The Rust seed, native runtime variants and compiler backfill finished with exit
zero. The pre/post source fingerprints matched. Before publishing the built
authority, lock revalidation rejected the same owner PID and process group:

```
owner_pid=3721935
owner_pgid=3721935
expected start=554498359
observed start=554502731
error: Rust authority lock ownership was lost
```

No Stage2 compiler or Phase3 receipt was produced. The outer verdict retained
the previous compiler-backfill label despite that build's successful receipt.
The failed attempt and all Cargo artifacts remain preserved.

The old MSYS/Cygwin fallback used `/proc/<pid>/stat` field 22. Cygwin computes
that value by subtracting a system boot-time origin from native process creation
time ([upstream implementation](https://sourceware.org/pipermail/cygwin-cvs/2018q1/013505.html)).
The observed identity changed during this long-lived process; the precise host
event responsible for the origin change has not been established. A native
creation timestamp avoids dependence on that origin.

The repair records native Windows PID plus creation FILETIME, using the existing
Windows process observer. It checks two native process handles, checks the
MSYS-to-native mapping and process group before/after observation, and fails
closed on missing or inconsistent observations. Recycled-group refinement uses
the same native identity. A live group with an old boot-relative claim remains
held conservatively; the new representation never authorizes reclaiming it.

Regression: `portable_process_lock_windows_birth_test.shs` changes emulated
start ticks in a private helper copy while retaining the real native owner,
then verifies ownership, changed-birth rejection and foreign-release rejection.
The Windows observer and existing EXIT-trap lock contracts also require PASS.
Passing these focused checks alone does not prove bootstrap or Phase3 success.

Concurrent recovery fixture correction: contenders must check acquisition and
ownership before entering the protected section. Failed acquisition previously
continued into that section, causing false overlap diagnostics. Failure traces
are now retained, and a contender that did not create the section marker cannot
remove another contender's marker during cleanup.

Performance follow-up: four simultaneous native-identity contenders on this
host exceeded the old 15-second acquisition budget. One acquired after 18
seconds; three returned timeout (75) after 24–25 seconds, without admission.
Evidence: `/tmp/portable-process-lock-test.4027779/recovery.*.trace`.
Windows recovery tests now allow a bounded 120 seconds; other hosts keep 15.
This is a test scheduling budget, not a claim of improved lock latency.
The owner of `windows-process-observer.ps1` should investigate avoiding repeated
PowerShell startup while preserving birth checks and fail-closed behavior.
