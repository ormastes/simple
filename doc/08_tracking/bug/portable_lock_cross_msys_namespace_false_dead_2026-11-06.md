# Portable lock: a live MSYS owner is classified dead from Git Bash

Status: reproduced; not fixed. Date: 2026-11-06. Source pin:
`6e03930143983a5c9861321f67aff300b07f16ed`.

## Failure and evidence

The node-attribute bootstrap attempt 4 ran under `C:/msys64/usr/bin/bash.exe`.
Its seed and native-all Cargo builds both completed successfully (native exits
0; 16m58s and 10m16s). The parent then aborted with
`portable-lock: ownership check failed reason=claim-read` before runtime-nolto
and self-hosted admission. No lifecycle feature test executed.

The common Git cache lock at `D:/dev/simple/.git/simple-rust-cargo-cache-locks`
then belonged to a different live Git Bash bootstrap in `D:/dev/wt/boot2`:
native PID 27876, runtime-local PID 395. That process was not stopped and its
lock was not removed. Ownership replacement alone does not prove which actor
removed the original claim; the focused read-only probe below establishes the
underlying false-dead classification.

## Focused reproduction

Using the existing `portable-process-lock.shs` and `portable-hardlink-lock.pl`:

1. Acquire a private `probe` lock from MSYS Bash and keep that shell alive for
   45 seconds. The root is inside the isolated bootstrap worktree at
   `build/node-attributes-qualification/lock-namespace-probe`.
2. From `C:/dev/tool/Git/bin/bash.exe`, load that same claim and call
   `portable_lock_claim_state` with its recorded PID/start/group. Do not acquire
   or recover the lock from the second shell.
3. Actual result: `dead`, exit 0. Expected: `live`, or conservatively `unknown`.
4. The owner exec session was polled and remained running after that result.
   Its claim recorded local PID/group 953 and native Windows PID 24116 in the
   decoded `owner_start_hex`. The owner later released the claim and exited 0.

`claim-state` first calls `process_snapshot($pid)` and `pid_absent($pid)` and
then checks `$pgid`. These POSIX IDs are local to the MSYS runtime. A native
Windows identity in the start field does not make local PID absence in another
runtime proof of Windows process termination. Recovery must check the recorded
native PID plus birth identity, or fail closed across unrecognized namespaces.

## Containment and required fix

Use one Git Bash runtime for cooperating Windows bootstrap lanes while this is
unfixed. Preserve the existing cache; never bypass ownership checks or delete a
foreign live claim. The explicit shared Cargo cache-root override is rejected
on Windows by the current canonical bootstrap and is not a workaround.

Add a cross-runtime test covering live-owner classification and refusal to
recover, followed by normal owner release and genuine dead-owner recovery.
Also retain the existing same-runtime PID-reuse/group-survival tests. No helper
implementation was modified in this report. The node-attribute bootstrap's
terminal log and bounded-process receipts remain under its isolated
`build/node-attributes-qualification` and `build/bootstrap/node-attributes-runtime`.
