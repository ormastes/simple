# Test daemon multi-session broker coordination

Executable: `test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl`.
Requirement: `REQ-SSPEC-SYSTEM`.

Status: **Focused capacity PASS; fresh identity remains FAIL / OPEN**. Evidence
comes from two source snapshots, not a complete rerun of the revised seven-case
file. Baseline cycle one passed scenarios 1–2 and failed scenarios 3–4. After
the broker repair, cycle two ran only scenario 4 plus new scenarios 5–7:
**4 passed, 0 failed, 435 ms**, process exit zero. Scenarios 1–2 retain their
baseline PASS; scenario 3 retains its unchanged baseline FAIL. No whole-file
or whole-suite PASS is claimed. This manual is maintained by hand; docgen
remains pending.

Baseline log:
`build/phase-one-ui-diagnostic/test_daemon_multi_session_system_spec/cycle-one.log`.
Focused repair log:
`build/phase-one-ui-diagnostic/daemon-capacity-cycle-two_spec/cycle-two.log`.
Each has adjacent `.rss.env`, `.exit`, and `.command.json` receipts.
`build/phase-one-ui-diagnostic/platform-daemon-inputs.json` binds the baseline;
`build/phase-one-ui-diagnostic/platform-daemon-cycle-two-inputs.json` binds the
repair production source, canonical spec, and extracted exact scenario blocks.

1. Register the production default adapter descriptors and acquire QEMU-kind
   leases for ARM64, RISC-V, and x86-64, plus a container-kind ARM64 lease.
   Require distinct identities, independent kind counts, and no running process
   claim. Execution through the default adapter must report failure with zero
   passed tests. Stop the container alone, then shut down the broker.
2. Acquire two architecture leases. Release and reacquire the matching ARM64
   lease; its identity must be reused and test count incremented, while RISC-V
   retains its original count. Removing the ARM64 lease must preserve RISC-V.
3. Acquire identical fresh-per-test requests with release between them. Require
   independently addressable identities and count one per instance. Stopping
   the first must preserve the second.
4. Set the QEMU maximum to one. A second fresh request must not grow that pool
   beyond one; eviction of idle capacity or refusal are both permitted by this
   cap assertion. A container request must remain independently admissible.
5. With QEMU capacity zero, refuse a fresh request without tracking a lease.
6. At a fully active capacity of one, refuse fresh admission while preserving
   the existing lease identity and test count. This exercises active bookkeeping
   only; the default adapter still has no running environment.
7. After lowering capacity below the existing pool size, refuse another
   architecture without evicting and replacing a lease while still over limit.

The first two scenarios exercise broker bookkeeping with the production default
adapter. That adapter deliberately returns PID zero and an idle lease, and its
execute method fails. These scenarios do not establish successful environment
startup, health, or real test execution. Live QEMU/container startup, concurrency,
reset, shutdown, and cross-architecture execution remain required and unverified.

The baseline exposed two defects: fresh requests bypassed capacity checks, and
repeated fresh requests received identical session IDs. The broker repair now
skips only idle reuse for fresh requests and applies the normal capacity gate.
Zero capacity refuses admission; an already-over-limit pool also refuses new
admission without destroying existing leases. The four capacity checks passed in the focused second cycle described above.
The identity regression remains unresolved: stopping
one duplicate ID removes both leases. See
[identity and admission follow-up](../../../../08_tracking/bug/test_daemon_fresh_instance_identity_and_admission_2026-10-11.md).

A refused acquisition still uses the existing untracked default lease shape;
this repair does not claim an explicit pending protocol or adapter lifecycle
fix. Live resource admission remains unqualified.

The legacy `test/system/test_daemon/test_daemon_multi_session_system_spec.spl`
constant-only duplicate is removed. Architecture, kind, and reuse-policy intent
is now tested through production owners. Coverage annotations declare 80%
targets; no measured coverage or passing counts are claimed.
