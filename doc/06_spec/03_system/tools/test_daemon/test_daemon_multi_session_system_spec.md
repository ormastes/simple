# Test daemon multi-session broker coordination

Executable: `test/03_system/tools/test_daemon/test_daemon_multi_session_system_spec.spl`.
Requirement: `REQ-SSPEC-SYSTEM`.

Status: **All eleven scenarios have focused passing evidence across three source
snapshots**: two baseline cases, four capacity cases, and five identity cases.
This is not one complete-file run, a current-tree full PASS, a native-product
PASS, or live-environment qualification. Docgen remains pending; this guide is
maintained by hand.

| Cycle | Selected scenarios | Result | Source scope |
|---|---|---|---|
| One | Original four | 2 PASS, 2 FAIL | Baseline; retain kind/architecture and shared-reuse PASS |
| Two | Original capacity + three added capacity edges | 4 PASS, 0 FAIL; 435 ms | Capacity repair snapshot |
| Three | Original fresh identity + four added identity contracts | 5 PASS, 0 FAIL; 895 ms | Identity repair snapshot; exit 0, quiescent 1 |

Retained logs under `build/phase-one-ui-diagnostic/`:
`test_daemon_multi_session_system_spec/cycle-one.log`,
`daemon-capacity-cycle-two_spec/cycle-two.log`, and
`daemon-identity-cycle-three_spec/cycle-three.log`.
Each has adjacent `.rss.env`, `.exit`, and `.command.json` receipts.
The corresponding manifests are `platform-daemon-inputs.json`,
`platform-daemon-cycle-two-inputs.json`, and
`daemon-identity-cycle-three-inputs.json`; the final source patch is
`daemon-identity-cycle-three.patch`. These bind the selected exact scenario
blocks and source identities; earlier passing cases were not rerun. The final
review reported zero new P0/P1 findings. No fourth daemon cycle was performed.

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
The baseline identity regression showed that stopping
one duplicate ID removed both leases. The repaired regression passed in cycle three. See
[identity and admission follow-up](../../../../08_tracking/bug/test_daemon_fresh_instance_identity_and_admission_2026-10-11.md).

The identity follow-up allocates a compact process-owner namespace plus a serial
allocation sequence in the descriptor before startup. Shared grouping keys stay
unchanged; broker code preserves adapter-returned resource identities. Capacity
refusals now use an empty-ID `LEASE_PENDING`, which cannot address a tracked
lease. The daemon response and concrete adapter dispatch remain unqualified.

Four added identity contracts passed in cycle three: descriptor IDs differ for
matching keys and survive default-adapter startup; independent brokers allocate
distinct instances; pending handles cannot release or stop an occupied lease;
incomplete descriptors fail closed. Together with the original fresh-instance
regression, these account for the five selected cycle-three cases.

A P2 follow-up remains at `src/app/test_daemon/daemon.spl:352–357`:
`handle_session_acquire` returns `TRESP_COMPLETED` even for an empty-ID
`LEASE_PENDING` handle. Queue/retry or explicit refusal semantics must be wired
at that response boundary; broker pending safety alone does not close it.

QEMU socket and container adapter resource names consume descriptor identity;
service, hardware, remote-PC, and native/headless GUI leases do as well. GUI
container mode remains explicitly excluded: its fixed resource name and missing
container lifecycle dispatch require a separate repair. Headless GUI display
allocation, hardware port isolation, and live resource admission are unverified.

The legacy `test/system/test_daemon/test_daemon_multi_session_system_spec.spl`
constant-only duplicate is removed. Architecture, kind, and reuse-policy intent
is now tested through production owners. Coverage annotations declare 80%
targets; no measured coverage or passing counts are claimed.
