# Machine paired cleanup V1 production transition

Status: **AUTHORED_NOT_RUN**. Mirrors
`test/01_unit/lib/container/machine_cleanup_progress_v1_spec.spl`.
No native fault, descriptor close, principal owner or storage writer ran.

These assertions exercise the actual production pure cleanup reducer. They do
not inject a fake native close result into an actual owner or claim a native
fault was reproduced.

| Requirement | Authored production transition assertions |
|---|---|
| REQ-MACHINE-PAIRED-CLEANUP-001 | Machine `consumed-error` marks that component closed and records its diagnostic; retained principal leaves only the partner live; later principal release returns closed-with-error and preserves the original diagnostic. |
| REQ-MACHINE-PAIRED-CLEANUP-002 | Copied progress values cannot overwrite a consumed component or first diagnostic. Unknown and stale text remain retained. Only positive released/consumed-error or this pair's previously recorded closed state permits consumption. |

The actual authority owns a private canonical id/generation registry so copied
authority/cleanup handles observe the same progress. It checks actual process
and genuine native process-origin guard before accessing that state, skips confirmed-consumed native
components and retries only live partners. Diagnostic access remains available
after resources are consumed. No numeric descriptor is reconstructed or retried.

Actual value-copy aliases through the native domain close path have a separate
authored scenario in the direct local process admission manual. CloseHandle,
HeapFree, Linux close faults, process/thread changes and interrupted cleanup
remain native fault-fixture obligations, all **NOT_RUN**.
The Linux process-lifetime procfs origin latch must run before inherited registry
access or closed-status reporting; matching numeric PID/TID alone is insufficient
after a fork/PID-namespace collision. Windows uses the actual canonical native
process/thread guard. The pure transition is not a substitute for either guard.
