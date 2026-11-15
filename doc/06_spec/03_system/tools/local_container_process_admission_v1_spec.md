# Actual direct local process admission refusal V1

Status: **AUTHORED_NOT_RUN**. Mirrors
`test/03_system/tools/local_container_process_admission_v1_spec.spl`.
No native fixture, compiler, runtime, provider command or doc generator ran.

The executable fixture requires an administrator-installed standalone machine
policy, exact prefixed membership for the actual current process, the real OS
principal producer, the actual selected provider observer and an empty machine
WAL. It never installs policy, changes ACLs, injects identity values, substitutes
an enrolled Host grant or treats an unsupported platform as a passing case.

| Requirement | Authored assertions |
|---|---|
| REQ-LOCAL-PROCESS-ADMISSION-001 | Acquire a genuine process capability and installed standalone foundation. Submit canonical request metadata; require migration-fence refusal and unchanged actual WAL head. Close through two actual copied domain handles and require the shared completed cleanup disposition. |
| REQ-LOCAL-PROCESS-ADMISSION-002 | Close a genuine separate process owner, then submit malformed metadata through its stale copied handle. Require stale-owner refusal before request decoding and retain a current domain for exact cleanup. |

The standalone-only zero-argument factory rejects managed mode immediately
after reading actual installed policy, before provider observation or principal
creation. It authenticates actual process membership before observing its
standalone provider and retains that principal through reader-to-writer
transfer. A pending machine-writer close preserves the principal; after writer
close the principal can close. Data snapshots, UID/SID text, PID values and
booleans cannot manufacture either capability.

Separate mandatory fixture profiles remain **MANUAL_NOT_RUN**: managed mode
refusal, unlisted actual native principal, wrong Linux service UID, namespace
or token drift, unsupported retained WAL history, failure while transferring
reader/principal ownership and retained native cleanup. Managed-mode ordering
is source-reviewed; this fixture does not instrument provider calls to claim
dynamic no-effect coverage.

`process_admit_v1` validates actual process identity and exact policy membership,
canonical request metadata and configured resource ceilings. Empty WAL refuses
because a genuine legacy-writer/provider migration fence is absent. Retained
history refuses because no supported standalone debit/adoption and native
absence settlement capability exists. No positive reservation, provider create,
terminal adoption or capacity release is exposed.

This boundary is direct in-process authorization. A service cannot authenticate
a client by passing its own process principal; kernel-authenticated peer
capability production remains a separate requirement before Caret daemon use.
