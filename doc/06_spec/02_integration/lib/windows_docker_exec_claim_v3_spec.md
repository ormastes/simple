# Windows installed-state exec claim consumer

Status: **SOURCE-ONLY NOT_RUN**. No compiler, native filesystem, Engine request,
parallel broker or Windows process was executed.

Source: `src/lib/nogc_async_mut/container/providers/windows/docker_exec_claim_v3.spl`.
Spec: `test/02_integration/lib/windows_docker_exec_claim_v3_spec.spl`.
Fixture: `test/fixtures/orchestration/windows_docker_exec_claim_fixture_v3.spl`.

The consumer accepts one retained `ContainerExecStateAccessV3` from the Host
factory above verified unique deployment and completed installation. It accepts
no native root, helper-root path or generic metadata wrapper. The lower namespace
is canonical full scope plus child operation ID; changing helper, argv, environment,
installation or request cannot select a new namespace for the same operation.
The immutable record contains the full installed-state binding and original stream
and query template. Mismatch refuses; old helper-root records are not migrated.

`from_installed_access_v3` correlates the access binding with the original exec
admission, expected installation artifact and deployment claim. Every reserve
rechecks the retained binding and current admission clock. Publication must report
success and read back the exact bytes before CreateReserved or StartReserved.
Errors retain the whole updated access, including native cleanup held inside it.
Only Create, Birth and Start record kinds are available; there is no deletion.
Records are bounded to four MiB by the shared port.

Ready means persistence-owner availability, never Engine permission. A copied
phase or binding does not authenticate Host signatures or consume a native effect
continuation. The actual broker/effect owner must still verify delegated proofs,
consume one-use authority and check the live deadline before native submission.
The GET-only exchange remains closed to mutations.

| Authored case | Intended observation |
|---|---|
| Create/birth/start | Readback before reservation; expired pre-start retains birth; fresh start once; reopen never retries |
| Two access instances | Interleaved same-namespace consumers cannot both reserve fresh create; unresolved create survives restart |
| Changed content | Different helper, argv or environment under the same scope/child operation collides and refuses |
| Installed binding mismatch | No publication; acquired access retained for cleanup |
| Readback and close faults | Publication uncertainty remains unknown; failed close retains updated owner for retry |
| Invalid birth | Candidate remains diagnostic, no verified birth or start |
| Birth-only restart | Unreadable start record is unknown, not absence or permission |

These are explicit scripted lower-port protocol/fault cases exercising the actual
claim consumer. They do not qualify atomic Windows publication, real concurrent
brokers, protected-root uniqueness, signed Host enrollment or native close faults.
The previous arbitrary-helper-root fixtures were removed because their origin
cannot satisfy the required installed role. Actual factory tests must cover two
helper roots, copied installed metadata, simultaneous native brokers, crash after
reservation before birth, and unknown create/start restart. Those gates remain
outstanding. Native private-file ACL/fault tests belong to the shared file owner.

Birth-only reopening conservatively returns UnknownStart when the lower read port
cannot distinguish missing from denied/corrupt records. The uninterrupted owner
may accept refreshed start authorization before its first reservation. Neither
file cleanup nor helper Job collection proves exec exit or releases parent charge.

Dependency: shared `exec_state_access_v3` at `27ee281d3c0`, actual Host deployment
and completed installed-state producer, generic exec/original-intent admission,
and Windows stream/control codecs. This consumer alone is not full effect closure.
