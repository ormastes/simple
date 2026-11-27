# Durable parent-owned Engine exec continuation

Source: `test/01_unit/lib/nogc_async_mut/container/providers/linux/engine_exec_owner_v3_spec.spl`.

Fourteen authored scenarios, UNEXECUTED. Journal fixtures use actual temporary files, mode0600 publication, directory barriers and generation-bearing owned locks. Structural requests/receipts represent journal test data, not live Engine birth. No Unix connection token or native effect is fabricated.

| Scenario | Oracle |
|---|---|
| Record invariants | Impossible prepared/known/start/unknown combinations and unknown-create resurrection refuse. |
| Real WAL/CAS | Immutable payload remains unchanged; actual mode/UID metadata checked; stale full-row CAS refuses without replacing the newer row. |
| Birth crash window | Existing canonical birth file repairs creating/io-armed record to durable known ID under real lock/barriers; no caller ID or create retry. |
| Conflicting birth | Wrong original query binding leaves unknown-create row unchanged. |
| Stale actual owner | Both send and close stages call the real continuation, reject stale revision before any Unix executor entry, and never invent a handle. |
| Cleanup qualification | Only exact durable before image or exact attempted after image qualify; arbitrary latest revisions refuse. |
| Actual publication readback | Real continuation rereads the attempted publication and performs a real directory barrier without inventing connection/response ownership. |
| Live-used reducer | Full accepted writes advance to read, partial progress preserves offset, zero remaining write refuses, connect timeout is not Pending, whole expiry stops Pending. |
| Begin boundary | Unsupported action rejects before native CLI or WAL work. |
| Local cleanup | No-connection cleanup completes locally, blocks later sends and preserves durable facts without a journal access. |
| Stale/prestart evidence | Stale-view cleanup does no I/O; a start turn never returns its earlier verify inspection as post-start evidence. |
| Separate inspect | Structural original binding permits expired admission; public mutation begin refuses inspect, and observation-free inspect rejects a foreign parent before native work. |
| Lifetime claim | Actual owned session-lock contention refuses a second owner; confirmed release permits reacquisition, stale generation release and stale-view cleanup cannot release the new claim. |
| Retirement refusal | Attempted durability ownership prevents cleanup_complete without inventing a connection. |

Mutation entrypoint is `LinuxOciEngineExecOwnerV3.begin` (create/start only); read-only `inspect` takes no caller observation and does not borrow launch expiry. Parent continuations use `step(1..25)`. One actual Unix operation is performed per successful continuation. The native wait slice starts after durable arming and is capped by the fixed whole transport deadline. It does not bound filesystem fsync/lock syscalls or synchronous CLI hashing/capture wall time.

Before each I/O, the owner acquires the existing owned lock, matches the exact WAL revision and durably arms the step. Stale copies are diagnostic views with no send/read/close authority. Publication uncertainty retains the exact before/attempted images, candidate birth, lock cleanup and connection independently; readback never adopts arbitrary newer state. Unknown lock-close outcomes remain quarantined. The existing directory owner invalidates before native close; its close-error is consumed and is not blindly retried.

Create submission uncertainty cannot retry. Known ID and canonical original birth are published before start. Orphan birth repair verifies the original request, control pin and canonical create query, then flushes before an exact-ID GET. Reconciliation returns the original retained birth without synthesizing new timestamp/evidence. Read-only inspect retains prior lifecycle classification; false Running/zero ExitCode is not terminal proof.

Immutable payload stores canonical request, original Host intent, original operation envelope, parent request and installed artifact. The provider checks SDN escaped size before encoding and caps it at16MiB; the individual bounded records can nest escaped1MiB request,2MiB Host intent and parent bytes, so the earlier proposed3MiB was insufficient. Small CAS rows remain capped at8KiB. Payload and birth remain private mode0600 under the existing trusted state-root assumptions; no new generic journal, raw lock, worker registry or broad prune is introduced.

Pending acceptance: real signed Host loader/child begin, common facade composition, actual peer-correlated create/start/inspect, timeout/partial-send and close-error native paths, and crash process restart. No compiler builds, executable specifications or native tests were run for this source slice. Whitespace and direct-environment source guards passed; these do not qualify runtime behavior. TTY, stdin, output ownership, renewal and scheduler work are outside this checkpoint.

`cleanup()->Turn` abandons only the local transport through the same revision-guarded continuation. It never stops the exec/container or releases capacity. `cleanup-complete` means local owners are gone, while any error/effect uncertainty and durable birth/start facts remain retained. Stale views perform no cleanup I/O.

Cycle5 repair: a generation-bearing `.session.lock` lifetime claim is held separately from each step WAL lock. Every existing create record refuses a new create begin, including unarmed/probing rows. The lifetime claim is released only after native transport and WAL cleanup resolve under canonical revision proof; stale views never release copied claims. Retained/unknown generation outcomes remain owned and no raw descriptor retry is attempted. Mutating writes check the already-bound raw request digest/operation/action and actual Unix clock without re-encoding the multi-MiB context each chunk; begin retains full original-context validation.

The additive `cleanup_complete` result is derived only from an explicit cleanup request, no stale view, and empty connection, per-step lock, lifetime lock and attempted-publication owners. Error remains independently reported. It proves local retirement only, never actual exec termination or capacity release.
