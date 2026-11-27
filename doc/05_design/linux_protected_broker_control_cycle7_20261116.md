# Actual cycle7 broker control ports — source only

This source extends the original protected resource allocation and existing journal health slot. No second writer, owner registry, raw descriptor getter, runtime export, or reader-to-mutation public factory is added. Native/compiler/spec execution is NOT_RUN.

## Exact trusted chain

`linux_protected_root_broker_acquire_v1(journal, installed, operation_key, claim_digest, selected_root, origin_ms, deadline_ms, offered=nil) -> LinuxProtectedBrokerAcquireTurnV1`

The caller is the reviewed installed Host producer in canonical package `lib.nogc_sync_mut.orchestration`. It derives operation/attempt/root authorization from the actual same journal and retained installed policy before calling. The narrow journal bridge validates the actual original protected writer, private health binding, owner state and stored CURRENT. The existing health slot reserves the exact operation/claim/installed-reader identity/root before opening the external reader. A duplicate returns the original reader, deadline and opening/error state; it does not reopen. Different claims for the same root are refused. Sixty-four entries bound one journal lifetime; tombstones are never recycled. This is a finite refusal limit, not an unbounded recovery registry.

Acquire fields: `journal`, `installed`, `reader?`, `ready`, `origin_ms`, `deadline_ms`, `rejected_offered?`, `facts_known`, `completed`, `error`. Capture all returned custody before checking flags. An extra offered reader not adopted remains in `rejected_offered`; never close the canonical child through that arm. The parent journal health slot retains every actual child/opening ticket before errors. A broken health mutex leaves retained canonical custody and does not claim recoverable progress or successful close.

`linux_protected_root_broker_cancel_begin_v1(parent, expected_root, identity, original_deadline_ms) -> LinuxProtectedBrokerControlTurnV1`

`linux_protected_root_broker_cancel_step_v1(loan) -> LinuxProtectedBrokerControlTurnV1`

Turn fields: actual `parent`, opaque `loan?`, `facts_known`, `publication`, `pending`, `observation?`, `consumed`, `durable_required`, `error`. The reader must bear the opaque original-journal adoption claim. Every effect checks that claim against the still-held actual writer and canonical child, then uses only the original child FD under its existing health ticket. The Host must independently revalidate current installed/approved historical policy, exact operation/attempt and original deadline before every call. The lower mechanism is not a replacement authorization policy. Fresh nonce, fixed request, atomic rename, forced transient response reads and once-consumption are real source implementations. `durable_required` is only a diagnostic that the echoed terminal reply cannot serve as proof. Matching nonterminal cancellation ACK is not durable absence, reap, Host outcome or resource release.

`linux_protected_root_broker_reap_publish_v1(parent, expected_root, identity, canonical_reap_bytes, original_deadline_ms) -> LinuxProtectedBrokerReapTurnV1`

Reap fields: actual `parent`, `facts_known`, `publication`, `verified`, `error`. Caller must first derive canonical bytes from genuine `GroupProcessStreamRecoveryOwnerV3.prospective_reap_bytes_v3(actualLease)` and exact original Host admission. No bytes/ACK constructor grants this effect. Only `tree-reaped.sdn` may be linked without replacement. Existing exact bytes are accepted; mismatches are retained errors. Host separately validates reap, commits/readbacks protected metadata and original journal outcome. An expired deadline permits checking an existing exact receipt, never a new publication.

`linux_protected_root_broker_release_v1(journal, installed, operation_key, claim_digest) -> LinuxProtectedBrokerAcquireTurnV1`

Only the reviewed Host calls release after genuine required settlement, or explicitly authorized resource-abandon cleanup that makes no workload completion claim. It drains one exact child cleanup step and stores returned opening state before errors. Pending returns the retained canonical reader; completed leaves a tombstone and invalidates old loans. Original reader aliases cannot close an adopted child. Journal shutdown uses the same bounded child drain before releasing the writer; closing resource custody never asserts broker termination or completed Host work.

## Restricted compiler policy

RootReader: friend `lib.nogc_sync_mut.orchestration`; internal_export the five exact acquire/release/cancel_begin/cancel_step/reap_publish free functions. Health: friend `lib.nogc_sync_mut.io`; internal_export `OperationJournalLinuxStorageBorrowV1` and the fixed claim-current function. Storage: friend `lib.common.task_runner`; internal_export `LinuxProtectedStorageResourcesV1`. Journal bridge: friend `lib.nogc_sync_mut.io`; internal_export `distributed_operation_journal_broker_borrow_v3`. Opaque claim/loan fields and constructors remain private even for friends. This is package visibility, not an exact-file allowlist.

Protected build admission requires actual strict `SIMPLE_HIR_ENFORCE_MEMBER_VISIBILITY=1` plus Deny enforcement and policy-bound build/cache identity. Qualification is pending in the separate compiler lane. Default-off artifacts cannot claim these restrictions. Runtime origin, original writer, claim, deadline, nonce and once fences remain mandatory regardless.

## Source dependencies and limits

Accepted authR2 plus reader extension4 are exact preimages. Fixed cancel codec and actual prospective reap producer are separate dependencies. Host worker owns public installed authorization/effect orchestration and real owner-bearing fixtures. No full live control or compiler privacy qualification is claimed by this leaf. Partial stage publication or consumed-close uncertainty retains original resources, diagnostics and Host charge; no blind unlink, rearmed retry, or fabricated cleanup receipt.
