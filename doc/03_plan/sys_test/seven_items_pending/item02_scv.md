# Item 2: SCV + jj + GitHub textual databases

Status: NOT_IMPLEMENTED acceptance scenarios. This status describes the new scenario bodies, not the implementation status of the product. Criteria were authored before their SSpec skeletons. No tests or compilers were run.

Executable skeleton: [item02_scv_spec.spl](../../../../test/03_system/seven_items_pending/item02_scv_spec.spl).

## Sources and existing coverage

Canonical umbrella: [seven-item host completion plan](../../seven_plans_host_completion_2026-09-29.md), item 2. References: [selected functional requirements](../../../02_requirements/feature/simple_distributed_textual_databases.md), [selected NFRs](../../../02_requirements/nfr/simple_distributed_textual_databases.md), [research](../../../01_research/app/tools/scv/simple_distributed_textual_databases_scv_jj_github_2026-09-13.md), [architecture](../../../04_architecture/simple_distributed_textual_databases.md), [detailed system plan](../simple_distributed_textual_databases.md).

Existing `test/03_system/app/scv/feature/simple_distributed_textual_databases_spec.spl` has 153 intentional fail-fast contract cases covering REQ-001–036 and NFR-001–015 happy/boundary/failure paths. Those remain the detailed contract catalog. This file adds combined two-replica, jj-history, settlement, adapter, retention and per-host campaigns; it does not duplicate their individual checker bodies. AC01–04 combine identity/transaction/convergence/publication; AC05–08 combine evidence/adapters/retention/security; AC09 adds the Operating-B workflow gate and AC10 the complete host campaign.

The new scenarios are umbrella end-to-end campaigns. They preserve the existing detailed tests and requirements; they neither replace those catalogs nor certify completion. Windows first, then Linux/WSL is execution ordering, not removal of other supported hosts.

## Acceptance criteria

### S7-I02-AC01: offline identity and jj history survive round trips

- Requirements: REQ-001 REQ-002 REQ-003 REQ-004 REQ-010 REQ-011 REQ-015 NFR-014 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Two isolated clones with the same schema, separate durable actor incarnations, Unicode/delimiter-like fields and recorded SCV/jj revisions; one restored counter snapshot.
- Action: Create offline records, serialize typed patches, advance jj history, reconnect, settle aliases and replay the accepted log.
- Observable result: Distinct offline identities converge to permanent context-bound aliases without changing SCV identities; rollback rotates incarnation; canonical bytes and full/incremental state digests agree; invalid bare aliases or reused batch IDs with changed bytes refuse.

### S7-I02-AC02: local transaction validation precedes durable mutation

- Requirements: REQ-006 REQ-010 REQ-012 REQ-029 NFR-012 NFR-013 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Disposable checkout with valid schema/references and SJ writer ownership, plus unauthorized, stale-version and broken-reference patches and a second local writer.
- Action: Submit valid and invalid patches through the app boundary while another writer contends, then interrupt atomic replacement and reopen the database.
- Observable result: Only authorized valid transactions become durable; invalid patches change neither aliases nor state; recovery exposes one complete pre/post state, never a partial tree; network waits release the lease and adapter writes cannot bypass ownership.

### S7-I02-AC03: two offline clones converge without erasing conflicts

- Requirements: REQ-013 REQ-014 REQ-015 REQ-027 REQ-028 NFR-010 NFR-014 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Two replicas share a base containing scalar, set and tombstone fields with recorded causal history.
- Action: Make independent-field edits, same-scalar conflicts and delete/update races offline; exchange changes in both orders, resolve explicitly, replay and inspect jj/SCV history.
- Observable result: Independent edits merge; incompatible and tombstone races remain durable conflicts until reviewed resolution; accepted replay is idempotent; no resurrection or acknowledgement loss occurs and converged state/history retain original causal relationships.

### S7-I02-AC04: protected remote settlement recovers races and lost acknowledgements

- Requirements: REQ-005 REQ-007 REQ-008 REQ-009 REQ-022 NFR-006 NFR-010 NFR-013 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Designated disposable protected GitHub remote with two authorized integrators, pinned tool versions and expected-head/read-back capability; independently inspectable accepted history.
- Action: Race publication, lose one acknowledgement, restart the worker, restore connectivity, then present an old authority receipt or missing protection capability.
- Observable result: Exactly one complete candidate wins each expected-head update; loser replans and uncertain sender reads back before allocating; numbers never reuse, regression blocks settlement, and recovery is under 10 minutes after dependencies return without discarding oldest pending work.

### S7-I02-AC05: test observations remain immutable across CI discovery and evaluation

- Requirements: REQ-016 REQ-017 REQ-018 REQ-019 REQ-020 REQ-021 REQ-024 REQ-025 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Revision-pinned configuration/reproduction and a run manifest with planned shards; duplicate, reordered, changed-payload and missing events from event/poll/bundle adapters.
- Action: Ingest events, restart between durable receipt and cursor advancement, retry discovery, evaluate pinned expectations and attempt CI policy mutation.
- Observable result: Identical observations deduplicate while distinct attempts remain; changed bytes quarantine; all ten required entity kinds retain immutable revisions; absent shards remain NOT_RUN/INCOMPLETE, evaluations distinguish specified outcomes and CI cannot approve expectations or promote configuration.

### S7-I02-AC06: GitHub and alternative bridges respect delivery authority

- Requirements: REQ-023 REQ-024 REQ-025 REQ-027 REQ-028 REQ-029 NFR-012 NFR-015 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Designated GitHub/Actions test project plus non-GitHub Git, GitLab-CI and Jenkins-class capability fixtures, scoped credentials outside evidence and pinned last-common provider state.
- Action: Drive a semantic edit through bridge intent, remote delivery and read-back; inject create timeout, permission loss, duplicate delivery and conflicting provider field edits.
- Observable result: Acknowledgement requires reconciled effect identity; uncertain delivery cannot duplicate remote creation; permission loss is not deletion; provider IDs remain namespaced, causation loops stop and credentials never enter database/test artifacts.

### S7-I02-AC07: retention and resnapshot preserve query truth and pinned evidence

- Requirements: REQ-030 REQ-031 REQ-032 REQ-033 REQ-034 NFR-007 NFR-008 NFR-009 NFR-010 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Controlled CAS, pinned unresolved failures/releases and ordinary observations through day 28 plus a reproducible ten-year-equivalent cohort and an offline stale replica.
- Action: Query exact and rolled-up history, ingest late duplicates, hydrate a pinned 100 MiB bundle, resnapshot and reconnect the stale replica.
- Observable result: Routine observations remain exact for at least 28 days; later summaries retain revised provenance and never average daily percentiles; queries label exact/aggregated/restricted/unavailable honestly; pins have 100% verified closure and local hydration is at most 5 seconds; stale operations require typed resnapshot; packed Git and full-clone transfer each remain at most 2 GiB, CAS separately reported.

### S7-I02-AC08: untrusted import and key changes fail without secret publication

- Requirements: REQ-006 REQ-026 REQ-035 NFR-010 NFR-011 NFR-012 NFR-013 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Quarantined malicious archive variants with traversal, links, decompression growth and secret fields; algorithm-tagged signed patches across namespaces and rotated/revoked keys.
- Action: Import bounded bundles without executing reproduction content, attempt cross-domain replay and revoked-key publication, and exercise restricted evidence deletion policy.
- Observable result: Malformed/quota/unauthorized inputs publish no settled identity or secret metadata; signatures bind version/domain and enforce revocation; no privilege escalation occurs; deletion reports distinguish controlled key erasure from immutable clone/history bytes that cannot be guaranteed erased.

### S7-I02-AC09: Operating B measures real indexed and maintenance workloads

- Requirements: REQ-002 REQ-015 NFR-001 NFR-002 NFR-003 NFR-004 NFR-005 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: At least 1,000,000 aliases and observations with representative conflicts and a 10,000-observation import, on the declared reference machine and pinned Git/jj/tool versions.
- Action: Run indexed alias/status/dedup queries, complete validated import, million-row compaction dry-run and 10,000-operation resnapshot/rebase with raw receipts.
- Observable result: Alias/status p95 each at most 100 ms and dedup p95 at most 250 ms, with p50/p95/p99; import at most 5 seconds and 256 MiB RSS; compaction at most 10 seconds and 512 MiB; rebase at most 60 seconds; receipts retain dataset/tool/host/sample/timeout identities and all measured validation work.

### S7-I02-AC10: host-specific filesystem behavior cannot counterfeit convergence

- Requirements: REQ-011 REQ-029 REQ-036 NFR-013 NFR-014 NFR-015 (IDs belong to the linked item-specific requirement documents).
- Status: NOT_IMPLEMENTED.
- Setup: Separate supported-host lanes for Windows native, Linux/WSL, Linux native, macOS and FreeBSD with case-sensitive/insensitive paths, Unicode and mixed line-ending fixtures; SimpleOS requires explicit capability admission.
- Action: Repeat the two-clone transaction, locking, replacement, conflict and recovery campaign using the same semantic core and compare durable receipts.
- Observable result: Canonical database digests and semantic outcomes agree despite documented adapter differences; no per-host sibling or raw-runtime bypass supplies results; missing runners/capabilities stay incomplete with deterministic diagnostics, and WSL evidence never certifies Windows native.
