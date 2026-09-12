# G4 DB/context/service test handoff (Luna)

Status: component tests added against the frozen production owners; physical
service/namespace authority remains `MissingEvidence` until host wiring is
admitted.

## Frozen interfaces and oracles

| Interface | What the tests prove |
|---|---|
| `PureDatabase.memory/open/open_deferred`, transaction and query methods | Real row/PK/MVCC/FTS behavior, rollback and persistence refusal preserve the prior image; stale disk identity is rejected. |
| `ContextStoreV1.memory/open/replace_all/put/get_exact/query_literal/close` | Atomic replacement, duplicate/invalid identity rejection, stable ordering, literal Unicode search, id allocation, and close lifecycle. |
| `DbServerCapsule.new(SdnDatabase, CapabilityTable)` | Service is backed by `SdnDatabase`, not `PureDatabase`; policy, principal binding, exact retry/divergent commit ID, receipt bounds, and transport limits are tested at the server boundary. |
| selected-head reopen encode/decode/validate | Exact operation-to-journal binding, canonical bounds, stale writer/head status precedence, and diagnostic-only output. |
| GC `begin_authority_v1(contributions)` | All count/flag/stale-field negatives and a complete copied request still refuse without host issuance. |

## Executable coverage

`test/02_integration/app/context_store_v1_component_spec.spl` exercises the
production ContextStore owner with real assertions for round-trip/query,
invalid replacement rollback, duplicate identity atomicity, and idempotent
close. Existing unit specs in `test/01_unit/app/io/context_store_v1_contract_spec.spl`
cover Unicode literals, ordering, zero-ID allocation, max-ID overflow, and
closed-state errors.

The selected-head, GC, and service rows remain in their owner manifests until
the corresponding implementation hunk is present. A missing host row must use
`g4_require_physical_evidence_v1(row)` and fail with
`MissingEvidence: <row>`; no synthetic handle or copied DTO is a pass.

## Sol review guide

Verify the test calls production owners, keeps `SdnDatabase` and
`PureDatabase` distinct, checks exact row/value/order, and preserves bytes on
every refusal. Review each status-precedence flag and canonical boundary
independently; source scans and load-only checks do not count as execution.

## Astra final review guide

Review the isolated manifest and exact source/runtime/spec hashes. Require
>=95% measured branches per executable component, 100% on authority negatives,
rollback, stale identity, and GC refusal decisions. Keep physical namespace,
fsync/rename, crash/reopen, and host-GC evidence unqualified until the actual
host receipt and independent-process artifact exist.
