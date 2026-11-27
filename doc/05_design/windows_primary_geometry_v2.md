# Windows primary terminal geometry V2

Status: implementation source, AWAITING_VERIFICATION. No Windows native execution, build, test, SPipe generation, latency, or fault qualification was performed. The exhausted native campaign remains closed. This feature does not complete Caret or the full orchestrator acceptance plan.

## Endpoint and ownership

The installed Docker profile pins Engine API **1.48**. Its primary-container operation is `POST /v1.48/containers/{id}/resize?h=<rows>&w=<columns>`. Docker documents status 200 as success, 404 for an absent container, and 500 for a resize failure. This is distinct from exec resize. A 200 response acknowledges the API request; it does not independently observe the guest terminal dimensions. Source: [official Docker Engine API v1.48](https://docs.docker.com/reference/api/engine/version/v1.48/#tag/Container/operation/ContainerResize).

The common `terminal_primary_geometry_v2` port dispatches the retained Linux V1 exchange or an actual Windows geometry owner. The Windows leaf never creates a PTY, process, Job, second terminal reader, or synthetic Linux identity. It opens a separate native Engine pipe for a single bounded HTTP request; the adopted attach pipe retains its independent Input binding.

The Host service resolves the actual parent execution packet and observation from its existing protected journal, checks the actual parent/helper are executing, retains the original connection plan digest and rechecks it against both the supplied current connection and actual session before every scan/effect, and uses its current protected Docker policy. The adapter checks retained exact native-container authority, request scope, provider continuity and native host observations without synchronous Docker CLI calls. The provider's bounded read-only probe checks Engine identity, exact container ID, managed labels, running state and TTY. The resize connection must match the observed protected endpoint. Its inspection age is bounded from the actual monotonic probe start, not completion/publication.

## Authorization and request history

Geometry has its own issuer lease. The V5 consumer checks the canonical issuer and exact adopted target before begin and every step. The common/native owner also checks the exact request, session identity, adoption epoch/incarnation, Geometry kind, principal, nonce, revision and deadline. The native controlled write enforces expiry at the actual write boundary. Revoke, detach, target drift and cleanup cancel only this geometry exchange.

Durable attempts use immutable pairs under the **same journal writer**: `primary-geometry-v2/<binding-uid-hash>/<slot>.attempt.sdn` and `<slot>.receipt.sdn`. Existing native replacement restrictions remain unchanged. One service turn reads at most one pair. Known completions may return an opaque process-local prefix cursor bound to the same actual store/lease and exact terminal readback; restart has no such cursor. The scan refuses corrupt records, orphan receipts, gaps that contradict a receipt, and exhaustion of the fixed 4096-slot bound. It never reuses a slot or treats an unreadable file as absent.

The complete request digest binds the target, session identity through the record, principal, nonce digest, revision, issue/expiry time, attempt sequence, dimensions and full HTTP wire digest. A fresh random publication identity distinguishes this process's own uncertain publication from an identical request reserved elsewhere. A new attempt is published no-replace before the first provider step. Exact duplicate requests return retained evidence only. Known completion permits the next sequence; a new lease starts at sequence one. Pending or Unknown history blocks new effects across revision and session changes.

There is no restart reconstruction of a pipe. A reserved attempt without its terminal receipt is Unknown after process loss and blocks further geometry admission. Current engine size cannot resolve that ambiguity. The service retains the actual native exchange until cleanup finishes, then publishes immutable terminal evidence. Publication errors retain the task for exact retry. A failed reservation publication permits cleanup/reconciliation only, never a resize write.

## Bounded native exchange

Constructor admission allocates only a canonical same-thread registry slot; it performs no Engine connection or session poll. Subsequent turns drive the read-only probe, connect, endpoint check, Geometry binding/install, one full controlled request write, completion polling, bounded HTTP parsing and cleanup. The wire is bounded below the native 65536-byte write limit. A queued write is polled; a partial or uncertain completion is never retransmitted. Lost, malformed or ambiguous responses remain Unknown. Acknowledgement survives cleanup failure, and no task is discarded while native cleanup or receipt publication remains pending.

Nonreused native slots prevent copied owners from rewinding the effect. Windows registry access requires the actual native thread guard. The Host task stores no separate capacity ledger or journal projection; its retained store reference is used only to correlate the caller's current writer.

## Evidence and limitations

Authored tests exercise actual production wire/reducer checks and immutable records through the genuine shared journal fixture. The journal fixture is Linux-backed and explicitly scripted where it constructs a Windows provider. These tests do not qualify Windows ACLs, native pipes, guest resize, V5 scheduling latency or crash fault injection. All are NOT_RUN.

Native acceptance requires an actual protected, enrolled Windows service, a genuinely created running TTY container, a signed admitted and adopted primary connection, and separate live Input/Geometry issuers. Missing setup is a prerequisite failure, not an unsupported-host pass. The acceptance inventory records expiry/revoke, wrong identity/non-TTY, Input independence, changed payload, partial/lost writes, peer drift, cleanup failure, restart uncertainty and observed guest dimensions separately. One real configured-service SSpec now drives authenticated V5 resolve/issue/resize/observe/replay/revoke and actual independent Input write against an externally provisioned dedicated binding. It is AUTHORED_NOT_RUN. Guest-size observation and native fault injection remain NOT_COVERED until an admitted qualification campaign.

The HTTP probe, metadata verification and record IO are bounded by source contracts. Whole-service responsiveness, allocation behavior and p95 latency remain unqualified. Historical record inspection is incremental, not a synchronous directory walk. Process-crash evidence is the intended storage profile; no new power-loss durability claim is made.
