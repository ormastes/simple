<!-- codex-design -->
# Architecture: SimpleOS secure web and database servers

## Decision

Use existing production owners and compose them through narrow virtual capsules. The web service extends `src/lib/nogc_async_mut/http_server/`; it does not promote either synchronous UI web server. The database service adds bounded TCP/pgwire transport around `PostgresMimicServer` while `PureDatabase` remains the sole SQL/durability owner. SimpleOS gains real VFS-backed executable load/launch/exit semantics; rootfs injection is staging, not execution proof.

## Capsules and public contracts

- `server_lifecycle`: `ServerLifecycle.prepare/start/begin_drain/await_drained/stop/receipt` and `ArtifactReceipt(version, content_hash, config_hash, filesystem_path, boot_id)`.
- `bounded_runtime`: `ListenerProvider.bind/accept/close`, `BoundedWorkQueue<T>.try_submit/cancel/drain/depth`, deadline and size policies.
- `observability`: `ServerMetricsSink.count/observe_ms/gauge`, woven only at lifecycle and phase boundaries.
- `secure_transport`: socket-free protocol state machines over `SecureTransportIo.recv_bounded/send_all/close`, `SecureEntropy.fill`, and typed `SecurityError`.
- `accelerator_admission`: `AcceleratorProvider.capability/admit/execute_batch/fallback_receipt`; CPU is mandatory.
- DB-private: `PgWireCodec`, `PgSessionDispatcher`, `DatabaseDurability`.
- SSR-private: `SsrRenderer.render_composition/render_artifact` and `RenderCache.lookup/store/invalidate_revision`.

Protocol state remains private to its capsule. Common modules own only stable policies, errors, secret lifetime, capability interfaces, and receipts. Protocol modules may not declare socket, filesystem, process, entropy, clock, or device externs.

## Startup and hot paths

Startup validates configuration and artifact identity, loads key/certificate handles, recovers the database, loads bounded cache metadata, probes capabilities once, binds listeners, then publishes readiness. It performs no full-tree scan, source-file read, or subprocess per request.

Web hot path:

`SO_REUSEPORT accept shard -> IO completion -> bounded parser -> route -> bounded SSR queue -> web semantic/layout -> DrawIrComposition -> Engine2D -> response`.

Extend the worker path; do not add another accept loop. Cache immutable layout/render artifacts by content, theme, font, viewport, renderer ABI, and backend revision. Explicitly invalidate on any revision change. A long render yields or is bounded and cannot block unrelated connections.

DB hot path:

`accept shard -> bounded pgwire decoder -> authenticated session -> transaction dispatcher -> PureDatabase -> durability-before-ACK -> encoder`.

Each accept shard owns its socket, incremental decoder, authentication state,
response encoder, deadlines, and output buffer. It may parse independent client
input concurrently, but it must not share or copy a mutable
`PostgresMimicServer`/`PureDatabase` across threads. Decoded commands enter a
bounded typed mailbox owned by one database dispatcher. Producers reserve
mailbox capacity with atomic compare/exchange before publishing; a close race
rolls the reservation back, so the configured bound remains true under
concurrent producers. The dispatcher assigns
session IDs and is the sole mutator of session, transaction, storage, and
durability state. Responses return through per-shard bounded completion queues;
disconnect and timeout cancel only commands that have not entered a transaction
mutation. Queue saturation fails before database mutation.

This single-owner baseline makes connection parsing and encoding parallel while
preserving per-session and transaction ordering. Read-only MVCC snapshots may
later be sharded only when `PureDatabase` exposes an immutable snapshot handle
with a pinned generation. GPU scans consume only such admitted immutable
snapshots and return candidate rows to the database owner for scalar validation.
Bound frame size, sessions, queued queries, transaction duration, result bytes,
completion depth, and drain time.

## Security architecture

TLS states are `AwaitClientHello`, `PreparingFlight`, `AwaitClientFinished`, `Established`, `Closing`, `Closed`. SSH client/server states cover banner, KEXINIT, hybrid reply, NEWKEYS, service, auth, channels, and close. Invalid transitions fail closed.

`CryptoPolicy` pins TLS-required behavior, hybrid `Disabled|Preferred|Required`, allowed AEAD/signature algorithms, handshake limits, and rekey thresholds. The selected hybrid profile pins FIPS 203 ML-KEM-768 plus the applicable versioned X25519MLKEM768 wire encoding; exact hello/KEXINIT bytes and selected group are transcript-bound. ML-KEM does not authenticate. Certificate or SSH host-key signatures and AEAD remain mandatory.

Secret material uses owned `SecretBytes` with zeroization on transition, error, and close. Public errors never include secrets or attacker-controlled raw fields. Decapsulation failures are uniform. TLS-required listeners have no plaintext branch; unknown/mismatched SSH host keys never prompt-and-continue.

## SimpleOS execution boundary

REQ-001 is blocked until the VFS can open a staged executable, validate its format/recipe and hash, map it into an isolated process address space, create process/thread state, transfer arguments/config handles, schedule it, expose exit status, and reclaim resources. QEMU proof must launch through this path, not call a linked-in server function.

`FsExecReceipt.pid` is observational data, not process authority. Runnable
promotion additionally requires `process_registered=true`, which only the
scheduler/task owner may issue after registration. Current synchronous ring-3
handoffs intentionally return unregistered receipts even when they preserve an
exit code; they cannot satisfy server lifecycle evidence.

## Acceleration

CPU worker sharding precedes GPU work. Never offload ordinary request parsing, record AEAD, or individual small queries. Batch only hybrid KEM, compression, admitted scans/vector operations, or render tiles. Physical-device admission requires compiled/submitted/fence/readback receipts, oracle parity, pinned digests/device identity, a measured throughput crossover, and p99 no more than 1.2x CPU. Quarantine on mismatch.

## Observability and budgets

Record startup, accept, parse, queue, handler, render, plan, execute, commit, crypto, send, drain, reject, cancel, cache, and accelerator-fallback metrics. Metrics contain phase/algorithm/backend/error class, never keys, passwords, transcripts, ciphertext, or private certificate data.

Initial budgets are requirement gates: bounded startup and drain; zero unexpected protocol errors; Linux release-native p95 <=2x matched incumbents; all queue/frame/session/render/transaction/handshake limits configured and observable. Concrete numeric size/time defaults are finalized per platform during implementation and preregistered before benchmarks.
