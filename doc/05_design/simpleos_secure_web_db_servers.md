<!-- codex-design -->
# Detail design: SimpleOS secure web and database servers

## Wave 1: executable and lifecycle foundation

Implement VFS-backed process execution and `ArtifactReceipt`. Add Linux and SimpleOS adapters for `ListenerProvider`, monotonic time, entropy, and key/certificate file handles. Both server entrypoints use `ServerLifecycle`; readiness is published only after recovery, capability probing, and listener bind. Drain rejects new work, awaits bounded in-flight work, flushes durable state, closes listeners, and records exit evidence.

## Wave 2: production protocols

The web entrypoint composes the existing async HTTP worker and a bounded SSR queue. `SsrRenderer` must call the canonical semantic/layout and Draw IR owner, then Engine2D; output supports HTML/semantic artifacts and deterministic pixel/readback fixtures.

Before renderer wiring, the worker/connection path must gain a typed asynchronous handler state machine: `Submitted`, `Pending`, `Completed`, `Cancelled`, `TimedOut`, and `Rejected`. Completion is delivered back to the owning worker; disconnect, timeout, overload, and drain remove the pending job exactly once. This prerequisite is tracked in `doc/08_tracking/bug/http_worker_async_handler_resume_missing_2026-08-11.md`.

Graceful drain closes new admission without cancelling accepted render jobs.
Accepted work completes or reaches its existing deadline, then its final response
is serialized with `Connection: close`. Forced shutdown is a separate transition
that cancels remaining jobs and closes the completion channel. This distinction
prevents successful requests from being discarded merely because deployment
drain began.

The DB listener implements the declared PostgreSQL v3 subset: startup, bounded SSLRequest handling, authentication, simple query, ready/error, cancellation, and terminate. Decoder returns typed errors without partial session mutation. `PgSessionDispatcher` owns session ordering and delegates database operations; ACK occurs only after the durability owner confirms commit.

The hosted listener is split into `PgWireFrontWorker` and
`PgDatabaseOwner`. Front workers own sockets and codecs and submit typed
`PgDispatchCommand(job_id, connection_id, session_id, deadline, operation)` to
a bounded mailbox. `PgDatabaseOwner` alone owns `PostgresMimicServer`; it emits
`PgDispatchCompletion` to the originating worker. Submission rejection produces
an overload error before mutation. Once a mutating command begins, cancellation
cannot report success until rollback or commit reaches a terminal durability
state. Shutdown closes admission, drains accepted commands to a deadline,
checkpoints, then closes completion queues and listeners in that order.

## Wave 3: secure transport

`SecurityErrorCode` includes invalid configuration, malformed frame, limit, timeout, peer close, no shared algorithm, downgrade, authentication, certificate, host key, decapsulation, accelerator rejection, and invariant failure. Socket edges map errors to protocol alerts/disconnects.

TLS server/client and SSH client/server use deterministic socket-free step functions. Certificate verification covers chain, signature, hostname, validity, and trust anchor. SSH policy requires modern KEX, host key, AEAD, bounded authentication, and filesystem-provisioned host keys. Fixed production test keys are forbidden.

Hybrid profiles pin algorithm name/group, lengths, ordering, hash/combiner, implementation version, and standard/draft version. `Required` rejects absence or mismatch; `Preferred` permits classical fallback only before hybrid selection and only by explicit policy. Any selected-hybrid failure is fatal. The unbacked SSH SFFI is excluded.

The TLS implementation now exposes the same `Disabled|Preferred|Required`
policy on client and server configuration. The non-runtime client path uses
fresh CSPRNG material to construct the existing hybrid-first ClientHello and
decapsulates a selected 1120-byte ServerHello share before the key schedule.
The server supplies an independent ML-KEM encapsulation seed and rejects a
missing hybrid offer in `Required` mode. `Disabled` skips ML-KEM key generation;
`Preferred` retains classical interoperability. The fd/runtime ClientHello
adapter remains classical and fails immediately when `Required` is requested.

## Wave 4: acceleration and performance

`CryptoBatchScheduler` and equivalent DB/render batch schedulers enforce maximum batch and deadline. Below crossover they select scalar/SIMD. GPU admission requires exact source/binary/profile digest, physical device identity, submission/fence/readback, oracle parity, and latency/throughput evidence. A provider mismatch quarantines it and fails a required backend or boundedly falls back for a suggested backend.

Benchmark fixtures pin hardware, workers, protocol, TLS/group, payload/schema, durability, client capacity, and versions. At least 30 paired ABBA release-native samples yield raw JSONL plus summary JSON/CSV. Linux and SimpleOS rows are never mixed.

## Current implementation checkpoint

Hosted entrypoints now exist at `src/app/simple_web_server/main.spl` and `src/app/postgres_mimic_server/main.spl`. Plaintext defaults are loopback-only; non-loopback web binding requires paired TLS credentials, and the database daemon refuses non-loopback until an owned TLS/password-authentication path exists. SimpleOS artifact catalog/staging receipts pin version, SHA-256, filesystem path, disk-image identity, and disk-image hash but deliberately remain `runnable=false`. Live promotion requires independently observed scheduler registration/start and a socket challenge bound to the same image, launch ID, filesystem path, artifact hash, and PID. A running listener does not need to exit before promotion; bounded shutdown is separate evidence.

The socket-neutral database ownership core now exists in
`postgres_mimic/dispatch_lifecycle.spl` and `database_owner.spl`: bounded front
commands are claimed and executed serially by the sole
`PostgresMimicServer` owner. The remaining concurrency step is a hosted/SimpleOS
front-worker adapter with thread-safe submission/completion channels; the
current synchronous Linux listener is not yet parallel and must not be used as
parallelism evidence.

## Failure handling

All parsers are incremental and size bounded. Timeouts/cancellation unwind owned state and zeroize secrets. Queue overflow returns an explicit overload response where safe or closes before authentication. Recovery corruption, invalid key policy, unsupported required hybrid profile, and artifact hash mismatch prevent readiness. No synthetic success may satisfy a test oracle.

The production HTTP/1 incremental parser enforces an 8192-byte request-line
bound, an 8192-byte per-field bound, and a 100-field bound while data is still
arriving. Request lines must have exactly three fields, a reviewed HTTP method,
and HTTP/1.0 or HTTP/1.1. Header field names accept RFC token ASCII only;
malformed, control, and UTF-8 names fail the connection parser instead of
being silently ignored. This closes parser-differential and unbounded-partial-
line cases without claiming live TLS/browser interoperability.
