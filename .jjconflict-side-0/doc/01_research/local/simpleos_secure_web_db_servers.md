<!-- codex-research -->
# SimpleOS secure web and database servers — local research

## Current evidence

- `src/lib/nogc_async_mut/http_server/server.spl` has a per-CPU worker/EventLoop/IoDriver design with `SO_REUSEPORT`, keep-alive, routing, compression, cache, and sendfile. `src/lib/web/http/server.spl` and `src/app/ui.web/server.spl` are synchronous/non-production alternatives; the latter performs real server-side HTML rendering but one WebSocket can block other clients.
- `src/lib/nogc_sync_mut/database/server/server.spl` has fail-closed framing, capabilities, transactions, optimistic conflicts, and durability-before-ACK, but only `MemoryTransport`. `src/app/postgres_mimic_server/main.spl` is a one-query CLI, not a TCP/pgwire daemon.
- SimpleOS can resolve and spawn filesystem ELF/SMF programs through `src/os/apps/shell/path_search.spl` and `exec.spl`. Existing disk/QEMU evidence stages other apps, not production web/DB servers that bind, persist, restart, and answer clients.
- GPU web/DB offload contracts and rendering acceleration exist, but they are not wired to either server hot path. Small request parsing is a poor GPU target; coarse batches (crypto, compression, scans/vector operations, rendering) are plausible only above measured crossover points.
- Modern SSpec coverage exists for DB semantics and browser/rendering, but DB tests use memory transport and rendering tests do not prove live request -> SSR -> browser display on SimpleOS.
- The nginx baseline records about 199.5k RPS at 1 KiB; the Simple result is pending. The PostgreSQL comparison reports the live server unavailable and embedded Simple missing four of five CRUD targets.

## Security and interoperability

- Pure-Simple crypto includes AES-GCM, ChaCha20-Poly1305, Ed25519, X25519, SHA-2, HKDF, HMAC, X.509, ML-KEM, and X25519+ML-KEM-768 orchestration. Some hot paths still use runtime externs, so “pure Simple” must distinguish algorithm/orchestration from runtime/device boundaries.
- `src/lib/nogc_sync_mut/http_server/tls_server.spl` is explicitly incomplete and can return cleartext passthrough; production HTTPS is not proven. Browser TLS delegates transport/crypto to the hosted runtime.
- The generic SSH client SFFI has unresolved runtime symbols and is documented to fail. Existing sshd/static tests do not prove live OpenSSH interoperability; the RV64 live lane remains blocked at key exchange.
- ML-KEM KATs and accelerator providers exist, but X25519MLKEM768 is not wired into live TLS or SSH. Current interpreted hybrid exchange performance is not production evidence. ML-KEM is key establishment, not encryption or authentication.

## Required proof gaps

1. Cached native server artifacts staged on a SimpleOS filesystem, launched in QEMU, bound to sockets, interoperable, persistent, restartable, and measured.
2. Async web SSR and a real DB TCP/pgwire transport with bounded backpressure, cancellation, timeouts, worker ownership, and graceful shutdown.
3. Browser<->webserver TLS 1.3 and SSH client/server<->OpenSSH live matrices, including hostile fragmentation and authentication failures.
4. Native release benchmarks against nginx/PostgreSQL/OpenSSH and independent crypto implementations; median/p95/p99, errors, CPU, RSS, and reproducible receipts.
5. Physical-GPU receipts and batch crossover curves; CPU fallback must remain correct and usually preferred for small requests.

