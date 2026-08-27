# Parallel agent plan: SimpleOS secure web/DB servers

## Shared contracts before parallel implementation

The merge owner freezes `ServerLifecycle`, `ListenerProvider`, `BoundedWorkQueue<T>`, `ServerMetricsSink`, `ArtifactReceipt`, `SecureTransportIo`, `HybridKemProvider`, `PgWireCodec`, `PgSessionDispatcher`, `SsrRenderer`, `RenderCache`, and `AcceleratorProvider`, plus the step/helper/checker names in the system-test plan. No lane may claim support from importability, static inspection, interpreter timing, or simulated GPU evidence.

## Waves

1. **Evidence baseline** (complete): web hot-path/SSR audit; DB/pgwire audit; SimpleOS packaging/network capability audit; TLS/SSH/PQC threat-model and oracle audit; benchmark reproducibility audit.
2. **CPU production foundation** (parallel after contracts): VFS process-exec/lifecycle lane; async SSR worker lane; DB TCP/pgwire lane; TLS 1.3/browser lane; pure-Simple SSH client+sshd lane.
3. **Modern SSpec** (parallel): live web+SSR+browser scenarios; DB network/durability/restart scenarios; OpenSSL/Chromium/Firefox matrix; OpenSSH both directions; hostile framing/slowloris/auth failures; generated manuals.
4. **Performance** (parallel): nginx+h2load; PostgreSQL+pgbench; OpenSSH; scalar/SIMD crypto; SSR render/live. One independent reviewer validates matched semantics and rejects client bottlenecks.
5. **PQC and acceleration** (gated): wire pinned hybrid negotiation; then coarse GPU lanes for crypto, compression, DB operators, and render tiles. Admit only with correctness parity, physical-device receipts, and crossover evidence.

## Ownership

- Sidecar lanes: lower-model discovery is allowed for bounded inventories only; current design sidecars were normal-model read-only lanes. Future lower-model implementation sidecars must target frozen interfaces and fail-fast helpers.
- Merge owner: `/root` owns shared interfaces, integration, and requirement traceability.
- Final reviewer: a different highest-capability agent runs requirement traceability, security, SimpleOS, SSpec-vacuity, and benchmark-honesty gates.
- Concurrent dirty files remain owned by their current sessions; new work uses isolated feature lanes and must not absorb unrelated changes.
