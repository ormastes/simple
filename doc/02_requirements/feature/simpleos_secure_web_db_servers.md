<!-- codex-research -->
# Requirements: SimpleOS secure web and database servers

Selected option: **B — production foundation plus hybrid PQC negotiation**.

## Functional requirements

- **REQ-001 — Filesystem executables:** The web server and database server shall build as cached native artifacts, be staged on a SimpleOS filesystem, launch through the normal filesystem executable path, bind configured sockets, and expose version/hash receipts.
- **REQ-002 — Lifecycle and persistence:** Both servers shall support bounded startup, graceful shutdown, restart, connection draining, timeout/backpressure policy, and recovery. Committed database data shall survive server and SimpleOS restart.
- **REQ-003 — Parallel web serving:** The production web path shall use CPU-sharded asynchronous accept/event-loop workers with keep-alive, bounded queues, cancellation, and no per-request subprocess or full-tree scan.
- **REQ-004 — Server-side GUI rendering:** The production web server shall render representative Simple GUI/web scenes server-side through the canonical web semantic/layout -> `DrawIrComposition` -> Engine2D path, serve results without blocking unrelated clients, and provide semantic plus pixel/readback evidence.
- **REQ-005 — Database network service:** The database server shall expose a live bounded TCP service and a documented PostgreSQL v3 compatibility subset sufficient for the selected benchmark and Simple clients. Framing, authentication, sessions, transactions, cancellation, capability enforcement, durability-before-ACK, and overload behavior shall fail closed.
- **REQ-006 — Browser interoperability:** The Simple browser shall interoperate bidirectionally with the Simple web server over HTTP/1.1 and TLS 1.3 for declared cipher/group combinations, including certificate chain, hostname, validity, signature, and trust-anchor validation. Chromium/Firefox/OpenSSL shall serve as external oracles where supported.
- **REQ-007 — SSH interoperability:** A production pure-Simple SSH client and SimpleOS sshd shall negotiate, authenticate, execute commands, transfer representative data, and fail closed against each other and current OpenSSH in both directions. The unbacked generic SSH SFFI stack shall not count as evidence.
- **REQ-008 — Common secure cryptography:** Web and SSH services shall support documented modern authenticated encryption, key exchange, signatures/host keys, secure randomness, replay/downgrade resistance, key erasure policy, and protocol-specific transcript binding. TLS-required configurations shall never fall back to cleartext.
- **REQ-009 — Hybrid post-quantum key establishment:** TLS and SSH shall support a pinned, versioned X25519+ML-KEM-768 hybrid negotiation compatible with the applicable current draft/OpenSSH encoding. ML-KEM shall be described as key establishment, not encryption or authentication; classical authentication and AEAD remain mandatory.
- **REQ-010 — Pure-Simple ownership:** Protocol state machines, negotiation, transcript/key schedule orchestration, ML-KEM/X25519 algorithms, and server policy shall be implemented in `.spl`. Runtime, OS, and physical-device boundaries shall be explicitly inventoried and shall not be represented as pure-Simple algorithm code.
- **REQ-011 — Accelerator admission:** SIMD/GPU providers may accelerate only coarse, validated batches such as hybrid KEM, compression, database scans/vector operations, or render tiles. Each provider shall have CPU correctness parity, explicit capability admission, bounded fallback, and no GPU dependency for ordinary small request parsing.
- **REQ-012 — Modern SSpec coverage:** Executable modern SSpec scenarios shall cover every requirement, primary operator/user flows, edge/error/security paths, SimpleOS QEMU lifecycle, live protocols, SSR captures, interoperability, and benchmark receipts. No placeholder passes or unresolved oracles may satisfy a requirement.
- **REQ-013 — Honest incumbent comparison:** Reproducible harnesses shall compare matched workloads with nginx/h2load, PostgreSQL/pgbench, OpenSSH, and at least one independent cryptographic implementation. Unsupported protocol features shall be reported, not emulated as false parity.

## Scope boundaries

- PostgreSQL compatibility is the explicit tested subset, not full PostgreSQL feature parity.
- GPUDirect-class networking is an experimental Linux-host lane and shall not be claimed as SimpleOS support without physical SimpleOS evidence.
- Post-quantum signatures are outside this selection unless separately required; hybrid KEM does not replace certificate or SSH host-key authentication.

