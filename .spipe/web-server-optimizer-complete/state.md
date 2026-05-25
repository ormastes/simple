# SStack State: web-server-optimizer-complete

## User Request
> Make simple web server complete. Perf equal to nginx specially for static HTML, HTTP/2 multi-content download, HTTP/3 UDP. Improve optimizer plugin to improve simple optimization when C-generated binary is slower than Simple-generated, and make it general to optimize other cases also.

## Task Type
feature

## Refined Goal
> Two parallel workstreams to make Simple's web server production-grade and the compiler optimizer plugin general-purpose:
>
> **Workstream A — Web Server Completion (nginx-class)**
> 1. HTTP/2 server-side stream multiplexing — upgrade existing h2 frame/parser/writer into a full H2 server connection handler that multiplexes concurrent streams over a single TLS connection (HPACK, flow control, SETTINGS, GOAWAY)
> 2. HTTP/3 server over QUIC/UDP — build QUIC transport layer (UDP datagrams, connection IDs, Initial/Handshake/1-RTT packets, loss detection, congestion control) and wire existing h3_frame + qpack into a usable H3 server endpoint
> 3. Static file serving at nginx-level throughput — sendfile/zero-copy dispatch (already in net capability tiers), pre-compressed file cache (gzip+brotli), mmap-backed responses, ETag/Last-Modified cache validation, Range requests
> 4. Unified server entry point — single `HttpServer` that negotiates ALPN → H1/H2/H3 and delegates to protocol-specific connection handlers
>
> **Workstream B — Compiler Optimizer Plugin Generalization**
> 1. Perf-comparison harness — automated benchmark that compiles the same function via Simple codegen vs. C codegen (Cranelift vs. clang), identifies cases where Simple-gen is slower, and emits optimization hints
> 2. General optimization rule engine — extend the existing MIR dynamic pass manifest (`optimizer_manifest.spl`) to support user-defined pattern→rewrite rules (not just built-in passes), with cost-model scoring
> 3. C-parity optimization passes — specific MIR passes targeting the top Simple-slower-than-C patterns: redundant bounds checks, unnecessary copies, missed SIMD vectorization, suboptimal register allocation hints
> 4. `bin/simple optimize` CLI — surface for running the optimizer tool interactively: profile, suggest, apply passes

## Acceptance Criteria

### Workstream A — Web Server
- [ ] AC-1: H2 server multiplexing — async H2 connection handler with concurrent stream dispatch, HPACK encode/decode, per-stream flow control, SETTINGS/GOAWAY frames; spec covers 3+ concurrent streams
- [ ] AC-2: H3 server over QUIC — QUIC transport with UDP send/recv, connection ID routing, Initial+Handshake+1-RTT packet types, loss detection timer, congestion window; H3 frames dispatched over QUIC streams; spec covers connection setup + single request
- [ ] AC-3: Static file perf — sendfile zero-copy path used when capability tier supports it, pre-compressed cache (serve .gz/.br if Accept-Encoding matches), mmap fallback, ETag + Range support; benchmark fixture shows throughput within 2x of nginx for 1KB/10KB/100KB files
- [ ] AC-4: Unified server — single `HttpServer.listen()` entry that ALPN-negotiates h1/h2/h3, routes to protocol handler; spec covers ALPN dispatch
- [ ] AC-5: All server specs pass (`bin/simple test test/unit/lib/nogc_async_mut/http_server/`)

### Workstream B — Optimizer
- [ ] AC-6: Perf-comparison harness — `bin/simple optimize --compare` compiles a sample function via Simple codegen + C codegen, reports wall-time and instruction counts, flags regressions
- [ ] AC-7: General rule engine — extend MIR optimizer manifest to accept pattern→rewrite rules in `.opt.json` files; rules can match MIR node patterns and emit replacement nodes; at least 3 example rules
- [ ] AC-8: C-parity passes — at least 3 new MIR optimization passes targeting: (a) redundant bounds-check elision, (b) copy-on-write to move promotion, (c) loop-invariant code motion; each with a before/after spec
- [ ] AC-9: CLI surface — `bin/simple optimize <file.spl>` runs analysis, prints suggestions with expected speedup; `--apply` flag auto-applies safe passes
- [ ] AC-10: All optimizer specs pass (`bin/simple test test/compiler/mir_opt/`)

## Cooperative Providers
- Codex: unavailable
- Gemini: unavailable

## Phase Checklist
- [x] 1-dev (Developer Lead) — 2026-05-25
- [x] 2-research (Analyst) — 2026-05-25
- [x] 3-arch (Architect) — 2026-05-25
- [ ] 4-spec (QA Lead)
- [ ] 5-implement (Engineer)
- [ ] 6-refactor (Tech Lead)
- [ ] 7-verify (QA)
- [ ] 8-ship (Release Mgr)

## Agent Teams

### Team A — Web Server (Phases 2-8 parallelized)
- **A1**: H2 server multiplexing (AC-1)
- **A2**: H3/QUIC server (AC-2)
- **A3**: Static file perf + benchmark (AC-3)
- **A4**: Unified server entry + ALPN (AC-4)

### Team B — Optimizer (Phases 2-8 parallelized)
- **B1**: Perf-comparison harness (AC-6)
- **B2**: General rule engine (AC-7)
- **B3**: C-parity MIR passes (AC-8)
- **B4**: CLI surface (AC-9)

## Phase Outputs

### 1-dev
Refined two workstreams with 10 ACs. Existing infrastructure:
- HTTP/2 protocol layer exists (h2_frame, h2_parser, h2_preface, h2_writer) — needs server-side multiplexing
- HTTP/3 protocol layer exists (h3_frame, h3_conn, h3_stream, qpack_*) — needs QUIC transport
- Async HTTP server exists with static_file.spl, compression.spl, worker.spl — needs sendfile/zero-copy perf path
- Net acceleration landed: TCP state machine, sendfile/zero-copy capability tiers, DMA buffers
- TLS layer exists (tls_handshake, tls_io, tls_common) — needs ALPN negotiation
- MIR optimizer has dynamic pass manifest with ABI contract — needs generalized rule engine
- Backend optimizer has PassRegistry with data-driven pass selection — needs C-parity passes
- Perf optimizer tool exists as skeleton — needs comparison harness

### 2-research
Research complete (2026-05-25). Full reports in:
- `research_web_server.md` — Workstream A findings
- `research_optimizer.md` — Workstream B findings

**Key findings — Web Server:**
- H2 wire framing complete (all 10 frame types). Missing: HPACK, connection state machine, stream lifecycle, flow control, SETTINGS exchange
- H3 frame layer + QPACK static-table encoder/decoder complete. QUIC transport entirely absent — no packet format, no QUIC-TLS. AsyncUdpSocket exists but is sync-wrapper facade
- Static file handler has sendfile zero-copy + pre-compressed LRU cache + Last-Modified. Missing: ETag/If-None-Match, Range/206, nginx benchmark
- TLS handshake parses ClientHello but doesn't dispatch on ALPN extension (type 0x0010). Worker is H1-only
- TLS 1.3 absent — blocker for QUIC-TLS (AC-2)
- HPACK can reuse QPACK base (same RFC 7541 foundation)

**Key findings — Optimizer:**
- C++ backend functional: `CCodegenAdapter.compile_module()` emits C++20 via `MirToC.translate_module()`. No comparison orchestrator exists
- 25+ MIR passes registered. `BoundsCheckElimination`, `CopyPropagation`, `LoopInvariantMotion` are registered but stubs (empty transform bodies)
- `ReadAheadHoist` implements LICM detection — reuse path for `LoopInvariantMotion`
- `CLibParityHotspot` has 10 rules in 3 families. Rule engine types exist (Rule, MatchHit, OptimizationRuleProvider)
- Dynamic manifest loads `.sdn/.json` with `load_manifest_v1()` → `DynamicPassRegistry`. Dispatch not yet wired in `run_pass_on_module`
- No `optimize` CLI subcommand. CLI routing via `src/app/cli/`

### 3-arch
<pending>

### 4-spec
<pending>

### 5-implement
<pending>

### 6-refactor
<pending>

### 7-verify
<pending>

### 8-ship
<pending>
