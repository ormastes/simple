# Simple vs Rust — Debug and Logging Parity Analysis

**Date:** 2026-07-28
**Sibling audits:** `simple_vs_rust_mission_critical_2026-07-27.md`,
`simple_vs_rust_safety_property_audit_2026-07-28.md`
**Baseline:** practical Rust — rustc/Cargo debug-info controls (DWARF levels, split
debug info, frame pointers, unwind tables), structured diagnostics, `log`/`tracing`
ecosystem, OpenTelemetry, tokio-console, sanitizers, Miri.
**Claims below are the incoming analysis; §Verification carries repo ground truth.**

## RAG verdict

| Dimension | RAG | Verdict |
|---|---|---|
| Overall debug/observability architecture | 🟠 | Components exist as separate systems without a common identity + evidence model |
| Native source-level debugging | 🔴 | End-to-end source provenance + real backend debug-info emission are the blockers |
| Compiler diagnostics | 🟠 | Rust-hosted compiler rich; self-hosted model behind it (parity drift in-repo) |
| Logging | 🟠 | Strong embedded/no-alloc foundations; incomplete structured dispatch + correlation |
| Runtime/distributed tracing | 🟠 | Trace IDs, spans, HTTP propagation, semantic replay exist — isolated implementations |
| Req/design/test traceability | 🟢/🟠 | Strong static traceability; not connected to symbols/builds/deployments/logs/crashes |
| Crash/postmortem | 🟠/🔴 | Panic capture in Rust-hosted CLI; no native cross-platform crash bundle + symbol service |
| Async/task debugging | 🔴 | No unified task/waker/queue/actor observability (tokio-console class) |
| Sanitizers + UB checking | 🔴 | Instrumentation exists; not first-class compiler/test profiles |

**Core diagnosis:** the problem is no longer missing features — it is the absence of ONE
diagnostic/provenance/logging/tracing/crash architecture joining them. Two traceability
kinds must stay separate but share stable IDs: engineering lifecycle (REQ → design →
symbol → test → build → deployment → incident) and runtime causal (request → task →
actor → queue → FFI → device → error → log → crash).

## Claimed defects (pre-verification)

1. **Diagnostic drift:** Simple-native diagnostic (severity/code/span/labels/notes/help)
   vs richer Rust-hosted model (machine-applicable fixes, replacements, applicability,
   JSON). Fix: one versioned `DiagnosticV1` schema (SDN-generated) → Rust/Simple/JSON/
   LSP/SARIF/CLI renderers; no handwritten parallel types.
2. **Source provenance (largest compiler defect):** `Span.merge()` resets file to ""
   and length 0; MIR builders emit `span: nil` for constants/copies/moves/arith/refs/
   loads/stores. Breaks debugger line mapping, variable locations, optimized
   attribution, replay locations, coverage, profiling. Fix: `SourceAnchor` (revision,
   file_id, syntax_id, symbol_id, byte range, expansion) + `OriginSet` (primary +
   related + kind: Authored/Desugared/MacroExpanded/AopGenerated/Specialized/Inlined/
   OptimizerSynthesized) mandatory on every HIR/MIR op; nil ≠ "generated"; compiler
   verifier rejects user-originated MIR without origin. File/line become a rendered
   view of stable anchors (fits the SymbolId md-link work).
3. **LLVM debug flag is a promise, not an implementation:** `debug_info` field +
   `with_debug_info()` exist; `compile_module` never consults them, emits no debug
   metadata. Fix: backend-neutral **DebugIR** (files, CUs, scopes, params, locals,
   line maps, inline sites, async suspension points, types incl. enums/discriminants/
   closures/generics, value locations) → DWARF5 / CodeView-PDB / dSYM / WASM-DWARF
   emitters. CLI: `--debug-info=none|line-tables|limited|full`,
   `--split-debug-info=off|packed|unpacked`, `--frame-pointers`, `--unwind-tables`,
   `--debug-optimized`; unsupported level = explicit error, never silent.
4. **Debugger stack is adapter scaffolding:** DAP disables function bps, exception
   info, logpoints, loaded sources, memory read, disassembly, cancellation; GDB
   adapter discards condition/hit/log fields; GDB/MI transport is shell+FIFO+grep with
   fixed timeouts. Fix: real subprocess pipes, streaming MI parser, token→request
   table, async-record handling, capabilities generated from adapter+target+artifact.
   **Debug metadata before more debugger UI.**
5. **Logging gap:** the no-alloc ring + filters + drop accounting are good (keep!);
   but `_dispatch_to_backends()` doesn't carry text messages into backends outside
   panic mode, and the compact record has no build/source/thread/task/actor/trace/span
   identity, typed fields, error chains, redaction, sampling flags. Fix: two-tier
   records — `FastEventRecord` (48-64B, ISR-safe: seq, mono-time, callsite_id,
   context_id, p0, p1, level, flags) + hosted `EventV1` enrichment on drain;
   `CallsiteId` resolves via build-time metadata table (template, field names/types,
   anchor, symbol, level, privacy).
6. **Tracing isolated:** web TraceContext (128-bit trace IDs, W3C traceparent, spans)
   exporter is an in-memory JSON array — no OTLP transport; not shared with std.log,
   scheduler, actors, SFFI, GPU queues, drivers, crash, replay.
7. **Semantic replay wired wrong:** event format rich, but MIR injection emits
   zero-arg trace calls with span:nil — feature model ahead of integration.
8. **Crash:** panic capture exists (Rust-hosted CLI); native signal capture
   (SIGSEGV/SIGABRT), Windows SEH/minidump, macOS artifacts, bare-metal trap capture,
   offline `simple symbolize`, build-id-keyed symbol bundles = missing. Target:
   `CrashBundleV1` (build id, modules, signal, fault addr, registers, thread + task/
   actor stacks, active trace/span, recent ring records, drop counters, config hash).

## Architecture: one Debug and Evidence Spine

```
SourceRevisionId─FileId─SyntaxId─SymbolId─OriginSet
        AST → HIR → MIR → Optimized MIR
          ├─ DiagnosticV1 → CLI/JSON/LSP/SARIF
          └─ DebugIR → DWARF/PDB/dSYM/WASM  → BuildManifest
BuildId─ExecutionId─TraceId─SpanId─TaskId─ActorId  (ObserveContext)
          ├─ sampled telemetry: FastEventRecord ring → subscribers/exporters (console/JSONL/file/syslog/ETW/OTLP/crash-ring)
          └─ lossless replay: SemanticEvent ring → .sst (separate reliability rules; loss must be reported)
Traceability graph: REQ/NFR → Design → Symbol → Test → Coverage → Build → Deployment → Trace/Log/Crash
```

Telemetry may sample/drop (accounted); replay must be deterministic or loudly lossy.
Never one storage policy for both.

## Priorities

**P0 (debugging parity):** 1 source provenance (fix Span.merge, SourceAnchor/OriginSet,
verifier) · 2 real debug metadata per production backend (line tables → full) ·
3 DiagnosticV1 canonical schema + `simple explain E####` · 4 real DAP/GDB/LLDB
(transport + honest capabilities + pretty-printers + optimized-out handling +
bare-metal RISC-V/ARM/SimpleOS cross-debug) · 5 ObserveContext propagation (calls,
spawn/await/resume, actors, queues, HTTP/RPC, SFFI, processes, GPU, drivers) ·
6 native crash-bundle pipeline + symbolizer.

**P1 (observability parity):** 7 subscriber/layer architecture (sinks: console, binary
ring, JSONL, rotating file, syslog/journald, ETW, os_log, semihosting/serial/JTAG,
OTLP, test-capture, crash-ring; policies: filters, batching, retry, backpressure,
overflow, sampling, rate limits, redaction, secret detection, cardinality caps, runtime
reload, flush deadlines) · 8 async console (task states, wake/poll counts, busy/idle,
longest poll, queue depths, mailbox depth, supervisor restarts, deadlock candidates,
blocking-in-async) · 9 sanitizer + checked-interpreter profiles
(`simple test --sanitize=address|thread|undefined|memory|leak`,
`--interpret-check=provenance` Miri-class) · 10 BuildManifest + symbol/artifact
lifecycle (old binary → exact old source).

**P2 (exceed typical Rust):** 11 graph-based traceability queries (REQ→symbols→tests→
builds→traces→crashes; requirement-without-system-test detection) · 12 deterministic
replay in the debugger (reverse-step over semantic events, ownership history, message
causality, first-divergence, DAP attach).

## System-test gates (no mocks for system claims)

Real llvm-dwarfdump/readelf/pdbutil inspection; real GDB and LLDB breakpoint/step/
inspect sessions (also at -O2 with inlining + optimized-out vars); async break inside
resumed coroutine showing logical parents; every advertised DAP capability exercised
against a live process; crash bundles from real abort/invalid-access/stack-overflow/
watchdog + offline symbolization; one trace ID preserved HTTP→task→actor→FFI→device;
ring overflow drop-accounting integrity; same invalid source through both compilers →
canonical JSON diff; sanitizers on real instrumented binaries; traceability query
REQ→symbol→test→build→trace→crash. Mocks stay for parser/serializer units only.

## Implementation order

1 SourceAnchor+OriginSet → 2 DiagnosticV1+DebugIR schemas → 3 LLVM DWARF end-to-end →
4 BuildId+symbol bundle+symbolizer → 5 real GDB/MI+DAP conformance → 6 ObserveContext+
EventV1+SpanV1 → 7 bridge std.log/web-tracing/SReplay/scheduler/crash → 8 export
layers+async console → 9 sanitizer+checked-interp profiles → 10 traceability graph.
Milestone name: **Debug and Evidence Spine v1** — not another standalone subsystem.

## Verification (repo ground truth, 2-agent sweep 2026-07-28) — ALL CLAIMS TRUE

**Compiler side:**
- **Span.merge TRUE:** `00.common/diagnostics/span.spl:48-53` — `merge()` routes through
  `Span.new` which hardcodes `file: "", length: 0`. Note `to()` (:33-45) preserves file —
  only `merge()` is broken.
- **MIR spans TRUE:** `50.mir/mir_data.spl` — 21 of 22 `span:` sites are `span: nil`
  (every `emit_*`: const/copy/move/binop/unary/ref/load/store/alloc/call/cast/aggregate/
  field/gep/void_call). The `emit_*` signatures don't even accept a span. Only
  `begin_function` (:62-71) takes one.
- **LLVM debug TRUE + a gift:** `llvm_backend.spl:65,187` `debug_info`/`with_debug_info`
  never read by `compile_module` (:256-323). BUT `llvm_ir_builder.spl:468-489` already
  implements `emit_debug_info_header()`/`emit_di_subprogram()` producing real
  `!DICompileUnit`/`!DISubprogram` — **dead DWARF code, zero callers**. DS3 = wire it.
- **Diagnostic drift TRUE:** native `diagnostic.spl:9-16` (labels/notes/one help) vs
  Rust `common/src/diagnostic.rs:26-57` (EasyFix + Replacement + FixConfidence + JSON).
- **SReplay TRUE:** rich event kinds (`replay/semantic/trace_events.spl:10-19`) but
  `mir_debug_trace_injection.spl:245-262` emits `Call(nil, fn, [])` with `span: nil`.
- **CLI PARTIAL:** no `--debug-info` flag anywhere; internal `debug_info: bool` =
  `not is_release` (`backend_helpers.spl:347,442`); `--debug-trace=functions|objects|full`
  exists but drives sreplay, not DWARF.

**Runtime side:**
- **Log facade TRUE:** `src/lib/log.spl` (788L) — levels/filters/env-parse/4-slot
  backends/1024-rec 40-byte no-alloc ring/drop counter/panic flush all real. Defect
  confirmed: `log_dispatch_text()` (:574-584) passes dummy `p0=0` to backends — message
  text NEVER reaches the ring; stderr only in panic mode. `log_dispatch_record()`
  (:567-572) is the only real-payload path and isn't the text API.
- **Record fields TRUE:** seq/ts/p0/p1/fmt_handle/subsys/level/flags only (:383-391) —
  no build/source/thread/task/trace/span identity, no typed fields/redaction/sampling.
- **Web tracing TRUE:** `web_framework/tracing.spl` — 128-bit TraceId, W3C
  traceparent parse/emit, spans w/ attrs+status; exporter = JSON array join (:321-326),
  no OTLP.
- **DAP TRUE:** `dap/protocol.spl:201-231` capability list matches exactly (cond/hit/
  step-back/setVar/data-bp true; function-bp/exception/logpoints/loadedSources/
  readMemory/disassemble/cancel/breakpointLocations false).
- **GDB TRUE:** `dap/adapter/gdb_mi.spl:265-271` discards condition/hit/log; nested
  expansion `Err`; `debug/remote/protocol/gdb_mi.spl` transport = mkfifo + `sh -c` +
  `echo >fifo` + `timeout 10 grep -m1` — confirmed shell/FIFO/grep.
- **Crash TRUE:** Rust CLI panic hook writes `.simple/logs/crash_{pid}.log`
  (`cli/init.rs:56-145`); guide marks SIGSEGV/SIGABRT handling "Planned"
  (`crash_containment.md:163`).
