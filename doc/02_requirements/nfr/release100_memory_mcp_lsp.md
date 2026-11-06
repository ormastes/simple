<!-- codex-design -->
# Release 1.0.0 memory and MCP/LSP nonfunctional requirements

Status: **OPEN / NOT_RUN**. The selected plans are [memory](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_nogc_ownership_memory_hardening_plan.md) §§1, 5–9, 11–16 and [MCP/LSP](../../03_plan/release/1.0.0/inputs_2026-11-06/simple_mcp_lsp_source_debugging_improvement_plan_2026-10-29.md) §§3–6, 15–18, 20–22. These are user-selected requirements, not measured results.

| ID | Contract | Required evidence | Status |
|---|---|---|---|
| NFR-001 | Warm `num`/`info`/`hint` service p95 <20 ms; exclude network/client rendering | Fixed reference machine, existing projection, repeated trials, distribution and build/provider identities | NOT_RUN |
| NFR-002 | Warm cached bounded outline p95 <100 ms | Fixed corpus/language mix, source/parser cache state, source byte/read counts | NOT_RUN |
| NFR-003 | Warm focused navigation and annotation detail each p95 <200 ms | Cached semantic index/facts; no hidden cold-provider startup in warm samples | NOT_RUN |
| NFR-004 | Approximately 2,000 model-visible tokens per initial focused view, configurable | Budget entire text + structured response; label tokenizer estimate; coherent spans, omission ledger and expansion handles | NOT_RUN |
| NFR-005 | 3,000 concurrent distinct query/cache keys | Memory/view, retained snapshots, cancellation cleanup, queue fairness and p99 under contention; not 3,000 debugger targets | NOT_RUN |
| NFR-006 | Every expensive query bounded, cancellable and progress-aware | Deadlines; graph depth/visited nodes/alias expansion/source/regex/probe/process/stop-snapshot bounds; first-result + total latency | NOT_RUN |
| NFR-007 | Cheap view/toggle does no compiler spawn, test run, toolchain census, history walk or debugger attach | Front-door process/operation counters; no semantic-cache invalidation from presentation changes | NOT_RUN |
| NFR-008 | Cold/warm startup, warm requests and maximum RSS measured separately | Exact binary/provider/cache state, hardware, corpus size/language mix, invocation and latency/RSS receipts | NOT_RUN; absolute cold-start/RSS caps require reviewed host/product configuration before admission |
| NFR-009 | Memory repair lowers affected owner's retained/live bytes, preserves semantics and stays inside predeclared elapsed/memory bounds | Controlled paired workload; owner/phase attribution, raw units, repetitions and sampling limits; no post-hoc threshold weakening | NOT_RUN; plan specifies no universal numeric cap |
| NFR-010 | Repeated equivalent work returns scratch to documented post-warmup envelope | Live payload/backing bytes, region reserve, registry capacity/tombstones, resource counts; separately charge required retained surfaces | NOT_RUN |
| NFR-011 | Default fused path parses each exact parser input once; capture-off performs zero checkpoint/edge-record allocations or writes | Parse/decode/recovery counters, fused/split outputs/cleanup, allocation and write instrumentation | NOT_RUN |
| NFR-012 | Immutable sharing reduces actual duplication; one admitted producer per equal action | Single-flight waits/hits, physical/private memory, collision and semantic-key controls, active-reader eviction and cancellation/crash tests | NOT_RUN |
| NFR-013 | No surviving managed descendants or leaked rights/reservations after failure | Timeout/cancel/parent-death/crash/spawn-failure and PID-reuse fixtures; cap reaches grandchildren; unknown metrics never allow unlimited fanout | NOT_RUN |
| NFR-014 | Independent budgets for workers, queues, fibers, output, handles, device pins and cache generations | Known-limit fixtures and saturation rejection/backpressure; calibrated bytes/KiB/pages and enforcement charge | NOT_RUN |
| NFR-015 | No untrusted execution, secret leakage or unauthorized state access from reading | Trust/access/symlink/handle-isolation, redaction-before-indexing, escape rendering and provider execution-denial cases | NOT_RUN |
| NFR-016 | Exact source and version integrity across Unicode, encodings and edits | Korean/combining/emoji/tabs/CRLF/no-final-newline, original-byte maps, source/virtual segment separation and stale-edit rejection | NOT_RUN |
| NFR-017 | All advertised operations truthful on failure/absence and protocol lifecycle | Missing provider, malformed response, timeout, cancellation, shutdown, framing limits; stdout protocol purity and no fabricated zero/clean result | NOT_RUN |
| NFR-018 | Independent anti-removal gates and proof admission fail closed | Exact candidate-bound executed cardinality, protected requirement baseline, required-route/mutation/axiom checks | NOT_RUN |
| NFR-019 | Platform/backend/provider matrix preserved | Memory §12.2 and MCP §20.5 receipts; unsupported or unavailable rows stay explicit and cannot count as PASS | NOT_RUN |
| NFR-020 | Canonical tracking migration is lossless and atomic | Complete pinned SDN parse, before-image, malformed/partial/conflict failure-no-write controls, unrelated-row preservation and integrity resealing | NOT_RUN |

## Measurement rules

Retain source reads/bytes, raw parse/decode counts, per-stage cache hits/misses, copied/materialized bytes, owner live payload/reserve/capacity, RSS/private/committed/shared residency, enforcement charge, faults, device/pinned bytes, phase/total/queue time, worker/fiber counts and cancellation duration. Preserve raw units and calibration references. RSS is neither live payload nor absence of leakage; summed RSS can double-count shared mappings. Report missing metrics as unavailable, never zero.

Memory §13.2's historical 50,000-call fixture (950,009 versus 9 retained objects; 83,892 versus 4,960 KiB RSS; 0.40 versus 0.33 s) is context only. It is neither a new benchmark nor a release threshold. Do not advertise speedup or whole-compiler memory admission from those samples.

The plan does not specify universal startup/RSS, deep-query deadlines, session quota or compiler-budget numbers. Root and the owning implementation must pin these in reviewed target/fixture configuration before performance acceptance; pending numbers block admission rather than permitting unlimited work or invented PASS.
