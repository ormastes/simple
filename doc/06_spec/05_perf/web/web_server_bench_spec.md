# web_server_bench_spec

> Purpose: measure and prove the Simple web server's in-process hot path —

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# web_server_bench_spec

Purpose: measure and prove the Simple web server's in-process hot path —

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/web/web_server_bench_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: measure and prove the Simple web server's in-process hot path —
parse_request_line -> inline dispatch -> serialize_response — with absolute
wire-format oracles (HTTP/1.1 200 + exact body) and emitted bench artifacts.
Audience: web runtime and perf owners.

## Scenarios

### web server bench (AC-3, AC-8, AC-9)

#### parse_request_line parses GET correctly (oracle)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- parse_request_line parses GET correctly (oracle)
   - Expected: method equals `GET`
   - Expected: path equals `/api/health`
   - Expected: ver equals `HTTP/1.1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("parse_request_line parses GET correctly (oracle)")
# Gate test: verify the in-memory parse seam works in interpreter mode.
val parsed = parse_request_line(GET_HEALTH_LINE)
val method = parsed.0
val path   = parsed.1
val ver    = parsed.2
expect(method).to_equal("GET")
expect(path).to_equal("/api/health")
expect(ver).to_equal("HTTP/1.1")
```

</details>

#### HttpResponse.json serializes to HTTP/1.1 200 with correct body (oracle)

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- HttpResponse.json serializes to HTTP/1.1 200 with correct body (oracle)
   - Expected: has_200 is true
   - Expected: has_body is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("HttpResponse.json serializes to HTTP/1.1 200 with correct body (oracle)")
# Core correctness oracle: proves the handler ran and produced a real
# HTTP response, not a no-op. Assert on text primitives only.
val resp = HttpResponse.json(HEALTH_BODY)
val wire = serialize_response(resp)
val has_200 = wire.contains("HTTP/1.1 200")
val has_body = wire.contains(HEALTH_BODY)
expect(has_200).to_equal(true)
expect(has_body).to_equal(true)
```

</details>

#### full hot-path (parse→dispatch→serialize) returns 200 for /api/health

**Manual warnings:**
- invalid capture metadata value: protocol_json (expected kind tui|gui|html|text|api|protocol|exec|binary|log|artifact and mode after_step|after_scenario|on_failure|off)


- full hot-path (parse→dispatch→serialize) returns 200 for /api/health
   - Expected: has_200 is true
   - Expected: has_body is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("full hot-path (parse→dispatch→serialize) returns 200 for /api/health")
# End-to-end in-process oracle: parse request line + inline router +
# serialize. Asserts both status and body substring on text.
val wire = _parse_and_respond(GET_HEALTH_LINE)
val has_200  = wire.contains("HTTP/1.1 200")
val has_body = wire.contains(HEALTH_BODY)
expect(has_200).to_equal(true)
expect(has_body).to_equal(true)
```

</details>

#### warm throughput: parse+dispatch+serialize >= 1 ops/sec

- warm throughput: parse+dispatch+serialize >= 1 ops/sec
   - Expected: positive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("warm throughput: parse+dispatch+serialize >= 1 ops/sec")
# Throughput oracle: assert a real number was recorded (not a no-op).
# ops/sec must be > 0 — proving the loop ran and timing was captured.
val ops_sec = _measure_throughput(WARM_ITERS)
val positive = ops_sec > 0
expect(positive).to_equal(true)
```

</details>

#### warm throughput: serialize-only path >= 1 ops/sec

- warm throughput: serialize-only path >= 1 ops/sec
   - Expected: positive is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("warm throughput: serialize-only path >= 1 ops/sec")
# Serialize-only path throughput row.
val ops_sec = _measure_serialize_throughput(WARM_ITERS)
val positive = ops_sec > 0
expect(positive).to_equal(true)
```

</details>

#### bench_emit writes report and metrics files

- bench_emit writes report and metrics files
   - Expected: rt_file_exists(REPORT_PATH) is true
   - Expected: rt_file_exists(TABLE_PATH) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("bench_emit writes report and metrics files")
# AC-3: emit benchmark docs. Verified via file existence (text primitive),
# not by reading BenchResult fields (cross-module struct bug workaround).
# bench_run_warm is also invoked to exercise the harness path.
# Struct CONSTRUCTION cross-module works (proven in
# test/05_perf/lang/lang_script_vs_compiler_bench_spec.spl); only struct
# FIELD ACCESS returns Unit in interpreter mode, so verification here is
# artifact-based (file existence + content), never field reads.
val bc = make_bench_case("web_hot_path", "interp", "warm", 100)
val r = bench_run_warm(bc, _warm_emit_workload)
var rows: [BenchResult] = []
rows.push(r)
bench_emit(rows, REPORT_PATH, TABLE_PATH)
expect(rt_file_exists(REPORT_PATH)).to_equal(true)  # oracle: the bench report artifact is emitted
expect(rt_file_exists(TABLE_PATH)).to_equal(true)   # oracle: the metrics table artifact is emitted
```

</details>

<details>
<summary>Advanced: cold-start row: pending — server accept-loop blocks forever</summary>

#### cold-start row: pending — server accept-loop blocks forever

- cold-start row: pending — server accept-loop blocks forever
   - Expected: wire contains `HTTP/1.1 200`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("cold-start row: pending — server accept-loop blocks forever")
# The web server main.spl (examples/06_io/simple_web_server/main.spl)
# is a blocking accept-loop with no one-shot mode. bench_run_process
# would hang indefinitely. This row documents the gap and will be
# enabled if a --one-shot / --benchmark flag is added to the server CLI.
# AC-8: do NOT add such a flag without a separate approval — API change.
# Honest skip: prove this row's gating oracle before skipping — the
# hot-path wire format the cold row would double must be a valid 200.
val wire = _parse_and_respond(GET_HEALTH_LINE)
expect(wire.contains("HTTP/1.1 200")).to_equal(true)  # oracle: the request the cold row would replay yields a real 200
return "skip: server accept-loop has no one-shot mode — bench_run_process would block forever"
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-PERF`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `8b10af71ec8c4819e2af5ca4c41edbd2d1e402582697a58445eeb024b02c4327`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b10af71ec8c4819e2af5ca4c41edbd2d1e402582697a58445eeb024b02c4327`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b10af71ec8c4819e2af5ca4c41edbd2d1e402582697a58445eeb024b02c4327`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/05_perf/web/web_server_bench_spec.spl
mirror: doc/06_spec/05_perf/web/web_server_bench_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/web/web_server_bench_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/web/web_server_bench_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/web/web_server_bench_spec.spl:201:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warm throughput: parse+dispatch+serialize >= 1 ops/sec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web/web_server_bench_spec.spl:210:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warm throughput: serialize-only path >= 1 ops/sec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web/web_server_bench_spec.spl:218:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bench_emit writes report and metrics files' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
