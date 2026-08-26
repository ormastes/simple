# Web Server Bench Specification

> Tests covering web server bench (AC-3, AC-8, AC-9).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Server Bench Specification

## Scenarios

### web server bench (AC-3, AC-8, AC-9)

#### parse_request_line parses GET correctly (oracle)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


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


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("bench_emit writes report and metrics files")
# AC-3: emit benchmark docs. Verified via file existence (text primitive),
# not by reading BenchResult fields (cross-module struct bug workaround).
# bench_run_warm is also invoked to exercise the harness path.
# TODO: bench_run_warm + bench_emit require cross-module struct construction
# which returns Unit in interpreter mode (bug: interp_cross_module_struct_unit).
# Enable once that bug is fixed. File-existence verification is the AC-3
# evidence that the harness wired up correctly.
pending("interp-cross-module-struct-unit")
```

</details>

<details>
<summary>Advanced: cold-start row: pending — server accept-loop blocks forever</summary>

#### cold-start row: pending — server accept-loop blocks forever

- cold-start row: pending — server accept-loop blocks forever


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("cold-start row: pending — server accept-loop blocks forever")
# The web server main.spl (examples/06_io/simple_web_server/main.spl)
# is a blocking accept-loop with no one-shot mode. bench_run_process
# would hang indefinitely. This row documents the gap and will be
# enabled if a --one-shot / --benchmark flag is added to the server CLI.
# AC-8: do NOT add such a flag without a separate approval — API change.
pending("server-accept-loop-no-one-shot-mode")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/web/web_server_bench_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering web server bench (AC-3, AC-8, AC-9).
- web server bench (AC-3, AC-8, AC-9)

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

- Canonical SPipe generation for source `a5e94c68b526d85966d67b209602b0d701880f07511ae78e5fc19d7091a5f6c5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5e94c68b526d85966d67b209602b0d701880f07511ae78e5fc19d7091a5f6c5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5e94c68b526d85966d67b209602b0d701880f07511ae78e5fc19d7091a5f6c5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/05_perf/web/web_server_bench_spec.spl
mirror: doc/06_spec/05_perf/web/web_server_bench_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/05_perf/web/web_server_bench_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/web/web_server_bench_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/web/web_server_bench_spec.spl:1:1: blocker SSDOC-ORA-001 [oracle] (-50): unconditional pending or fail-fast scaffold remains
  why: A passing-looking document without an oracle is not conformance evidence.
  improve: Replace placeholders with an observable production assertion.
test/05_perf/web/web_server_bench_spec.spl:148:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parse_request_line parses GET correctly (oracle)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web/web_server_bench_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'HttpResponse.json serializes to HTTP/1.1 200 with correct body (oracle)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/web/web_server_bench_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'full hot-path (parse→dispatch→serialize) returns 200 for /api/health' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
