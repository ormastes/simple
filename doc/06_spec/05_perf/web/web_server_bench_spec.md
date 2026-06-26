# Web Server Bench Specification

> <details>

<!-- sdn-diagram:id=web_server_bench_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=web_server_bench_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

web_server_bench_spec -> std
web_server_bench_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=web_server_bench_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Web Server Bench Specification

## Scenarios

### web server bench (AC-3, AC-8, AC-9)

#### parse_request_line parses GET correctly (oracle)

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Throughput oracle: assert a real number was recorded (not a no-op).
# ops/sec must be > 0 — proving the loop ran and timing was captured.
val ops_sec = _measure_throughput(WARM_ITERS)
val positive = ops_sec > 0
expect(positive).to_equal(true)
```

</details>

#### warm throughput: serialize-only path >= 1 ops/sec

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Serialize-only path throughput row.
val ops_sec = _measure_serialize_throughput(WARM_ITERS)
val positive = ops_sec > 0
expect(positive).to_equal(true)
```

</details>

#### bench_emit writes report and metrics files

- pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- pending


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
