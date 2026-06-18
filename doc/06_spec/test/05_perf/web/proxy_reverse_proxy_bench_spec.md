# Reverse Proxy Production Benchmark Evidence

> This host-safe performance spec records deterministic benchmark rows for the production reverse-proxy helper path. It exercises route planning, upstream request serialization, response dechunk/forward policy, pooling, backpressure, and sync helper parity without opening sockets or claiming native throughput.

<!-- sdn-diagram:id=proxy_reverse_proxy_bench_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=proxy_reverse_proxy_bench_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

proxy_reverse_proxy_bench_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=proxy_reverse_proxy_bench_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Reverse Proxy Production Benchmark Evidence

This host-safe performance spec records deterministic benchmark rows for the production reverse-proxy helper path. It exercises route planning, upstream request serialization, response dechunk/forward policy, pooling, backpressure, and sync helper parity without opening sockets or claiming native throughput.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Requirements | doc/02_requirements/nfr/gpu_web_db_offload.md |
| Plan | doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md |
| Design | doc/05_design/gpu_web_db_offload.md |
| Research | doc/01_research/local/gpu_web_db_offload.md |
| Source | `test/05_perf/web/proxy_reverse_proxy_bench_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

This host-safe performance spec records deterministic benchmark rows for the
production reverse-proxy helper path. It exercises route planning, upstream
request serialization, response dechunk/forward policy, pooling, backpressure,
and sync helper parity without opening sockets or claiming native throughput.

## Requirements

**Requirements:** doc/02_requirements/nfr/gpu_web_db_offload.md

- Proxy benchmark evidence must report latency-shaped rows before production
  proxy throughput claims.
- CPU-owned proxy control-plane work remains separate from GPU/offload metrics.
- Large-response helpers must expose response bytes and backpressure state.

## Plan

**Plan:** doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md

## Design

**Design:** doc/05_design/gpu_web_db_offload.md

## Research

**Research:** doc/01_research/local/gpu_web_db_offload.md

## Scenarios

### reverse proxy production benchmark evidence

#### should report host-safe async proxy policy benchmark metrics

- Measure async proxy planning, serialization, dechunking, reuse, and backpressure policy
   - Expected: row.name equals `async_proxy_policy_100`
   - Expected: row.mode equals `async`
   - Expected: row.metric equals `latency_us`
   - Expected: row.iterations equals `PROXY_BENCH_ITERS`
   - Expected: row.response_bytes equals `PROXY_BENCH_ITERS * 2`
   - Expected: row.upstream_reuse equals `PROXY_BENCH_ITERS`
   - Expected: row.backpressure_pauses equals `PROXY_BENCH_ITERS`
   - Expected: row.errors equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure async proxy planning, serialization, dechunking, reuse, and backpressure policy")
val row = make_async_proxy_policy_row()
expect(row.name).to_equal("async_proxy_policy_100")
expect(row.mode).to_equal("async")
expect(row.metric).to_equal("latency_us")
expect(row.value_us).to_be_greater_than(0)
expect(row.iterations).to_equal(PROXY_BENCH_ITERS)
expect(row.request_bytes).to_be_greater_than(0)
expect(row.response_bytes).to_equal(PROXY_BENCH_ITERS * 2)
expect(row.upstream_reuse).to_equal(PROXY_BENCH_ITERS)
expect(row.backpressure_pauses).to_equal(PROXY_BENCH_ITERS)
expect(row.errors).to_equal(0)
```

</details>

#### should report host-safe sync proxy helper benchmark metrics

- Measure sync proxy matching and fixed-length request serialization
   - Expected: row.name equals `sync_proxy_helper_100`
   - Expected: row.mode equals `sync`
   - Expected: row.metric equals `latency_us`
   - Expected: row.iterations equals `PROXY_BENCH_ITERS`
   - Expected: row.response_bytes equals `PROXY_BENCH_ITERS * 2`
   - Expected: row.upstream_reuse equals `0`
   - Expected: row.backpressure_pauses equals `0`
   - Expected: row.errors equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure sync proxy matching and fixed-length request serialization")
val row = make_sync_proxy_helper_row()
expect(row.name).to_equal("sync_proxy_helper_100")
expect(row.mode).to_equal("sync")
expect(row.metric).to_equal("latency_us")
expect(row.value_us).to_be_greater_than(0)
expect(row.iterations).to_equal(PROXY_BENCH_ITERS)
expect(row.request_bytes).to_be_greater_than(0)
expect(row.response_bytes).to_equal(PROXY_BENCH_ITERS * 2)
expect(row.upstream_reuse).to_equal(0)
expect(row.backpressure_pauses).to_equal(0)
expect(row.errors).to_equal(0)
```

</details>

#### should report host-safe async request streaming benchmark metrics

- Measure fixed request-body streaming, upstream writes, and backpressure policy
   - Expected: row.name equals `async_proxy_request_stream_100`
   - Expected: row.mode equals `async`
   - Expected: row.metric equals `latency_us`
   - Expected: row.iterations equals `PROXY_BENCH_ITERS`
   - Expected: row.response_bytes equals `0`
   - Expected: row.upstream_reuse equals `0`
   - Expected: row.backpressure_pauses equals `PROXY_BENCH_ITERS`
   - Expected: row.errors equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure fixed request-body streaming, upstream writes, and backpressure policy")
val row = make_async_proxy_request_stream_row()
expect(row.name).to_equal("async_proxy_request_stream_100")
expect(row.mode).to_equal("async")
expect(row.metric).to_equal("latency_us")
expect(row.value_us).to_be_greater_than(0)
expect(row.iterations).to_equal(PROXY_BENCH_ITERS)
expect(row.request_bytes).to_be_greater_than(PROXY_BENCH_ITERS * 10)
expect(row.response_bytes).to_equal(0)
expect(row.upstream_reuse).to_equal(0)
expect(row.backpressure_pauses).to_equal(PROXY_BENCH_ITERS)
expect(row.errors).to_equal(0)
```

</details>

#### should report host-safe async tunnel handshake benchmark metrics

- Measure tunnel planning, setup serialization, upstream 101 validation, and relay readiness
   - Expected: row.name equals `async_proxy_tunnel_handshake_100`
   - Expected: row.mode equals `async`
   - Expected: row.metric equals `latency_us`
   - Expected: row.iterations equals `PROXY_BENCH_ITERS`
   - Expected: row.upstream_reuse equals `0`
   - Expected: row.backpressure_pauses equals `PROXY_BENCH_ITERS`
   - Expected: row.errors equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure tunnel planning, setup serialization, upstream 101 validation, and relay readiness")
val row = make_async_proxy_tunnel_row()
expect(row.name).to_equal("async_proxy_tunnel_handshake_100")
expect(row.mode).to_equal("async")
expect(row.metric).to_equal("latency_us")
expect(row.value_us).to_be_greater_than(0)
expect(row.iterations).to_equal(PROXY_BENCH_ITERS)
expect(row.request_bytes).to_be_greater_than(PROXY_BENCH_ITERS * 80)
expect(row.response_bytes).to_be_greater_than(PROXY_BENCH_ITERS * 70)
expect(row.upstream_reuse).to_equal(0)
expect(row.backpressure_pauses).to_equal(PROXY_BENCH_ITERS)
expect(row.errors).to_equal(0)
```

</details>

#### should report host-safe async production hardening benchmark metrics

- Measure timeout, request backpressure, response backpressure, pool pressure, and throughput evidence
   - Expected: row.name equals `async_proxy_hardening_evidence_100`
   - Expected: row.mode equals `async`
   - Expected: row.metric equals `latency_us`
   - Expected: row.iterations equals `PROXY_BENCH_ITERS`
   - Expected: row.request_bytes equals `PROXY_BENCH_ITERS * 6`
   - Expected: row.upstream_reuse equals `PROXY_BENCH_ITERS`
   - Expected: row.backpressure_pauses equals `PROXY_BENCH_ITERS * 3`
   - Expected: row.errors equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure timeout, request backpressure, response backpressure, pool pressure, and throughput evidence")
val row = make_async_proxy_hardening_evidence_row()
expect(row.name).to_equal("async_proxy_hardening_evidence_100")
expect(row.mode).to_equal("async")
expect(row.metric).to_equal("latency_us")
expect(row.value_us).to_be_greater_than(0)
expect(row.iterations).to_equal(PROXY_BENCH_ITERS)
expect(row.request_bytes).to_equal(PROXY_BENCH_ITERS * 6)
expect(row.response_bytes).to_be_greater_than(0)
expect(row.upstream_reuse).to_equal(PROXY_BENCH_ITERS)
expect(row.backpressure_pauses).to_equal(PROXY_BENCH_ITERS * 3)
expect(row.errors).to_equal(0)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Requirements:** [doc/02_requirements/nfr/gpu_web_db_offload.md](doc/02_requirements/nfr/gpu_web_db_offload.md)
- **Plan:** [doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md](doc/03_plan/agent_tasks/gpu_web_db_offload_impl_status.md)
- **Design:** [doc/05_design/gpu_web_db_offload.md](doc/05_design/gpu_web_db_offload.md)
- **Research:** [doc/01_research/local/gpu_web_db_offload.md](doc/01_research/local/gpu_web_db_offload.md)


</details>
