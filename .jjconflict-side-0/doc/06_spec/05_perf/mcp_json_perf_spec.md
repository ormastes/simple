# MCP JSON Primitive Performance Benchmark

> MCP JSON Primitive Performance Benchmark

<!-- sdn-diagram:id=mcp_json_perf_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_json_perf_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_json_perf_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_json_perf_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP JSON Primitive Performance Benchmark

MCP JSON Primitive Performance Benchmark

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | MCP JSON Perf Opt Round 1 |
| Category | Performance \| MCP |
| Status | Implemented |
| Source | `test/05_perf/mcp_json_perf_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

MCP JSON Primitive Performance Benchmark

Measures wall-clock microseconds for the hot JSON primitive functions
used on every MCP handshake message (initialize, tools/list).
Uses rt_time_now_unix_micros() for timing.
Note: interpreter mode only verifies file loading (it block bodies don't execute).

## Scenarios

### MCP JSON Primitive Performance

<details>
<summary>Advanced: find_text completes within threshold</summary>

#### find_text completes within threshold _(slow)_

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bench_find_text(200))
```

</details>


</details>

<details>
<summary>Advanced: unescape_json_string completes within threshold</summary>

#### unescape_json_string completes within threshold _(slow)_

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bench_unescape(200))
```

</details>


</details>

<details>
<summary>Advanced: extract_field_raw completes within threshold</summary>

#### extract_field_raw completes within threshold _(slow)_

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bench_extract_field_raw(200))
```

</details>


</details>

<details>
<summary>Advanced: extract_json_string completes within threshold</summary>

#### extract_json_string completes within threshold _(slow)_

- check


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
check(bench_extract_json_string(200))
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
