# MCP JSON Primitive Performance Benchmark

> All thresholds are generous (60s) — goal is detecting order-of-magnitude

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MCP JSON Primitive Performance Benchmark

All thresholds are generous (60s) — goal is detecting order-of-magnitude

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/05_perf/mcp_json_perf_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Operations Tested
    - find_text (N=200): substring-scan loop, O(n*m) with per-iter slice
    - unescape_json_string (N=200): 6 chained .replace() calls
    - extract_field_raw (N=200): full field extraction over ~2KB JSON
    - extract_json_string (N=200): key lookup in initialize message

    ## Threshold
    All thresholds are generous (60s) — goal is detecting order-of-magnitude
    regressions and recording before/after µs for optimization work.

## Scenarios

### MCP JSON Primitive Performance

<details>
<summary>Advanced: find_text completes within threshold</summary>

#### find_text completes within threshold _(slow)_

- find_text completes within threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("find_text completes within threshold")
check(bench_find_text(200))
```

</details>


</details>

<details>
<summary>Advanced: unescape_json_string completes within threshold</summary>

#### unescape_json_string completes within threshold _(slow)_

- unescape_json_string completes within threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("unescape_json_string completes within threshold")
check(bench_unescape(200))
```

</details>


</details>

<details>
<summary>Advanced: extract_field_raw completes within threshold</summary>

#### extract_field_raw completes within threshold _(slow)_

- extract_field_raw completes within threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("extract_field_raw completes within threshold")
check(bench_extract_field_raw(200))
```

</details>


</details>

<details>
<summary>Advanced: extract_json_string completes within threshold</summary>

#### extract_json_string completes within threshold _(slow)_

- extract_json_string completes within threshold


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("extract_json_string completes within threshold")
check(bench_extract_json_string(200))
```

</details>


</details>

<details>
<summary>Advanced: extract_field_raw scales sub-quadratically with response size</summary>

#### extract_field_raw scales sub-quadratically with response size _(slow)_

- extract_field_raw scales sub-quadratically with response size


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-PERF
step("extract_field_raw scales sub-quadratically with response size")
check(bench_extract_scaling())
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
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

- Canonical SPipe generation for source `84f463651cd7673bab308caedc173f35b2cb0a31c049d11ba6b6bab100f038f2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84f463651cd7673bab308caedc173f35b2cb0a31c049d11ba6b6bab100f038f2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84f463651cd7673bab308caedc173f35b2cb0a31c049d11ba6b6bab100f038f2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/05_perf/mcp_json_perf_spec.spl
mirror: doc/06_spec/05_perf/mcp_json_perf_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/05_perf/mcp_json_perf_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/05_perf/mcp_json_perf_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/05_perf/mcp_json_perf_spec.spl:201:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'find_text completes within threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/mcp_json_perf_spec.spl:206:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'unescape_json_string completes within threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/05_perf/mcp_json_perf_spec.spl:211:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extract_field_raw completes within threshold' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
