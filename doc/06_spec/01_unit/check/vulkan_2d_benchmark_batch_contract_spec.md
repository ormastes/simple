# Vulkan 2d Benchmark Batch Contract Specification

> Tests covering Vulkan 2D benchmark frame batching.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Vulkan 2d Benchmark Batch Contract Specification

## Scenarios

### Vulkan 2D benchmark frame batching

#### records clear and rectangles before one submit per frame

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- records clear and rectangles before one submit per frame
   - Expected: source.count("rt_vulkan_submit_and_wait(cmd)") equals `1`
   - Expected: source does not contain `fn dispatch_compute(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-CHECK
step("records clear and rectangles before one submit per frame")
val source = file_read(
    "test/05_perf/graphics_2d/bench_2d_vulkan.spl")

expect(source).to_contain(
    "val cmd = rt_vulkan_begin_compute()")
expect(source).to_contain(
    "ready = encode_compute(cmd, pipe_rect")
expect(source).to_contain(
    "if not ready or not rt_vulkan_end_compute(cmd):")
expect(source).to_contain("rt_vulkan_discard_command(cmd)")
expect(source.count("rt_vulkan_submit_and_wait(cmd)")).to_equal(1)
expect(source).to_contain("compute_submits_per_frame=1")
expect(source.contains("fn dispatch_compute(")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/check/vulkan_2d_benchmark_batch_contract_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Vulkan 2D benchmark frame batching.
- Vulkan 2D benchmark frame batching

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-CHECK`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e89338779504148561e15a424a6b3d8b4fa2a1eb5e86b96c19d16774bbbbf65`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e89338779504148561e15a424a6b3d8b4fa2a1eb5e86b96c19d16774bbbbf65`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e89338779504148561e15a424a6b3d8b4fa2a1eb5e86b96c19d16774bbbbf65`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/check/vulkan_2d_benchmark_batch_contract_spec.spl
mirror: doc/06_spec/01_unit/check/vulkan_2d_benchmark_batch_contract_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=40
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=83; blocker cap makes effective=49
doc/06_spec/01_unit/check/vulkan_2d_benchmark_batch_contract_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/check/vulkan_2d_benchmark_batch_contract_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/check/vulkan_2d_benchmark_batch_contract_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/check/vulkan_2d_benchmark_batch_contract_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/check/vulkan_2d_benchmark_batch_contract_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'records clear and rectangles before one submit per frame' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
