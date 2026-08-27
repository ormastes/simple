# Direct Io Specification

> Tests covering OS DMA DirectIoResult durability.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Direct Io Specification

## Scenarios

### OS DMA DirectIoResult durability

#### defaults ordinary completion to non-durable and exposes durable completion

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults ordinary completion to non-durable and exposes durable completion
   - Expected: source contains `durable: bool`
   - Expected: source contains `static fn ok(bytes_transferred: i64, latency_us: i64) -> DirectIoResult:`
   - Expected: source contains `durable: false`
   - Expected: source contains `static fn durable_ok(bytes_transferred: i64, latency_us: i64) -> DirectIoResult:`
   - Expected: source contains `durable: true`
   - Expected: source contains `",durable=" + self.durable.to_text()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("defaults ordinary completion to non-durable and exposes durable completion")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
val source = read_file("src/os/drivers/dma/direct_io.spl")
expect(source.contains("durable: bool")).to_equal(true)
expect(source.contains("static fn ok(bytes_transferred: i64, latency_us: i64) -> DirectIoResult:")).to_equal(true)
expect(source.contains("durable: false")).to_equal(true)
expect(source.contains("static fn durable_ok(bytes_transferred: i64, latency_us: i64) -> DirectIoResult:")).to_equal(true)
expect(source.contains("durable: true")).to_equal(true)
expect(source.contains("\",durable=\" + self.durable.to_text()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/drivers/dma/direct_io_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering OS DMA DirectIoResult durability.
- OS DMA DirectIoResult durability

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

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `84672b500224f9e1e484ef5bfc9da7d1750c68089da6ed72aa91cfb5a35a7639`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84672b500224f9e1e484ef5bfc9da7d1750c68089da6ed72aa91cfb5a35a7639`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84672b500224f9e1e484ef5bfc9da7d1750c68089da6ed72aa91cfb5a35a7639`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/os/drivers/dma/direct_io_spec.spl
mirror: doc/06_spec/01_unit/os/drivers/dma/direct_io_spec.md (current)
findings: 3 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=87; blocker cap makes effective=49
doc/06_spec/01_unit/os/drivers/dma/direct_io_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/drivers/dma/direct_io_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/drivers/dma/direct_io_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
<!-- sspec-maintain:scorecard:end -->
