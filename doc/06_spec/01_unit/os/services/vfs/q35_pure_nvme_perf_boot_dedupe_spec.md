# Q35 Pure Nvme Perf Boot Dedupe Specification

> Tests covering q35 perf timing helpers shared across vfs boot files.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Q35 Pure Nvme Perf Boot Dedupe Specification

## Scenarios

### q35 perf timing helpers shared across vfs boot files

#### computes elapsed microseconds from start/end timestamps

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- computes elapsed microseconds from start/end timestamps
   - Expected: _elapsed_us(1000i64, 1500i64) equals `500u64`
   - Expected: _elapsed_us(0i64, 1000000i64) equals `1000000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("computes elapsed microseconds from start/end timestamps")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(_elapsed_us(1000i64, 1500i64)).to_equal(500u64)
expect(_elapsed_us(0i64, 1000000i64)).to_equal(1000000u64)
```

</details>

#### clamps elapsed microseconds to 1 when end does not advance past start

- clamps elapsed microseconds to 1 when end does not advance past start
   - Expected: _elapsed_us(1000i64, 1000i64) equals `1u64`
   - Expected: _elapsed_us(1000i64, 500i64) equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clamps elapsed microseconds to 1 when end does not advance past start")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(_elapsed_us(1000i64, 1000i64)).to_equal(1u64)
expect(_elapsed_us(1000i64, 500i64)).to_equal(1u64)
```

</details>

#### computes IOPS from an op count and elapsed microseconds

- computes IOPS from an op count and elapsed microseconds
   - Expected: _iops(1000u64, 1000000u64) equals `1000u64`
   - Expected: _iops(4000u64, 500000u64) equals `8000u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("computes IOPS from an op count and elapsed microseconds")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(_iops(1000u64, 1000000u64)).to_equal(1000u64)
expect(_iops(4000u64, 500000u64)).to_equal(8000u64)
```

</details>

#### clamps IOPS to 1 for a zero elapsed window or a zero-valued result

- clamps IOPS to 1 for a zero elapsed window or a zero-valued result
   - Expected: _iops(1000u64, 0u64) equals `1u64`
   - Expected: _iops(1u64, 1000000000u64) equals `1u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("clamps IOPS to 1 for a zero elapsed window or a zero-valued result")
# evidence(protocol_json): asserted result fields below are the complete typed oracle
expect(_iops(1000u64, 0u64)).to_equal(1u64)
expect(_iops(1u64, 1000000000u64)).to_equal(1u64)
```

</details>

#### measures a real wall-clock window with the shared helpers

- run the helpers over live timestamps bracketing actual work
   - Expected: elapsed > 0u64 is true
   - Expected: _iops(100000u64, elapsed) > 0u64 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("run the helpers over live timestamps bracketing actual work")
# evidence(protocol_json): elapsed/iops values asserted below are the complete typed oracle
val start = rt_time_now_unix_micros()
var i = 0
while i < 100000:
    i = i + 1
val end = rt_time_now_unix_micros()
val elapsed = _elapsed_us(start, end)
expect(elapsed > 0u64).to_equal(true)  # oracle: a real busy loop must take nonzero time per the shared clock helper
expect(_iops(100000u64, elapsed) > 0u64).to_equal(true)  # oracle: derived IOPS from a measured window must be positive
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/services/vfs/q35_pure_nvme_perf_boot_dedupe_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering q35 perf timing helpers shared across vfs boot files.
- q35 perf timing helpers shared across vfs boot files

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `70cdbc6c70d3df3c8d237cd42b2a4c02fd36511f95c745ce560331a2b1e3c2ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `70cdbc6c70d3df3c8d237cd42b2a4c02fd36511f95c745ce560331a2b1e3c2ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `70cdbc6c70d3df3c8d237cd42b2a4c02fd36511f95c745ce560331a2b1e3c2ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **97/100**; effective score: **97/100**; blockers: **0**.

SSpec documentization score: 97/100
source: test/01_unit/os/services/vfs/q35_pure_nvme_perf_boot_dedupe_spec.spl
mirror: doc/06_spec/01_unit/os/services/vfs/q35_pure_nvme_perf_boot_dedupe_spec.md (current)
findings: 2 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/services/vfs/q35_pure_nvme_perf_boot_dedupe_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/services/vfs/q35_pure_nvme_perf_boot_dedupe_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
