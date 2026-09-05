# Klog Specification

> Tests covering KernelLog helper.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Klog Specification

## Scenarios

### KernelLog helper

#### writes entries through the freestanding-safe helper

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- writes entries through the freestanding-safe helper
   - Expected: log.total() equals `1`
   - Expected: log.len() equals `1`
   - Expected: entries.len() equals `1`
   - Expected: entries[0].level equals `6`
   - Expected: entries[0].facility equals `1`
   - Expected: entries[0].pid equals `42`
   - Expected: entries[0].message equals `spawned`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("writes entries through the freestanding-safe helper")
var log = KernelLog.new(4)
klog_write(log, 6, 1, 42, "spawned")

expect(log.total()).to_equal(1)
expect(log.len()).to_equal(1)

val entries = log.read(0, 0, 4)
expect(entries.len()).to_equal(1)
expect(entries[0].level).to_equal(6)
expect(entries[0].facility).to_equal(1)
expect(entries[0].pid).to_equal(42)
expect(entries[0].message).to_equal("spawned")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/log/klog_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering KernelLog helper.
- KernelLog helper

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `fefa93acb1275c313aff58cecfeb1fb585f3c0efbcf35c4539c8760504b51220`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `fefa93acb1275c313aff58cecfeb1fb585f3c0efbcf35c4539c8760504b51220`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `fefa93acb1275c313aff58cecfeb1fb585f3c0efbcf35c4539c8760504b51220`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/os/kernel/log/klog_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/log/klog_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/log/klog_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/log/klog_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/log/klog_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/log/klog_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'writes entries through the freestanding-safe helper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
