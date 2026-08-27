# Kernel Log Specification

> Tests covering kernel log ring buffer.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Kernel Log Specification

## Scenarios

### kernel log ring buffer

#### preserves write order for dmesg-style reads

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- preserves write order for dmesg-style reads
   - Expected: entries.len() equals `2`
   - Expected: entries[0].timestamp_ns equals `0`
   - Expected: entries[0].pid equals `11`
   - Expected: entries[0].message equals `first`
   - Expected: entries[1].timestamp_ns equals `1`
   - Expected: entries[1].pid equals `22`
   - Expected: entries[1].message equals `second`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("preserves write order for dmesg-style reads")
val log = KernelLog.new(4)
log.write(3, 1, 11, "first")
log.write(6, 1, 22, "second")

val entries = log.read(0, 0, 4)
expect(entries.len()).to_equal(2)
expect(entries[0].timestamp_ns).to_equal(0)
expect(entries[0].pid).to_equal(11)
expect(entries[0].message).to_equal("first")
expect(entries[1].timestamp_ns).to_equal(1)
expect(entries[1].pid).to_equal(22)
expect(entries[1].message).to_equal("second")
```

</details>

#### filters by level and offset

- filters by level and offset
   - Expected: entries.len() equals `2`
   - Expected: entries[0].message equals `mid`
   - Expected: entries[1].message equals `high`
   - Expected: offset_entries.len() equals `1`
   - Expected: offset_entries[0].message equals `mid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("filters by level and offset")
val log = KernelLog.new(4)
log.write(2, 1, 1, "low")
log.write(4, 1, 2, "mid")
log.write(7, 1, 3, "high")

val entries = log.read(4, 0, 4)
expect(entries.len()).to_equal(2)
expect(entries[0].message).to_equal("mid")
expect(entries[1].message).to_equal("high")

val offset_entries = log.read(0, 1, 1)
expect(offset_entries.len()).to_equal(1)
expect(offset_entries[0].message).to_equal("mid")
```

</details>

#### keeps the newest entries when the ring wraps

- keeps the newest entries when the ring wraps
   - Expected: entries.len() equals `2`
   - Expected: entries[0].message equals `middle`
   - Expected: entries[1].message equals `new`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps the newest entries when the ring wraps")
val log = KernelLog.new(2)
log.write(3, 1, 1, "old")
log.write(3, 1, 2, "middle")
log.write(3, 1, 3, "new")

val entries = log.read(0, 0, 2)
expect(entries.len()).to_equal(2)
expect(entries[0].message).to_equal("middle")
expect(entries[1].message).to_equal("new")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/log/kernel_log_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering kernel log ring buffer.
- kernel log ring buffer

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `4e5a3fa4a86e6155fecd0a3aef1e12ba7f54177efef09ba63620cc0d4a2369ea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e5a3fa4a86e6155fecd0a3aef1e12ba7f54177efef09ba63620cc0d4a2369ea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e5a3fa4a86e6155fecd0a3aef1e12ba7f54177efef09ba63620cc0d4a2369ea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/os/kernel/log/kernel_log_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/log/kernel_log_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/log/kernel_log_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/log/kernel_log_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/log/kernel_log_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/log/kernel_log_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves write order for dmesg-style reads' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/log/kernel_log_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'filters by level and offset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/log/kernel_log_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the newest entries when the ring wraps' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
