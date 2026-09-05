# Monotonic Hardware Specification

> Tests covering SimpleOS boot monotonic clock arithmetic.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Monotonic Hardware Specification

## Scenarios

### SimpleOS boot monotonic clock arithmetic

#### keeps valid sub-microsecond intervals distinct from invalid samples

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- keeps valid sub-microsecond intervals distinct from invalid samples
   - Expected: boot_monotonic_elapsed_us(100, 100) equals `1`
   - Expected: boot_monotonic_elapsed_us(100, 99) equals `0`
   - Expected: boot_monotonic_elapsed_us(100, 125) equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps valid sub-microsecond intervals distinct from invalid samples")
expect(boot_monotonic_elapsed_us(100, 100)).to_equal(1)
expect(boot_monotonic_elapsed_us(100, 99)).to_equal(0)
expect(boot_monotonic_elapsed_us(100, 125)).to_equal(25)
```

</details>

#### creates exact deadlines and rejects overflow

- creates exact deadlines and rejects overflow
   - Expected: boot_monotonic_deadline_us(10, 500000) equals `500010`
   - Expected: boot_monotonic_deadline_us(9223372036854775806, 1) equals `9223372036854775807`
   - Expected: boot_monotonic_deadline_us(9223372036854775807, 1) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("creates exact deadlines and rejects overflow")
expect(boot_monotonic_deadline_us(10, 500000)).to_equal(500010)
expect(boot_monotonic_deadline_us(9223372036854775806, 1)).to_equal(9223372036854775807)
expect(boot_monotonic_deadline_us(9223372036854775807, 1)).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/boot/monotonic_hardware_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SimpleOS boot monotonic clock arithmetic.
- SimpleOS boot monotonic clock arithmetic

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `86c331d254993bad4d6fb7f3a41656253c0fdbe21ff826e1d56ce6e577d8bf87`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `86c331d254993bad4d6fb7f3a41656253c0fdbe21ff826e1d56ce6e577d8bf87`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `86c331d254993bad4d6fb7f3a41656253c0fdbe21ff826e1d56ce6e577d8bf87`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/os/boot/monotonic_hardware_spec.spl
mirror: doc/06_spec/01_unit/os/boot/monotonic_hardware_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/boot/monotonic_hardware_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/boot/monotonic_hardware_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/boot/monotonic_hardware_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/boot/monotonic_hardware_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps valid sub-microsecond intervals distinct from invalid samples' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/boot/monotonic_hardware_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'creates exact deadlines and rejects overflow' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
