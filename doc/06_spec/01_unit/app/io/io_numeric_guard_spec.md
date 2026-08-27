# Io Numeric Guard Specification

> Tests covering app io numeric guards.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Io Numeric Guard Specification

## Scenarios

### app io numeric guards

#### guards SIMPLE_MAX_PROCS parsing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- guards SIMPLE_MAX_PROCS parsing
   - Expected: _proc_gov_positive_int_or_zero("16") equals `16`
   - Expected: _proc_gov_positive_int_or_zero(" 4 ") equals `4`
   - Expected: _proc_gov_positive_int_or_zero("") equals `0`
   - Expected: _proc_gov_positive_int_or_zero("8x") equals `0`
   - Expected: _proc_gov_positive_int_or_zero("-2") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guards SIMPLE_MAX_PROCS parsing")
# oracle: digit-only env values parse exactly; malformed values clamp to 0 (unset)
expect(_proc_gov_positive_int_or_zero("16")).to_equal(16)
expect(_proc_gov_positive_int_or_zero(" 4 ")).to_equal(4)
expect(_proc_gov_positive_int_or_zero("")).to_equal(0)
expect(_proc_gov_positive_int_or_zero("8x")).to_equal(0)
expect(_proc_gov_positive_int_or_zero("-2")).to_equal(0)
```

</details>

#### guards file_size shell output parsing

- guards file_size shell output parsing
   - Expected: file_size("/tmp/io_guard_probe.txt") equals `5`
   - Expected: file_size("/tmp/io_guard_probe.txt") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("guards file_size shell output parsing")
# oracle: a real 5-byte file reports exactly 5; a 0-byte file reports 0
rt_file_write_text("/tmp/io_guard_probe.txt", "12345")
expect(file_size("/tmp/io_guard_probe.txt")).to_equal(5)
rt_file_write_text("/tmp/io_guard_probe.txt", "")
expect(file_size("/tmp/io_guard_probe.txt")).to_equal(0)
rt_file_remove("/tmp/io_guard_probe.txt")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/io_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering app io numeric guards.
- app io numeric guards

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `971d5d9f4542cd3653aa1df7c95e060eafc0f04675568fe56f0b3f2c3fb485e9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `971d5d9f4542cd3653aa1df7c95e060eafc0f04675568fe56f0b3f2c3fb485e9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `971d5d9f4542cd3653aa1df7c95e060eafc0f04675568fe56f0b3f2c3fb485e9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/app/io/io_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/app/io/io_numeric_guard_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/io/io_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/io_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/io_numeric_guard_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/io/io_numeric_guard_spec.spl:17:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards SIMPLE_MAX_PROCS parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/io/io_numeric_guard_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'guards file_size shell output parsing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
