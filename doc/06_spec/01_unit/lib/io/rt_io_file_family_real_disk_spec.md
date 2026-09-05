# Rt Io File Family Real Disk Specification

> Tests covering rt_io_file_* family moves real bytes on a real filesystem.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Rt Io File Family Real Disk Specification

## Scenarios

### rt_io_file_* family moves real bytes on a real filesystem

#### reproduces the defect and detects its class under the interpreter

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reproduces the defect and detects its class under the interpreter
- Run the run-path probe once under SIMPLE_EXECUTION_MODE=interpreter
- Infrastructure check: the rt_file_* control family must pass, or this example is measuring a broken probe rather than the bug
- Reproducer: open must hand back a real descriptor, not a stubbed zero/-1
- Reproducer: bytes written must be readable by a DIFFERENT family — an in-process fake cannot satisfy this
- Class: a predicate must agree with the control family about a file that demonstrably exists
- Class: a metadata read must return the true size, not a fabricated zero
- Class: a mutating call must really mutate, observed from outside the family
- No individual check may have failed


<details>
<summary>Executable SSpec</summary>

Runnable source: 27 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reproduces the defect and detects its class under the interpreter")
step("Run the run-path probe once under SIMPLE_EXECUTION_MODE=interpreter")
val interp = run_probe_in_mode("interpreter")

step("Infrastructure check: the rt_file_* control family must pass, or this example is measuring a broken probe rather than the bug")
expect(interp).to_contain("PASS control_rt_file_write_text")
expect(interp).to_contain("PASS control_rt_file_exists_true")
expect(interp).to_contain("PASS control_rt_file_read_text")

step("Reproducer: open must hand back a real descriptor, not a stubbed zero/-1")
expect(interp).to_contain("PASS rt_io_file_open_returns_nonnegative_fd")

step("Reproducer: bytes written must be readable by a DIFFERENT family — an in-process fake cannot satisfy this")
expect(interp).to_contain("PASS written_bytes_visible_to_control_family")

step("Class: a predicate must agree with the control family about a file that demonstrably exists")
expect(interp).to_contain("PASS rt_io_file_exists_agrees_with_control")

step("Class: a metadata read must return the true size, not a fabricated zero")
expect(interp).to_contain("PASS rt_io_file_meta_size_is_three")

step("Class: a mutating call must really mutate, observed from outside the family")
expect(interp).to_contain("PASS rt_io_file_delete_really_removes_file")

step("No individual check may have failed")
expect(interp).to_contain("RT_IO_FILE PROBE: ALL PASS")
```

</details>

#### detects the class under the JIT, where the stub substitution actually lives

- detects the class under the JIT, where the stub substitution actually lives
- Run the same probe once under SIMPLE_EXECUTION_MODE=jit
- Infrastructure check: the control family must still work under the JIT
- The rt_io_file_* family must behave identically to the control family under the JIT


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects the class under the JIT, where the stub substitution actually lives")
step("Run the same probe once under SIMPLE_EXECUTION_MODE=jit")
val jit = run_probe_in_mode("jit")

step("Infrastructure check: the control family must still work under the JIT")
expect(jit).to_contain("PASS control_rt_file_write_text")

step("The rt_io_file_* family must behave identically to the control family under the JIT")
expect(jit).to_contain("RT_IO_FILE PROBE: ALL PASS")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/io/rt_io_file_family_real_disk_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering rt_io_file_* family moves real bytes on a real filesystem.
- rt_io_file_* family moves real bytes on a real filesystem

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d7ac465e5b648966b6a2c6d87b4f3c0397be1ff2cc11a69c06ca6ad5579ffc5a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d7ac465e5b648966b6a2c6d87b4f3c0397be1ff2cc11a69c06ca6ad5579ffc5a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d7ac465e5b648966b6a2c6d87b4f3c0397be1ff2cc11a69c06ca6ad5579ffc5a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/lib/io/rt_io_file_family_real_disk_spec.spl
mirror: doc/06_spec/01_unit/lib/io/rt_io_file_family_real_disk_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/io/rt_io_file_family_real_disk_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/io/rt_io_file_family_real_disk_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/io/rt_io_file_family_real_disk_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reproduces the defect and detects its class under the interpreter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/io/rt_io_file_family_real_disk_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects the class under the JIT, where the stub substitution actually lives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
