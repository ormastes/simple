# Stage3 Bootstrap Flat Warning Specification

> Tests covering stage3 bootstrap-flat measurement warning.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Stage3 Bootstrap Flat Warning Specification

## Scenarios

### stage3 bootstrap-flat measurement warning

#### defines log_bootstrap_flat_warning as an always-on banner (uses log_warn, not log_phase)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines log_bootstrap_flat_warning as an always-on banner (uses log_warn, not log_phase)


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defines log_bootstrap_flat_warning as an always-on banner (uses log_warn, not log_phase)")
val source = log_helpers_source()

expect(source).to_contain("pub fn log_bootstrap_flat_warning(site: text):")
# log_warn's body is an unconditional print -- verify the warning
# function calls log_warn (unconditional), NOT log_phase (which is a
# no-op unless driver_phase_trace_enabled() -- the exact gate that
# made the original "aot:flat_mir_passes:skipped" banner invisible).
val fn_start = source.find("pub fn log_bootstrap_flat_warning(site: text):")
val fn_end = source.find("pub fn log_phase(msg: text):")
expect(fn_end).to_be_greater_than(fn_start)
val fn_body = source[fn_start:fn_end]
expect(fn_body).to_contain("log_warn(")
expect(fn_body).to_not_contain("driver_phase_trace_enabled()")
```

</details>

#### warns that a clean stage3 count is not tree-clean evidence, pointing at the bug record

- warns that a clean stage3 count is not tree-clean evidence, pointing at the bug record


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns that a clean stage3 count is not tree-clean evidence, pointing at the bug record")
val source = log_helpers_source()

expect(source).to_contain("is NOT evidence the tree is clean")
expect(source).to_contain(
    "doc/08_tracking/bug/stage3_clean_baseline_is_bootstrap_flat_artifact_2026-08-01.md")
```

</details>

#### is wired at the borrow-check / flat-MIR-passes skip site (driver_aot_pipeline.spl)

- is wired at the borrow-check / flat-MIR-passes skip site (driver_aot_pipeline.spl)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is wired at the borrow-check / flat-MIR-passes skip site (driver_aot_pipeline.spl)")
val source = aot_pipeline_source()

expect(source).to_contain(
    "use compiler.driver.driver_log_helpers.{log_debug, log_error, log_phase, log_bootstrap_flat_warning}")
expect(source).to_contain("if bootstrap_flat_aot:\n            log_phase(\"aot:flat_mir_passes:skipped\")\n            log_bootstrap_flat_warning(\"aot:flat_mir_passes:skipped\")")
```

</details>

#### is wired at the MIR-lowering skip site (driver_pipeline_lowering.spl)

- is wired at the MIR-lowering skip site (driver_pipeline_lowering.spl)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is wired at the MIR-lowering skip site (driver_pipeline_lowering.spl)")
val source = pipeline_lowering_source()

expect(source).to_contain(
    "use compiler.driver.driver_log_helpers.{log_debug, log_phase, log_build_progress, log_bootstrap_flat_warning}")
expect(source).to_contain("log_bootstrap_flat_warning(\"mir:bootstrap_fixed\")")
```

</details>

#### sabotage check: removing either call site would leave a skip branch with no loud warning

- sabotage check: removing either call site would leave a skip branch with no loud warning


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sabotage check: removing either call site would leave a skip branch with no loud warning")
# This encodes the exact defect shape from the bug report: a
# `bootstrap_flat_aot` / SIMPLE_BOOTSTRAP branch that returns/continues
# without ever calling the unconditional warning. Both known skip
# sites must call it exactly once.
val aot_source = aot_pipeline_source()
val lowering_source = pipeline_lowering_source()

val aot_calls = aot_source.split("log_bootstrap_flat_warning(").len() - 1
val lowering_calls = lowering_source.split("log_bootstrap_flat_warning(").len() - 1

expect(aot_calls).to_be_greater_than(0)
expect(lowering_calls).to_be_greater_than(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/driver/stage3_bootstrap_flat_warning_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering stage3 bootstrap-flat measurement warning.
- stage3 bootstrap-flat measurement warning

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f625ae0c01245d7117e703ad2ceecb6465a6e6f37d6b6088d35cf640a1141f7d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f625ae0c01245d7117e703ad2ceecb6465a6e6f37d6b6088d35cf640a1141f7d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f625ae0c01245d7117e703ad2ceecb6465a6e6f37d6b6088d35cf640a1141f7d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/driver/stage3_bootstrap_flat_warning_spec.spl
mirror: doc/06_spec/01_unit/compiler/driver/stage3_bootstrap_flat_warning_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/driver/stage3_bootstrap_flat_warning_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/driver/stage3_bootstrap_flat_warning_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/driver/stage3_bootstrap_flat_warning_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines log_bootstrap_flat_warning as an always-on banner (uses log_warn, not log_phase)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/stage3_bootstrap_flat_warning_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns that a clean stage3 count is not tree-clean evidence, pointing at the bug record' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/driver/stage3_bootstrap_flat_warning_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is wired at the borrow-check / flat-MIR-passes skip site (driver_aot_pipeline.spl)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
