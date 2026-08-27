# MIR terminator variant name (regression)

> Reproducer for `doc/08_tracking/bug/vhdl_backend_block_temps_emit_process_variables_not_signals_2026-08-04.md` (the "stale `MirTerminator.Return`" half). The `MirTerminator` enum declares `Ret`, never `Return`. Five spec files constructed `MirTerminator.Return(...)`, a variant that does not exist. Constructing an unknown variant is only diagnosed when the expression is actually evaluated, so the defect stayed invisible in files whose bodies were skipped, and detonated as `semantic: unknown variant or method 'Return' on enum MirTerminator` in the files whose bodies did run.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# MIR terminator variant name (regression)

Reproducer for `doc/08_tracking/bug/vhdl_backend_block_temps_emit_process_variables_not_signals_2026-08-04.md` (the "stale `MirTerminator.Return`" half). The `MirTerminator` enum declares `Ret`, never `Return`. Five spec files constructed `MirTerminator.Return(...)`, a variant that does not exist. Constructing an unknown variant is only diagnosed when the expression is actually evaluated, so the defect stayed invisible in files whose bodies were skipped, and detonated as `semantic: unknown variant or method 'Return' on enum MirTerminator` in the files whose bodies did run.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler / MIR |
| Status | Stable |
| Source | `test/01_unit/compiler/mir/mir_terminator_variant_name_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Reproducer for `doc/08_tracking/bug/vhdl_backend_block_temps_emit_process_variables_not_signals_2026-08-04.md`
(the "stale `MirTerminator.Return`" half). The `MirTerminator` enum declares
`Ret`, never `Return`. Five spec files constructed `MirTerminator.Return(...)`,
a variant that does not exist. Constructing an unknown variant is only
diagnosed when the expression is actually evaluated, so the defect stayed
invisible in files whose bodies were skipped, and detonated as
`semantic: unknown variant or method 'Return' on enum MirTerminator`
in the files whose bodies did run.

## Scenarios

### MirTerminator variant naming

#### declares Ret and does not declare Return

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- declares Ret and does not declare Return
   - Expected: source does not contain `    Return(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("declares Ret and does not declare Return")
val source = read("src/compiler/50.mir/mir_instruction_support.spl")

expect(source).to_contain("enum MirTerminator:")
expect(source).to_contain("Ret(value: MirOperand?)")
expect(source.contains("    Return(")).to_equal(false)
```

</details>

#### is not referenced as MirTerminator.Return by any previously affected spec

- is not referenced as MirTerminator.Return by any previously affected spec
   - Expected: source contains `MirTerminator.`
   - Expected: source does not contain `MirTerminator.Return`


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("is not referenced as MirTerminator.Return by any previously affected spec")
val affected = [
    "test/03_system/feature/compiler/mir_complex_spec.spl",
    "test/03_system/feature/compiler/mir_native_spec.spl",
    "test/03_system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl",
    "test/system/app/compiler/feature/optimization_plugin_jit_hotspot_system_spec.spl",
    "test/integration/compiler/vhdl_backend_e2e_spec.spl"
]

var i = 0
while i < affected.len():
    val path = affected[i]
    val source = read(path)
    # Guard against a vacuous pass if the file is ever moved away.
    expect(source.contains("MirTerminator.")).to_equal(true)
    expect(source.contains("MirTerminator.Return")).to_equal(false)
    i = i + 1
```

</details>

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `71e43a9fc74ed7e473b50faf4cfa9c1a938c5fb3f561023632f3be97ea0016b7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `71e43a9fc74ed7e473b50faf4cfa9c1a938c5fb3f561023632f3be97ea0016b7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `71e43a9fc74ed7e473b50faf4cfa9c1a938c5fb3f561023632f3be97ea0016b7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/mir_terminator_variant_name_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/mir_terminator_variant_name_spec.md (current)
findings: 5 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=84; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/mir_terminator_variant_name_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/mir_terminator_variant_name_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/mir_terminator_variant_name_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/mir_terminator_variant_name_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'declares Ret and does not declare Return' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/mir/mir_terminator_variant_name_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'is not referenced as MirTerminator.Return by any previously affected spec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
