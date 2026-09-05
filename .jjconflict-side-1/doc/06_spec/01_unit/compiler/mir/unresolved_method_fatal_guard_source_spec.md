# Unresolved Method Fatal Guard Source Specification

> Tests covering unresolved MIR method fail-fast guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unresolved Method Fatal Guard Source Specification

## Scenarios

### unresolved MIR method fail-fast guard

#### marks unresolved method placeholders fatal before bootstrap codegen

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- marks unresolved method placeholders fatal before bootstrap codegen
   - Expected: source does not contain `old_nonfatal_call`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("marks unresolved method placeholders fatal before bootstrap codegen")
val source = read_source("src/compiler/50.mir/_MirLoweringExpr/method_calls_literals.spl")
val fatal_call = "self.error_fatal(\"unresolved method call: {method}\", nil)"
val old_nonfatal_call = "self.error(\"unresolved method call: {method}\", nil)"
val panic_call = "b.emit_call(panic_op, [mir_operand_copy(panic_msg)], MirType.unit())"
val unreachable_const = "b.emit_const(temp, MirConstValue.Int(0), MirType.i64())"

val fatal_pos = source.index_of(fatal_call)
val panic_pos = source.index_of(panic_call)
val const_pos = source.index_of(unreachable_const)

expect(source).to_contain(fatal_call)
expect(source.contains(old_nonfatal_call)).to_equal(false)
expect(fatal_pos).to_be_greater_than(-1)
expect(fatal_pos).to_be_less_than(panic_pos)
expect(panic_pos).to_be_less_than(const_pos)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/mir/unresolved_method_fatal_guard_source_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering unresolved MIR method fail-fast guard.
- unresolved MIR method fail-fast guard

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

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f506de46f9914c211f84ee8ad554360d131a7794a34438a4409a3666be8059c8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f506de46f9914c211f84ee8ad554360d131a7794a34438a4409a3666be8059c8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f506de46f9914c211f84ee8ad554360d131a7794a34438a4409a3666be8059c8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/mir/unresolved_method_fatal_guard_source_spec.spl
mirror: doc/06_spec/01_unit/compiler/mir/unresolved_method_fatal_guard_source_spec.md (current)
findings: 4 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=85; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/mir/unresolved_method_fatal_guard_source_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/mir/unresolved_method_fatal_guard_source_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/mir/unresolved_method_fatal_guard_source_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/mir/unresolved_method_fatal_guard_source_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'marks unresolved method placeholders fatal before bootstrap codegen' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
