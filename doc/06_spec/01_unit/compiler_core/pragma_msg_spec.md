# Pragma Msg Specification

> Tests covering pragma_msg Built-in.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Pragma Msg Specification

## Scenarios

### pragma_msg Built-in

#### should expose pragma_msg as an interpreter builtin

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should expose pragma_msg as an interpreter builtin
   - Expected: src contains `if name == "pragma_msg":`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should expose pragma_msg as an interpreter builtin")
val src = builtins_source()
# Anchored to the real dispatch branch; the "# pragma_msg(expr) —"
# header comment must not be able to satisfy this.
expect(src.contains("if name == \"pragma_msg\":")).to_equal(true)
```

</details>

#### should evaluate its first argument before printing

- should evaluate its first argument before printing
   - Expected: src contains `if arg_eids.len() > 0`
   - Expected: src contains `val pm_val = eval_expr(arg_eids[0])`
   - Expected: src contains `if eval_had_error: return -1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should evaluate its first argument before printing")
val src = builtins_source()
expect(src.contains("if arg_eids.len() > 0")).to_equal(true)
expect(src.contains("val pm_val = eval_expr(arg_eids[0])")).to_equal(true)
expect(src.contains("if eval_had_error: return -1")).to_equal(true)
```

</details>

#### should print the argument text and return nil

- should print the argument text and return nil
   - Expected: src contains `print val_to_text(pm_val)`
   - Expected: src contains `return val_make_nil()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER_CORE
step("should print the argument text and return nil")
val src = builtins_source()
expect(src.contains("print val_to_text(pm_val)")).to_equal(true)
expect(src.contains("return val_make_nil()")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler_core/pragma_msg_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering pragma_msg Built-in.
- pragma_msg Built-in

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

- `REQ-SSPEC-COMPILER_CORE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `717aca263cd9cf7e35c054f494edae0e76793234917ff3ab01d5ea81322fa5a9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `717aca263cd9cf7e35c054f494edae0e76793234917ff3ab01d5ea81322fa5a9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `717aca263cd9cf7e35c054f494edae0e76793234917ff3ab01d5ea81322fa5a9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/compiler_core/pragma_msg_spec.spl
mirror: doc/06_spec/01_unit/compiler_core/pragma_msg_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler_core/pragma_msg_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler_core/pragma_msg_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler_core/pragma_msg_spec.spl:14:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should expose pragma_msg as an interpreter builtin' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/pragma_msg_spec.spl:14:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should expose pragma_msg as an interpreter builtin' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/pragma_msg_spec.spl:22:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should evaluate its first argument before printing' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/pragma_msg_spec.spl:22:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should evaluate its first argument before printing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler_core/pragma_msg_spec.spl:30:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should print the argument text and return nil' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/compiler_core/pragma_msg_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should print the argument text and return nil' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
