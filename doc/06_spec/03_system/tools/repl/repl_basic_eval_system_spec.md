# Repl Basic Eval System Specification

> Tests covering REPL Basic Evaluation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Repl Basic Eval System Specification

## Scenarios

### REPL Basic Evaluation

<details>
<summary>Advanced: should show banner on startup</summary>

#### should show banner on startup _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should show banner on startup


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should show banner on startup")
val output = run_repl(":quit\n")
expect(output).to_contain("Simple Language REPL")
```

</details>


</details>

<details>
<summary>Advanced: should evaluate print statements</summary>

#### should evaluate print statements _(slow)_

- should evaluate print statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should evaluate print statements")
val output = run_repl("print \"hello world\"\n:quit\n")
expect(output).to_contain("hello world")
```

</details>


</details>

<details>
<summary>Advanced: should exit on quit command</summary>

#### should exit on quit command _(slow)_

- should exit on quit command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should exit on quit command")
val output = run_repl(":quit\n")
expect(output).to_contain("Goodbye")
```

</details>


</details>

<details>
<summary>Advanced: should exit on exit command</summary>

#### should exit on exit command _(slow)_

- should exit on exit command


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should exit on exit command")
val output = run_repl("exit\n")
expect(output).to_contain("Goodbye")
```

</details>


</details>

<details>
<summary>Advanced: should show help</summary>

#### should show help _(slow)_

- should show help


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should show help")
val output = run_repl(":help\n:quit\n")
expect(output).to_contain("Commands")
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/repl/repl_basic_eval_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REPL Basic Evaluation.
- REPL Basic Evaluation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 5 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b83ae005f8800f1ffc41f19d9fdb854be471491f7a502365589c50c909ca7843`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b83ae005f8800f1ffc41f19d9fdb854be471491f7a502365589c50c909ca7843`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b83ae005f8800f1ffc41f19d9fdb854be471491f7a502365589c50c909ca7843`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/repl/repl_basic_eval_system_spec.spl
mirror: doc/06_spec/03_system/tools/repl/repl_basic_eval_system_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=75 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/repl/repl_basic_eval_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/repl/repl_basic_eval_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/repl/repl_basic_eval_system_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should show banner on startup' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/repl/repl_basic_eval_system_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should show banner on startup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/repl/repl_basic_eval_system_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should evaluate print statements' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/repl/repl_basic_eval_system_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should evaluate print statements' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/repl/repl_basic_eval_system_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exit on quit command' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/repl/repl_basic_eval_system_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should exit on quit command' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/repl/repl_basic_eval_system_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should exit on exit command' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/repl/repl_basic_eval_system_spec.spl:72:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should show help' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
