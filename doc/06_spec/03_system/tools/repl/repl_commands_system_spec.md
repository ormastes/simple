# Repl Commands System Specification

> Tests covering REPL Commands.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Repl Commands System Specification

## Scenarios

### REPL Commands

<details>
<summary>Advanced: should handle :quit</summary>

#### should handle :quit _(slow)_

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should handle :quit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle :quit")
val output = run_repl(":quit\n")
expect(output).to_contain("Goodbye")
```

</details>


</details>

<details>
<summary>Advanced: should handle :q shorthand</summary>

#### should handle :q shorthand _(slow)_

- should handle :q shorthand


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle :q shorthand")
val output = run_repl(":q\n")
expect(output).to_contain("Goodbye")
```

</details>


</details>

<details>
<summary>Advanced: should handle :clear</summary>

#### should handle :clear _(slow)_

- should handle :clear


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle :clear")
val output = run_repl(":clear\n:quit\n")
expect(output).to_contain("State cleared")
```

</details>


</details>

<details>
<summary>Advanced: should handle :history</summary>

#### should handle :history _(slow)_

- should handle :history


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle :history")
val output = run_repl("val x = 1\n:history\n:quit\n")
expect(output).to_contain("val x = 1")
```

</details>


</details>

<details>
<summary>Advanced: should handle :show</summary>

#### should handle :show _(slow)_

- should handle :show


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle :show")
val output = run_repl("val x = 1\n:show\n:quit\n")
expect(output).to_contain("val x = 1")
```

</details>


</details>

<details>
<summary>Advanced: should handle exit() function call</summary>

#### should handle exit() function call _(slow)_

- should handle exit() function call


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should handle exit() function call")
val output = run_repl("exit()\n")
expect(output).to_contain("Goodbye")
```

</details>


</details>

<details>
<summary>Advanced: should terminate on EOF</summary>

#### should terminate on EOF _(slow)_

- should terminate on EOF
   - Expected: code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should terminate on EOF")
val (stdout, stderr, code) = process_run("bash", ["-c", "echo '' | " + find_simple_binary() + " run src/app/repl/main.spl 2>/dev/null"])
expect(code).to_equal(0)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/repl/repl_commands_system_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering REPL Commands.
- REPL Commands

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 7 |
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

- Canonical SPipe generation for source `8b1c58ac7b051d3971040b7e6d9ffa01ebbf3e2e7aca97c3628496b9d21a0240`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8b1c58ac7b051d3971040b7e6d9ffa01ebbf3e2e7aca97c3628496b9d21a0240`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8b1c58ac7b051d3971040b7e6d9ffa01ebbf3e2e7aca97c3628496b9d21a0240`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/tools/repl/repl_commands_system_spec.spl
mirror: doc/06_spec/03_system/tools/repl/repl_commands_system_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/repl/repl_commands_system_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/repl/repl_commands_system_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/repl/repl_commands_system_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/tools/repl/repl_commands_system_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle :quit' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/repl/repl_commands_system_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle :quit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/repl/repl_commands_system_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle :q shorthand' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/repl/repl_commands_system_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle :q shorthand' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/repl/repl_commands_system_spec.spl:56:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle :clear' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/repl/repl_commands_system_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should handle :clear' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/repl/repl_commands_system_spec.spl:62:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle :history' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/repl/repl_commands_system_spec.spl:68:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle :show' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/repl/repl_commands_system_spec.spl:74:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should handle exit() function call' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
