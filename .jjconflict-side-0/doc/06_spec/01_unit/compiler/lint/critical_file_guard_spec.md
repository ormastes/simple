# Critical File Guard Specification

> Tests covering Critical file guard lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Critical File Guard Specification

## Scenarios

### Critical file guard lint

#### config/critical_files.sdn exists

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- config/critical_files.sdn exists
   - Expected: file_exists("config/critical_files.sdn") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("config/critical_files.sdn exists")
expect(file_exists("config/critical_files.sdn")).to_equal(true)
```

</details>

#### config has entries section

- config has entries section
   - Expected: content contains `entries:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("config has entries section")
val content = read_file("config/critical_files.sdn")
expect(content.contains("entries:")).to_equal(true)
```

</details>

#### config protects star_import.spl

- config protects star_import.spl
   - Expected: content contains `src/compiler/35.semantics/lint/star_import.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("config protects star_import.spl")
val content = read_file("config/critical_files.sdn")
expect(content.contains("src/compiler/35.semantics/lint/star_import.spl")).to_equal(true)
```

</details>

#### config protects error.spl

- config protects error.spl
   - Expected: content contains `src/compiler/00.common/error.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("config protects error.spl")
val content = read_file("config/critical_files.sdn")
expect(content.contains("src/compiler/00.common/error.spl")).to_equal(true)
```

</details>

#### config protects itself

- config protects itself
   - Expected: content contains `config/critical_files.sdn`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("config protects itself")
val content = read_file("config/critical_files.sdn")
expect(content.contains("config/critical_files.sdn")).to_equal(true)
```

</details>

#### guard module has CFG001 deletion check

- guard module has CFG001 deletion check
   - Expected: source contains `"CFG001"`
   - Expected: source contains `critical file deleted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("guard module has CFG001 deletion check")
val source = read_file("src/compiler/35.semantics/lint/critical_file_guard.spl")
expect(source.contains("\"CFG001\"")).to_equal(true)
expect(source.contains("critical file deleted")).to_equal(true)
```

</details>

#### guard module has CFG002 shrinkage check

- guard module has CFG002 shrinkage check
   - Expected: source contains `"CFG002"`
   - Expected: source contains `shrunk below`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("guard module has CFG002 shrinkage check")
val source = read_file("src/compiler/35.semantics/lint/critical_file_guard.spl")
expect(source.contains("\"CFG002\"")).to_equal(true)
expect(source.contains("shrunk below")).to_equal(true)
```

</details>

#### guard is registered in __init__.spl

- guard is registered in __init__.spl
   - Expected: source contains `export critical_file_guard.*`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("guard is registered in __init__.spl")
val source = read_file("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("export critical_file_guard.*")).to_equal(true)
```

</details>

#### guard is integrated in query_lint.spl

- guard is integrated in query_lint.spl
   - Expected: source contains `check_all_critical_files`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("guard is integrated in query_lint.spl")
val source = read_file("src/app/cli/query_lint.spl")
expect(source.contains("check_all_critical_files")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/lint/critical_file_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Critical file guard lint.
- Critical file guard lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7b5b1d331e7fc4a184eb4ed4e7e140a5e6723bb532ff4466eefac0eaa9d312d1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7b5b1d331e7fc4a184eb4ed4e7e140a5e6723bb532ff4466eefac0eaa9d312d1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7b5b1d331e7fc4a184eb4ed4e7e140a5e6723bb532ff4466eefac0eaa9d312d1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/compiler/lint/critical_file_guard_spec.spl
mirror: doc/06_spec/01_unit/compiler/lint/critical_file_guard_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/compiler/lint/critical_file_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/lint/critical_file_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/lint/critical_file_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/compiler/lint/critical_file_guard_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/compiler/lint/critical_file_guard_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'config/critical_files.sdn exists' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/critical_file_guard_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'config has entries section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/lint/critical_file_guard_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'config protects star_import.spl' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
