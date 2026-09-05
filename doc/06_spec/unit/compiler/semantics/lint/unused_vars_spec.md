# Unused Vars Specification

> Tests covering Unused Variables Lint.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unused Vars Specification

## Scenarios

### Unused Variables Lint

#### used variables

#### does not flag variables that are used

- does not flag variables that are used
   - Expected: mentions_x is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag variables that are used")
val code = "fn compute() -> i64:\n    val x = 10\n    val y = 20\n    x + y\n"
val unused = check_unused_vars_text(code)
val mentions_x = names_contain(unused, "x")
expect(mentions_x).to_equal(false)
```

</details>

#### does not flag variables used in print

- does not flag variables used in print
   - Expected: mentions_greeting is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag variables used in print")
val code = "fn greet():\n    val greeting = \"Hello\"\n    print greeting\n"
val unused = check_unused_vars_text(code)
val mentions_greeting = names_contain(unused, "greeting")
expect(mentions_greeting).to_equal(false)
```

</details>

#### unused variables

#### flags unused val declarations

- flags unused val declarations
   - Expected: mentions_unused is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags unused val declarations")
val code = "fn test():\n    val unused_val = 42\n    print \"done\"\n"
val unused = check_unused_vars_text(code)
val mentions_unused = names_contain(unused, "unused_val")
expect(mentions_unused).to_equal(true)
```

</details>

#### flags unused var declarations

- flags unused var declarations
   - Expected: mentions_unused is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flags unused var declarations")
val code = "fn test():\n    var unused_var = 0\n    print \"done\"\n"
val unused = check_unused_vars_text(code)
val mentions_unused = names_contain(unused, "unused_var")
expect(mentions_unused).to_equal(true)
```

</details>

#### underscore-prefixed variables

#### does not flag _prefixed variables

- does not flag _prefixed variables
   - Expected: mentions_ignored is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag _prefixed variables")
val code = "fn test():\n    val _ignored = 42\n    print \"done\"\n"
val unused = check_unused_vars_text(code)
val mentions_ignored = names_contain(unused, "_ignored")
expect(mentions_ignored).to_equal(false)
```

</details>

#### does not flag single underscore

- does not flag single underscore
   - Expected: mentions_underscore is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not flag single underscore")
val code = "fn test():\n    val _ = 42\n    print \"done\"\n"
val unused = check_unused_vars_text(code)
val mentions_underscore = names_contain(unused, "_")
expect(mentions_underscore).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/lint/unused_vars_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Unused Variables Lint.
- Unused Variables Lint

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
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

- Canonical SPipe generation for source `3ca58abcc9a2fd062184894692d7e4be043595869293e67e9bbe75c7310d5ae7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3ca58abcc9a2fd062184894692d7e4be043595869293e67e9bbe75c7310d5ae7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3ca58abcc9a2fd062184894692d7e4be043595869293e67e9bbe75c7310d5ae7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/semantics/lint/unused_vars_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/lint/unused_vars_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/lint/unused_vars_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/lint/unused_vars_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/lint/unused_vars_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag variables that are used' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/lint/unused_vars_spec.spl:151:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not flag variables used in print' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/lint/unused_vars_spec.spl:160:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'flags unused val declarations' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
