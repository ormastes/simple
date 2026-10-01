# Import Syntax Specification

> Tests covering Import Syntax for mod.spl Files.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import Syntax Specification

## Scenarios

### Import Syntax for mod.spl Files

#### Curly braces syntax: use app.io.{...}

#### imports env_get with curly braces

- imports env_get with curly braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("imports env_get with curly braces")
val result = env_get("PATH")
expect result.len() > 0
```

</details>

#### imports env_set with curly braces

- imports env_set with curly braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("imports env_set with curly braces")
val result = env_set("TEST_VAR_CURLY", "test")
expect result == true
```

</details>

#### imports shell with curly braces

- imports shell with curly braces


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("imports shell with curly braces")
val result = shell("echo test")
expect result.exit_code == 0
```

</details>

#### Parentheses syntax: use app.io.mod (...)

#### imports file_exists with parentheses

- imports file_exists with parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("imports file_exists with parentheses")
val result = file_exists("test/02_integration/compiler/import_syntax_spec.spl")
expect result == true
```

</details>

#### imports cwd with parentheses

- imports cwd with parentheses


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("imports cwd with parentheses")
val result = cwd()
expect result.len() > 0
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/02_integration/compiler/import_syntax_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Import Syntax for mod.spl Files.
- Import Syntax for mod.spl Files

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

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `579a29614678a6360533807a2ea0b60f0247a5303d33b30ba511a9662cf85e0e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `579a29614678a6360533807a2ea0b60f0247a5303d33b30ba511a9662cf85e0e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `579a29614678a6360533807a2ea0b60f0247a5303d33b30ba511a9662cf85e0e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/02_integration/compiler/import_syntax_spec.spl
mirror: doc/06_spec/02_integration/compiler/import_syntax_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/compiler/import_syntax_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/compiler/import_syntax_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/compiler/import_syntax_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports env_get with curly braces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/import_syntax_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports env_set with curly braces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/compiler/import_syntax_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'imports shell with curly braces' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
