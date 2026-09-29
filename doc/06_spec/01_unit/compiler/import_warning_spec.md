# Import Warning Specification

> Tests covering Import path warnings, Warning message content, Warning severity.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Import Warning Specification

## Scenarios

### Import path warnings

#### warns when slash is used in import path

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- warns when slash is used in import path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns when slash is used in import path")
val warnings = analyze_import_warning("use a/b\n")
check(warnings_contain(warnings, "warning[E0501]"))
```

</details>

#### provides helpful suggestion

- provides helpful suggestion


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("provides helpful suggestion")
val warnings = analyze_import_warning("use a/b\n")
check(warnings_contain(warnings, "help: use dot-separated"))
```

</details>

#### does not warn on correct absolute import

- does not warn on correct absolute import


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn on correct absolute import")
val warnings = analyze_import_warning("use compiler.parser\n")
check(warnings_contain(warnings, "absolute import ok"))
```

</details>

#### does not warn on correct relative import

- does not warn on correct relative import


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn on correct relative import")
val warnings = analyze_import_warning("use ./local/module\n")
check(warnings_contain(warnings, "relative import ok"))
```

</details>

#### does not warn on correct parent import

- does not warn on correct parent import


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not warn on correct parent import")
val warnings = analyze_import_warning("use ../parent/module\n")
check(warnings_contain(warnings, "relative import ok"))
```

</details>

#### warns on multiple slash usages

- warns on multiple slash usages


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on multiple slash usages")
val warnings = analyze_import_warning("use a/b/c\n")
check(warnings_contain(warnings, "warning[E0501]"))
```

</details>

#### warns on mixed slash and dot

- warns on mixed slash and dot


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("warns on mixed slash and dot")
val warnings = analyze_import_warning("use a/b.c\n")
check(warnings_contain(warnings, "warning[E0501]"))
```

</details>

### Warning message content

#### explains the issue

- explains the issue


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("explains the issue")
val warnings = analyze_import_warning("use a/b\n")
check(warnings_contain(warnings, "cannot import unfolded package"))
```

</details>

#### suggests dot separator

- suggests dot separator


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suggests dot separator")
val warnings = analyze_import_warning("use a/b\n")
check(warnings_contain(warnings, "dot-separated module paths"))
```

</details>

#### mentions relative paths

- mentions relative paths


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mentions relative paths")
val warnings = analyze_import_warning("use ../a/b\n")
check(warnings_contain(warnings, "relative import ok"))
```

</details>

### Warning severity

#### is a warning, not an error

- is a warning, not an error


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is a warning, not an error")
val warnings = analyze_import_warning("use a/b\n")
check(warnings.len() > 0)
```

</details>

#### allows compilation to continue

- allows compilation to continue


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allows compilation to continue")
val warnings = analyze_import_warning("use a/b\nuse compiler.parser\n")
check(warnings.len() > 0)
check(warnings_contain(warnings, "absolute import ok"))
```

</details>

#### does not prevent import resolution

- does not prevent import resolution


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not prevent import resolution")
val warnings = analyze_import_warning("use a/b\nuse compiler.parser\n")
check(warnings_contain(warnings, "warning[E0501]"))
check(warnings_contain(warnings, "absolute import ok"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/import_warning_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Import path warnings, Warning message content, Warning severity.
- Import path warnings
- Warning message content
- Warning severity

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
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

- Canonical SPipe generation for source `968be605d70fdd4aac57019069a66aa2f8d66b7b83001e75a0a132e3d3e31756`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `968be605d70fdd4aac57019069a66aa2f8d66b7b83001e75a0a132e3d3e31756`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `968be605d70fdd4aac57019069a66aa2f8d66b7b83001e75a0a132e3d3e31756`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/compiler/import_warning_spec.spl
mirror: doc/06_spec/01_unit/compiler/import_warning_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/import_warning_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/import_warning_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/import_warning_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'warns when slash is used in import path' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/import_warning_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides helpful suggestion' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/import_warning_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not warn on correct absolute import' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
