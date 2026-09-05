# Star Export Lint Specification

> Tests covering Star export lint (W0407).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Star Export Lint Specification

## Scenarios

### Star export lint (W0407)

#### star_import.spl contains check_star_export function

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- star_import.spl contains check_star_export function
   - Expected: source contains `fn check_star_export(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("star_import.spl contains check_star_export function")
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("fn check_star_export(")).to_equal(true)
```

</details>

#### detects wildcard via ends_with check

- detects wildcard via ends_with check
   - Expected: source contains `ends_with(".*")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detects wildcard via ends_with check")
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("ends_with(\".*\")")).to_equal(true)
```

</details>

#### emits W0407 code

- emits W0407 code
   - Expected: source contains `"W0407"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits W0407 code")
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("\"W0407\"")).to_equal(true)
```

</details>

#### has facade exemption for __init__.spl

- has facade exemption for __init__.spl
   - Expected: source contains `__init__.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has facade exemption for __init__.spl")
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("__init__.spl")).to_equal(true)
```

</details>

#### has facade exemption for mod.spl

- has facade exemption for mod.spl
   - Expected: source contains `mod.spl`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has facade exemption for mod.spl")
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("mod.spl")).to_equal(true)
```

</details>

#### strips .* suffix to get module_path

- strips .* suffix to get module_path
   - Expected: source contains `n.slice(0, n.len() - 2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("strips .* suffix to get module_path")
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("n.slice(0, n.len() - 2)")).to_equal(true)
```

</details>

#### uses unified StarWildcardWarning struct

- uses unified StarWildcardWarning struct
   - Expected: source contains `struct StarWildcardWarning:`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses unified StarWildcardWarning struct")
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("struct StarWildcardWarning:")).to_equal(true)
```

</details>

#### has shared _is_facade_file helper

- has shared _is_facade_file helper
   - Expected: source contains `fn _is_facade_file(`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has shared _is_facade_file helper")
val source = read_file("src/compiler/35.semantics/lint/star_import.spl")
expect(source.contains("fn _is_facade_file(")).to_equal(true)
```

</details>

#### is registered in __init__.spl

- is registered in __init__.spl
   - Expected: source contains `export check_star_export, check_star_export_file`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is registered in __init__.spl")
val source = read_file("src/compiler/35.semantics/lint/__init__.spl")
expect(source.contains("export check_star_export, check_star_export_file")).to_equal(true)
```

</details>

#### is integrated in query_lint.spl

- is integrated in query_lint.spl
   - Expected: source contains `check_star_export_file}`
   - Expected: source contains `val star_export_warnings = check_star_export_file(decl_indices, file)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is integrated in query_lint.spl")
val source = read_file("src/app/cli/query_lint.spl")
# Anchored to the real import and the real call site; the
# "# --- C5a/C5c: Star wildcard warnings ---" banner comment must not
# be able to satisfy this on its own.
expect(source.contains("check_star_export_file}")).to_equal(true)
expect(source.contains("val star_export_warnings = check_star_export_file(decl_indices, file)")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/lint/star_export_lint_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Star export lint (W0407).
- Star export lint (W0407)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
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

- Canonical SPipe generation for source `e404667fedf5f350203014f019fcf81359badf7267f59c18e52ea073a9bf2823`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e404667fedf5f350203014f019fcf81359badf7267f59c18e52ea073a9bf2823`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e404667fedf5f350203014f019fcf81359badf7267f59c18e52ea073a9bf2823`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/compiler/lint/star_export_lint_spec.spl
mirror: doc/06_spec/unit/compiler/lint/star_export_lint_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=50
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/compiler/lint/star_export_lint_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/lint/star_export_lint_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/lint/star_export_lint_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/unit/compiler/lint/star_export_lint_spec.spl:12:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'star_import.spl contains check_star_export function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint/star_export_lint_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'detects wildcard via ends_with check' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/lint/star_export_lint_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits W0407 code' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
