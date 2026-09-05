# Auto Defer Specification

> Tests covering WI-5: Auto-defer pass file exists, WI-5: Auto-defer data structures, WI-5: Resource trait detection, WI-5: Scope analysis, WI-5: Auto-defer analysis pass, WI-5: Exports.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Auto Defer Specification

## Scenarios

### WI-5: Auto-defer pass file exists

#### auto_defer.spl exists in semantics directory

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- auto_defer.spl exists in semantics directory


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto_defer.spl exists in semantics directory")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.len()).to_be_greater_than(0)
```

</details>

### WI-5: Auto-defer data structures

#### AutoDeferCandidate struct defined

- AutoDeferCandidate struct defined
   - Expected: content contains `struct AutoDeferCandidate`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AutoDeferCandidate struct defined")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("struct AutoDeferCandidate")).to_equal(true)
```

</details>

#### AutoDeferCandidate has var_name field

- AutoDeferCandidate has var_name field
   - Expected: content contains `var_name: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AutoDeferCandidate has var_name field")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("var_name: text")).to_equal(true)
```

</details>

#### AutoDeferCandidate has type_name field

- AutoDeferCandidate has type_name field
   - Expected: content contains `type_name: text`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AutoDeferCandidate has type_name field")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("type_name: text")).to_equal(true)
```

</details>

#### AutoDeferCandidate has has_manual_defer field

- AutoDeferCandidate has has_manual_defer field
   - Expected: content contains `has_manual_defer: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AutoDeferCandidate has has_manual_defer field")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("has_manual_defer: bool")).to_equal(true)
```

</details>

#### AutoDeferCandidate has no_auto_defer annotation field

- AutoDeferCandidate has no_auto_defer annotation field
   - Expected: content contains `has_no_auto_defer_annotation: bool`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AutoDeferCandidate has no_auto_defer annotation field")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("has_no_auto_defer_annotation: bool")).to_equal(true)
```

</details>

#### AutoDeferResult struct defined

- AutoDeferResult struct defined
   - Expected: content contains `struct AutoDeferResult`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("AutoDeferResult struct defined")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("struct AutoDeferResult")).to_equal(true)
```

</details>

### WI-5: Resource trait detection

#### is_resource_type function defined

- is_resource_type function defined
   - Expected: content contains `fn is_resource_type`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("is_resource_type function defined")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn is_resource_type")).to_equal(true)
```

</details>

#### checks for Resource trait

- checks for Resource trait
   - Expected: content contains `"Resource"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks for Resource trait")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("\"Resource\"")).to_equal(true)
```

</details>

#### checks for Closeable trait

- checks for Closeable trait
   - Expected: content contains `"Closeable"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks for Closeable trait")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("\"Closeable\"")).to_equal(true)
```

</details>

#### checks for AutoCloseable trait

- checks for AutoCloseable trait
   - Expected: content contains `"AutoCloseable"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("checks for AutoCloseable trait")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("\"AutoCloseable\"")).to_equal(true)
```

</details>

#### has_close_method function defined

- has_close_method function defined
   - Expected: content contains `fn has_close_method`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_close_method function defined")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn has_close_method")).to_equal(true)
```

</details>

### WI-5: Scope analysis

#### find_deferred_vars function defined

- find_deferred_vars function defined
   - Expected: content contains `fn find_deferred_vars`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find_deferred_vars function defined")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn find_deferred_vars")).to_equal(true)
```

</details>

#### parses defer x.close() pattern

- parses defer x.close() pattern
   - Expected: content contains `starts_with("defer ")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses defer x.close() pattern")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("starts_with(\"defer \")")).to_equal(true)
```

</details>

#### has_no_auto_defer_annotation function defined

- has_no_auto_defer_annotation function defined
   - Expected: content contains `fn has_no_auto_defer_annotation`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has_no_auto_defer_annotation function defined")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn has_no_auto_defer_annotation")).to_equal(true)
```

</details>

### WI-5: Auto-defer analysis pass

#### auto_defer_analyze function defined

- auto_defer_analyze function defined
   - Expected: content contains `fn auto_defer_analyze`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto_defer_analyze function defined")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn auto_defer_analyze")).to_equal(true)
```

</details>

#### auto_defer_generate_stmts function defined

- auto_defer_generate_stmts function defined
   - Expected: content contains `fn auto_defer_generate_stmts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto_defer_generate_stmts function defined")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("fn auto_defer_generate_stmts")).to_equal(true)
```

</details>

#### generates defer var.close() statements

- generates defer var.close() statements
   - Expected: content contains `.var_name}.close()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generates defer var.close() statements")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
# Checks that the generated statement includes .close()
expect(content.contains(".var_name}.close()")).to_equal(true)
```

</details>

### WI-5: Exports

#### exports data structures

- exports data structures
   - Expected: content contains `pub struct AutoDeferCandidate`
   - Expected: content contains `pub struct AutoDeferResult`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports data structures")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("pub struct AutoDeferCandidate")).to_equal(true)
expect(content.contains("pub struct AutoDeferResult")).to_equal(true)
```

</details>

#### exports analysis functions

- exports analysis functions
   - Expected: content contains `pub fn auto_defer_analyze`
   - Expected: content contains `pub fn auto_defer_generate_stmts`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports analysis functions")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("pub fn auto_defer_analyze")).to_equal(true)
expect(content.contains("pub fn auto_defer_generate_stmts")).to_equal(true)
```

</details>

#### exports detection functions

- exports detection functions
   - Expected: content contains `pub fn is_resource_type`
   - Expected: content contains `pub fn has_close_method`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("exports detection functions")
val content = rt_file_read_text("src/compiler/35.semantics/auto_defer.spl") ?? ""
expect(content.contains("pub fn is_resource_type")).to_equal(true)
expect(content.contains("pub fn has_close_method")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/semantics/auto_defer_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering WI-5: Auto-defer pass file exists, WI-5: Auto-defer data structures, WI-5: Resource trait detection, WI-5: Scope analysis, WI-5: Auto-defer analysis pass, WI-5: Exports.
- WI-5: Auto-defer pass file exists
- WI-5: Auto-defer data structures
- WI-5: Resource trait detection
- WI-5: Scope analysis
- WI-5: Auto-defer analysis pass
- WI-5: Exports

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `e82ac2fd61fc29e26fe90155e381bfe27ec65fd4edaba6012348ea4fee094965`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e82ac2fd61fc29e26fe90155e381bfe27ec65fd4edaba6012348ea4fee094965`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e82ac2fd61fc29e26fe90155e381bfe27ec65fd4edaba6012348ea4fee094965`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/semantics/auto_defer_spec.spl
mirror: doc/06_spec/unit/compiler/semantics/auto_defer_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/semantics/auto_defer_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/semantics/auto_defer_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/semantics/auto_defer_spec.spl:16:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'auto_defer.spl exists in semantics directory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/auto_defer_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AutoDeferCandidate struct defined' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/semantics/auto_defer_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'AutoDeferCandidate has var_name field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
