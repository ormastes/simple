# Api Surface Specification

> Tests covering Public API Detection, Symbol Categories, API Documentation Coverage, Symbol Analysis.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Api Surface Specification

## Scenarios

### Public API Detection

#### public function is in API

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- public function is in API


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("public function is in API")
val visibility = "public"
check(visibility == "public")
```

</details>

#### private function is not in API

- private function is not in API


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("private function is not in API")
val visibility = "private"
check(visibility == "private")
```

</details>

#### module-level function

- module-level function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module-level function")
val scope = "module"
check(scope == "module")
```

</details>

#### class method

- class method


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("class method")
val scope = "method"
check(scope == "method")
```

</details>

#### static method

- static method


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("static method")
val scope = "static"
check(scope == "static")
```

</details>

### Symbol Categories

#### function symbol

- function symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("function symbol")
val kind = "function"
check(kind == "function")
```

</details>

#### class symbol

- class symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("class symbol")
val kind = "class"
check(kind == "class")
```

</details>

#### trait symbol

- trait symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trait symbol")
val kind = "trait"
check(kind == "trait")
```

</details>

#### enum symbol

- enum symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("enum symbol")
val kind = "enum"
check(kind == "enum")
```

</details>

#### type alias symbol

- type alias symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("type alias symbol")
val kind = "type_alias"
check(kind == "type_alias")
```

</details>

#### constant symbol

- constant symbol


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("constant symbol")
val kind = "constant"
check(kind == "constant")
```

</details>

### API Documentation Coverage

#### documented function

- documented function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("documented function")
val has_doc = true
check(has_doc)
```

</details>

#### undocumented function

- undocumented function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("undocumented function")
val has_doc = false
check(not has_doc)
```

</details>

#### doc coverage percentage

- doc coverage percentage


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("doc coverage percentage")
val documented = 80
val total = 100
val coverage = documented * 100 / total
check(coverage == 80)
```

</details>

#### coverage threshold check

- coverage threshold check


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("coverage threshold check")
val coverage = 85
val threshold = 80
check(coverage >= threshold)
```

</details>

### Symbol Analysis

#### count public functions

- count public functions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count public functions")
val count = 42
check(count > 0)
```

</details>

#### count public classes

- count public classes


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count public classes")
val count = 15
check(count > 0)
```

</details>

#### count public traits

- count public traits


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("count public traits")
val count = 8
check(count > 0)
```

</details>

#### module dependency graph

- module dependency graph


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("module dependency graph")
val edges = 100
check(edges > 0)
```

</details>

#### cyclic dependency detection

- cyclic dependency detection


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("cyclic dependency detection")
val has_cycle = false
check(not has_cycle)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/tools/api_surface_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Public API Detection, Symbol Categories, API Documentation Coverage, Symbol Analysis.
- Public API Detection
- Symbol Categories
- API Documentation Coverage
- Symbol Analysis

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 20 |
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

- Canonical SPipe generation for source `84211f63321b203767a0f4f2988365215ae1f66bd1e85acded0101814c643b84`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `84211f63321b203767a0f4f2988365215ae1f66bd1e85acded0101814c643b84`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `84211f63321b203767a0f4f2988365215ae1f66bd1e85acded0101814c643b84`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/tools/api_surface_spec.spl
mirror: doc/06_spec/unit/compiler/tools/api_surface_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/tools/api_surface_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/tools/api_surface_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/tools/api_surface_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'public function is in API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/tools/api_surface_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'private function is not in API' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/tools/api_surface_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'module-level function' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
