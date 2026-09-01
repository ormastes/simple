# Query Specification

> Tests covering Symbol Query, Type Query, Code Navigation, AST Query.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Query Specification

## Scenarios

### Symbol Query

#### find function by name

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- find function by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find function by name")
val name = "main"
check(name == "main")
```

</details>

#### find class by name

- find class by name


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find class by name")
val name = "Point"
check(name == "Point")
```

</details>

#### find method by class and name

- find method by class and name


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find method by class and name")
val class_name = "Point"
val method = "get_x"
check(class_name == "Point" and method == "get_x")
```

</details>

#### find symbols by pattern

- find symbols by pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find symbols by pattern")
val pattern = "parse_*"
check(pattern.starts_with("parse"))
```

</details>

#### find symbols in module

- find symbols in module


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find symbols in module")
val module = "compiler.frontend"
check(module.contains("frontend"))
```

</details>

### Type Query

#### query type of expression

- query type of expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query type of expression")
val expr_type = "i64"
check(expr_type == "i64")
```

</details>

#### query return type of function

- query return type of function


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query return type of function")
val ret_type = "text"
check(ret_type == "text")
```

</details>

#### query field types of class

- query field types of class


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query field types of class")
val fields = ["x: i64", "y: i64"]
check(fields.len() == 2)
```

</details>

#### query trait implementations

- query trait implementations


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query trait implementations")
val impls = ["Display", "Debug"]
check(impls.len() == 2)
```

</details>

### Code Navigation

#### go to definition

- go to definition


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("go to definition")
val file = "src/main.spl"
val line = 10
check(file.ends_with(".spl"))
check(line > 0)
```

</details>

#### find all references

- find all references


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find all references")
val refs = 5
check(refs > 0)
```

</details>

#### find callers

- find callers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find callers")
val callers = 3
check(callers > 0)
```

</details>

#### find callees

- find callees


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("find callees")
val callees = 2
check(callees > 0)
```

</details>

### AST Query

#### query all if expressions

- query all if expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query all if expressions")
val count = 10
check(count > 0)
```

</details>

#### query all match expressions

- query all match expressions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query all match expressions")
val count = 5
check(count > 0)
```

</details>

#### query all function definitions

- query all function definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query all function definitions")
val count = 50
check(count > 0)
```

</details>

#### query all class definitions

- query all class definitions


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query all class definitions")
val count = 20
check(count > 0)
```

</details>

#### query all use statements

- query all use statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("query all use statements")
val count = 15
check(count > 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/tools/query_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Symbol Query, Type Query, Code Navigation, AST Query.
- Symbol Query
- Type Query
- Code Navigation
- AST Query

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `b78bbca95066edcf847c3e6fdeed928b43f3b151fe3f70a020c8906930a24df7`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b78bbca95066edcf847c3e6fdeed928b43f3b151fe3f70a020c8906930a24df7`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b78bbca95066edcf847c3e6fdeed928b43f3b151fe3f70a020c8906930a24df7`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/tools/query_spec.spl
mirror: doc/06_spec/unit/compiler/tools/query_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/tools/query_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/tools/query_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/tools/query_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'find function by name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/tools/query_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'find class by name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/tools/query_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'find method by class and name' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
