# Skip Keyword - Basic Functionality

> Tests basic parsing and runtime behavior of the `skip` keyword as a standalone statement. Verifies that skip can be used in various contexts (if blocks, function bodies, loops), that it does not prevent subsequent code execution, does not affect return values, and does not alter variable scope.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Skip Keyword - Basic Functionality

Tests basic parsing and runtime behavior of the `skip` keyword as a standalone statement. Verifies that skip can be used in various contexts (if blocks, function bodies, loops), that it does not prevent subsequent code execution, does not affect return values, and does not alter variable scope.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #PARSER-002 |
| Category | Syntax |
| Status | Active |
| Source | `test/feature/usage/parser_skip_basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests basic parsing and runtime behavior of the `skip` keyword as a standalone
statement. Verifies that skip can be used in various contexts (if blocks,
function bodies, loops), that it does not prevent subsequent code execution,
does not affect return values, and does not alter variable scope.

## Syntax

```simple
skip
use std.spec.step

fn test_function():
skip
return "completed"
```

## Scenarios

### Skip keyword - basic functionality

#### parses skip as standalone statement

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses skip as standalone statement


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses skip as standalone statement")
var executed = true
skip
expect executed == true
```

</details>

#### parses skip with pass

- parses skip with pass


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses skip with pass")
skip
pass
expect true
```

</details>

#### parses skip in if block

- parses skip in if block


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses skip in if block")
val condition = true
if condition:
    skip
expect true
```

</details>

#### parses skip in function body

- parses skip in function body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses skip in function body")
fn test_function():
    skip
    return "completed"
expect test_function() == "completed"
```

</details>

#### parses multiple skip statements

- parses multiple skip statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses multiple skip statements")
skip
skip
skip
expect true
```

</details>

#### parses skip before expression

- parses skip before expression


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses skip before expression")
skip
val result = 2 + 2
expect result == 4
```

</details>

<details>
<summary>Advanced: parses skip in loop</summary>

#### parses skip in loop

- parses skip in loop


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("parses skip in loop")
var count = 0
for i in 0..3:
    skip
    count = count + 1
expect count == 3
```

</details>


</details>

#### skip does not prevent execution

- skip does not prevent execution


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skip does not prevent execution")
var executed = false
skip
executed = true
expect executed == true
```

</details>

#### skip does not affect return value

- skip does not affect return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skip does not affect return value")
fn returns_with_skip():
    skip
    return "value"
expect returns_with_skip() == "value"
```

</details>

#### skip does not affect variable scope

- skip does not affect variable scope


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("skip does not affect variable scope")
skip
val scoped = 100
expect scoped == 100
```

</details>

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

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4e66deb12ce302468e85c9fbd13c264d11292b5425d523170185d15583b43ba0`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4e66deb12ce302468e85c9fbd13c264d11292b5425d523170185d15583b43ba0`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4e66deb12ce302468e85c9fbd13c264d11292b5425d523170185d15583b43ba0`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/feature/usage/parser_skip_basic_spec.spl
mirror: doc/06_spec/feature/usage/parser_skip_basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/parser_skip_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/parser_skip_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/parser_skip_basic_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses skip as standalone statement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_skip_basic_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses skip with pass' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/parser_skip_basic_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses skip in if block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
