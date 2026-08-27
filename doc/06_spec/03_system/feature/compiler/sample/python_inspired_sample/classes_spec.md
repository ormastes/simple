# Classes (Python-Inspired Sample)

> Tests compilation of class definitions inspired by Python patterns including fields, methods, and static methods. Verifies that Simple's composition-based class model correctly compiles constructs familiar to Python developers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Classes (Python-Inspired Sample)

Tests compilation of class definitions inspired by Python patterns including fields, methods, and static methods. Verifies that Simple's composition-based class model correctly compiles constructs familiar to Python developers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | In Progress |
| Source | `test/03_system/feature/compiler/sample/python_inspired_sample/classes_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests compilation of class definitions inspired by Python patterns including
fields, methods, and static methods. Verifies that Simple's composition-based
class model correctly compiles constructs familiar to Python developers.

## Scenarios

### Classes

#### class definition

#### defines a simple class with fields

- defines a simple class with fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines a simple class with fields")
class Point:
    x: i64
    y: i64
val p = Point(x: 3, y: 4)
expect p.x == 3
expect p.y == 4
```

</details>

#### instance methods

#### defines and calls immutable method

- defines and calls immutable method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines and calls immutable method")
class Rectangle:
    width: i64
    height: i64

    fn area() -> i64:
        self.width * self.height

val rect = Rectangle(width: 5, height: 3)
expect rect.area() == 15
```

</details>

#### mutable methods

#### modifies instance with me method

- modifies instance with me method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("modifies instance with me method")
class Counter:
    value: i64

    me increment():
        self.value = self.value + 1

var c = Counter(value: 0)
c.increment()
expect c.value == 1
```

</details>

#### static methods

#### creates instance via static factory

- creates instance via static factory


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("creates instance via static factory")
class Circle:
    radius: f64

impl Circle:
    static fn unit() -> Circle:
        Circle(radius: 1.0)

val c = Circle.unit()
expect c.radius == 1.0
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
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

- Canonical SPipe generation for source `00feb18b35e025502a426295d3d0c1a7c8371c79ef5c8995dcf9b889d1210304`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `00feb18b35e025502a426295d3d0c1a7c8371c79ef5c8995dcf9b889d1210304`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `00feb18b35e025502a426295d3d0c1a7c8371c79ef5c8995dcf9b889d1210304`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/compiler/sample/python_inspired_sample/classes_spec.spl
mirror: doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/classes_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/classes_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/compiler/sample/python_inspired_sample/classes_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/compiler/sample/python_inspired_sample/classes_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines a simple class with fields' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/classes_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines and calls immutable method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/compiler/sample/python_inspired_sample/classes_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'modifies instance with me method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
