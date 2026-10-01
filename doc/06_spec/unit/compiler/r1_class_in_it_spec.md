# R1 Class In It Specification

> Tests covering R1 nested class definitions.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# R1 Class In It Specification

## Scenarios

### R1 nested class definitions

#### instantiates a class defined inside the it block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- instantiates a class defined inside the it block


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("instantiates a class defined inside the it block")
class Point:
    x: i32
    y: i32

val p = Point(x: 7, y: 11)
expect p.x == 7
expect p.y == 11
```

</details>

#### calls a static factory on a class defined inside the it block

- calls a static factory on a class defined inside the it block


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calls a static factory on a class defined inside the it block")
class IP:
    value: text

    static fn from(s: text) -> IP:
        IP(value: s)

val addr = IP.from("127.0.0.1")
expect addr.value == "127.0.0.1"
```

</details>

#### supports two it-blocks declaring the same class name (first wins)

- supports two it-blocks declaring the same class name (first wins)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports two it-blocks declaring the same class name (first wins)")
class Box:
    v: i32

val b = Box(v: 42)
expect b.v == 42
```

</details>

#### supports two it-blocks declaring the same class name (second occurrence)

- supports two it-blocks declaring the same class name (second occurrence)


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("supports two it-blocks declaring the same class name (second occurrence)")
# The hoist policy keeps the first declaration of `Box` and drops
# this one; the runtime semantics of the BDD interpreter still
# construct `Box(v: 99)` because it walks AST per `it` block.
class Box:
    v: i32

val b = Box(v: 99)
expect b.v == 99
```

</details>

#### handles a class with multiple fields and a method

- handles a class with multiple fields and a method


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles a class with multiple fields and a method")
class Rect:
    w: i32
    h: i32

    fn area(self) -> i32:
        self.w * self.h

val r = Rect(w: 4, h: 5)
expect r.area() == 20
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/unit/compiler/r1_class_in_it_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering R1 nested class definitions.
- R1 nested class definitions

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `01af42dbef87b8b2a377cfdb99ea2f94f29e65ae27a93230c7a888f3773143ba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `01af42dbef87b8b2a377cfdb99ea2f94f29e65ae27a93230c7a888f3773143ba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `01af42dbef87b8b2a377cfdb99ea2f94f29e65ae27a93230c7a888f3773143ba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/compiler/r1_class_in_it_spec.spl
mirror: doc/06_spec/unit/compiler/r1_class_in_it_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/compiler/r1_class_in_it_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/compiler/r1_class_in_it_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/compiler/r1_class_in_it_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'instantiates a class defined inside the it block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/r1_class_in_it_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls a static factory on a class defined inside the it block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/compiler/r1_class_in_it_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports two it-blocks declaring the same class name (first wins)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
