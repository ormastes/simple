# Implementation Blocks Specification

> Implementation blocks (`impl`) provide a flexible way to define methods for types outside of the type definition. This enables separation of concerns, method organization, and extension of types in different modules without modifying the original definition.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Implementation Blocks Specification

Implementation blocks (`impl`) provide a flexible way to define methods for types outside of the type definition. This enables separation of concerns, method organization, and extension of types in different modules without modifying the original definition.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #830-835 |
| Category | Language |
| Difficulty | 2/5 |
| Status | Implemented |
| Source | `test/03_system/feature/usage/impl_blocks_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Implementation blocks (`impl`) provide a flexible way to define methods for types outside
of the type definition. This enables separation of concerns, method organization, and
extension of types in different modules without modifying the original definition.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Impl Block | Collection of methods for a type |
| Instance Method | Methods that receive self as implicit parameter |
| Static Method | Methods that don't receive self |
| Method Organization | Grouping related behavior in impl blocks |

## Behavior

- Methods in impl blocks are part of the type's interface
- Impl blocks can be placed in any module or location
- Multiple impl blocks for the same type are merged
- Static methods are called with type name prefix
- Instance methods use dot notation on values

## Scenarios

### Implementation Blocks - Basic

#### defines methods in impl block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defines methods in impl block


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines methods in impl block")
val p = Point(x: 5, y: 10)
expect p.get_x() == 5
```

</details>

#### defines multiple methods

- defines multiple methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines multiple methods")
val r = Rectangle(width: 4, height: 5)
expect r.area() == 20
expect r.perimeter() == 18
```

</details>

### Implementation Blocks - Static Methods

#### uses static factory method

- uses static factory method


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses static factory method")
val p1 = Point.origin()
expect p1.x == 0
expect p1.y == 0

val p2 = Point.from_coords(3, 4)
expect p2.x == 3
expect p2.y == 4
```

</details>

### Implementation Blocks - Instance Methods

#### defines immutable methods

- defines immutable methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines immutable methods")
val c = Circle(radius: 5.0)
# Approximate equality due to floating point
expect c.area() > 78.0
expect c.circumference() > 31.0
```

</details>

#### defines mutable methods

- defines mutable methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("defines mutable methods")
val c = Counter(count: 0)
c.increment()
expect c.count == 1
c.decrement()
expect c.count == 0
```

</details>

### Implementation Blocks - Mixed Methods

#### mixes static and instance methods

- mixes static and instance methods


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("mixes static and instance methods")
val t = Temperature.from_fahrenheit(32.0)
# Approximately 0 celsius
expect t.celsius > -1.0
expect t.celsius < 1.0
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9299c0c1f381e42273641d3bed76f4a96fac06af8a5a62782f11472aa9f8cc83`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9299c0c1f381e42273641d3bed76f4a96fac06af8a5a62782f11472aa9f8cc83`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9299c0c1f381e42273641d3bed76f4a96fac06af8a5a62782f11472aa9f8cc83`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/impl_blocks_spec.spl
mirror: doc/06_spec/03_system/feature/usage/impl_blocks_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/impl_blocks_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/impl_blocks_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/impl_blocks_spec.spl:118:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines methods in impl block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/impl_blocks_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defines multiple methods' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/impl_blocks_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses static factory method' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
