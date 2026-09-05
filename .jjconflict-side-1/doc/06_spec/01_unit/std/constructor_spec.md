# Constructor Specification

> Tests covering Module-Level Constructors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Constructor Specification

## Scenarios

### Module-Level Constructors

#### Direct construction works (PRIMARY METHOD)

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- Direct construction works (PRIMARY METHOD)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Direct construction works (PRIMARY METHOD)")
val p = Point(5, 6)
check(p.x == 5)
check(p.y == 6)
```

</details>

#### Direct construction with named parameters

- Direct construction with named parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Direct construction with named parameters")
val p = Point(x: 7, y: 8)
check(p.x == 7)
check(p.y == 8)
```

</details>

#### fn new() is implicitly static at module level

- fn new() is implicitly static at module level


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn new() is implicitly static at module level")
val p = Point.new(3, 4)
check(p.x == 3)
check(p.y == 4)
```

</details>

#### fn create() is implicitly static

- fn create() is implicitly static


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn create() is implicitly static")
val cfg = Config.create(42)
check(cfg.value == 42)
```

</details>

#### fn default() is implicitly static

- fn default() is implicitly static


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn default() is implicitly static")
val settings = Settings.default()
check(settings.enabled == true)
```

</details>

#### fn from_* is implicitly static

- fn from_* is implicitly static


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("fn from_* is implicitly static")
val p = Point.from_tuple((10, 20))
check(p.x == 10)
check(p.y == 20)
```

</details>

#### static fn with_* works as factory

- static fn with_* works as factory


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("static fn with_* works as factory")
val b = Builder.with_name("test")
check(b.name == "test")
```

</details>

#### Explicit static keyword still works

- Explicit static keyword still works


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Explicit static keyword still works")
val r = Rectangle.new(10, 20)
check(r.width == 10)
check(r.height == 20)
```

</details>

#### Instance methods still get implicit self

- Instance methods still get implicit self


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Instance methods still get implicit self")
val c = Counter.new()
check(c.get_count() == 0)
c.increment()
check(c.get_count() == 1)
c.increment()
check(c.get_count() == 2)
```

</details>

#### Direct construction and new() can coexist

- Direct construction and new() can coexist


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Direct construction and new() can coexist")
val p1 = Point(1, 2)          # Direct
val p2 = Point.new(3, 4)      # Via new()
check(p1.x + p2.x == 4)
check(p1.y + p2.y == 6)
```

</details>

#### Direct construction preserves a returned array argument

- Direct construction preserves a returned array argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Direct construction preserves a returned array argument")
val envelope = ArrayEnvelope(items: constructor_test_items())
check(envelope.items.len() == 6)
check(envelope.items[0] == 4)
check(envelope.items[5] == 42)
```

</details>

#### Generic class construction preserves a specialized returned array

- Generic class construction preserves a specialized returned array


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Generic class construction preserves a specialized returned array")
val envelope = GenericArrayEnvelope<i64>(items: generic_constructor_test_items<i64>(7, 11))
check(envelope.items.len() == 2)
check(envelope.items[0] == 7)
check(envelope.items[1] == 11)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/constructor_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Module-Level Constructors.
- Module-Level Constructors

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

- Canonical SPipe generation for source `3fbc353df20951f2e8c14f2c4f8813ca671f0b8a45a283f224b2e81275da143c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3fbc353df20951f2e8c14f2c4f8813ca671f0b8a45a283f224b2e81275da143c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3fbc353df20951f2e8c14f2c4f8813ca671f0b8a45a283f224b2e81275da143c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/std/constructor_spec.spl
mirror: doc/06_spec/01_unit/std/constructor_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/constructor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/constructor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/constructor_spec.spl:90:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Direct construction works (PRIMARY METHOD)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/constructor_spec.spl:97:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Direct construction with named parameters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/std/constructor_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fn new() is implicitly static at module level' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
