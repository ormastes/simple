# constructor_spec

> Verifies the constructor behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# constructor_spec

Verifies the constructor behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/constructor_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the constructor behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Module-Level Constructors

#### Direct construction works (PRIMARY METHOD)

- Verify: Direct construction works (PRIMARY METHOD)


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: Direct construction works (PRIMARY METHOD)")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val p = Point(5, 6)
check(p.x == 5)
check(p.y == 6)
```

</details>

#### Direct construction with named parameters

- Verify: Direct construction with named parameters


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: Direct construction with named parameters")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val p = Point(x: 7, y: 8)
check(p.x == 7)
check(p.y == 8)
```

</details>

#### fn new() is implicitly static at module level

- Verify: fn new() is implicitly static at module level


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: fn new() is implicitly static at module level")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val p = Point.new(3, 4)
check(p.x == 3)
check(p.y == 4)
```

</details>

#### fn create() is implicitly static

- Verify: fn create() is implicitly static


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: fn create() is implicitly static")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val cfg = Config.create(42)
check(cfg.value == 42)
```

</details>

#### fn default() is implicitly static

- Verify: fn default() is implicitly static


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: fn default() is implicitly static")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val settings = Settings.default()
check(settings.enabled == true)
```

</details>

#### fn from_* is implicitly static

- Verify: fn from_* is implicitly static


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: fn from_* is implicitly static")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val p = Point.from_tuple((10, 20))
check(p.x == 10)
check(p.y == 20)
```

</details>

#### static fn with_* works as factory

- Verify: static fn with_* works as factory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: static fn with_* works as factory")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val b = Builder.with_name("test")
check(b.name == "test")
```

</details>

#### Explicit static keyword still works

- Verify: Explicit static keyword still works


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: Explicit static keyword still works")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val r = Rectangle.new(10, 20)
check(r.width == 10)
check(r.height == 20)
```

</details>

#### Instance methods still get implicit self

- Verify: Instance methods still get implicit self


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: Instance methods still get implicit self")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val c = Counter.new()
check(c.get_count() == 0)
c.increment()
check(c.get_count() == 1)
c.increment()
check(c.get_count() == 2)
```

</details>

#### Direct construction and new() can coexist

- Verify: Direct construction and new() can coexist


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: Direct construction and new() can coexist")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val p1 = Point(1, 2)          # Direct
val p2 = Point.new(3, 4)      # Via new()
check(p1.x + p2.x == 4)
check(p1.y + p2.y == 6)
```

</details>

#### Direct construction preserves a returned array argument

- Verify: Direct construction preserves a returned array argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: Direct construction preserves a returned array argument")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val envelope = ArrayEnvelope(items: constructor_test_items())
check(envelope.items.len() == 6)
check(envelope.items[0] == 4)
check(envelope.items[5] == 42)
```

</details>

#### Generic class construction preserves a specialized returned array

- Verify: Generic class construction preserves a specialized returned array


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_CONSTRUCTOR-001
step("Verify: Generic class construction preserves a specialized returned array")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val envelope = GenericArrayEnvelope<i64>(items: generic_constructor_test_items<i64>(7, 11))
check(envelope.items.len() == 2)
check(envelope.items[0] == 7)
check(envelope.items[1] == 11)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `296af096de4d718f44783e4a8eb132fbe2bb5f99c70470bb4860499a3f62dc42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `296af096de4d718f44783e4a8eb132fbe2bb5f99c70470bb4860499a3f62dc42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `296af096de4d718f44783e4a8eb132fbe2bb5f99c70470bb4860499a3f62dc42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **94/100**; effective score: **94/100**; blockers: **0**.

SSpec documentization score: 94/100
source: test/01_unit/std/constructor_spec.spl
mirror: doc/06_spec/01_unit/std/constructor_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/constructor_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/constructor_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/constructor_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
<!-- sspec-maintain:scorecard:end -->
