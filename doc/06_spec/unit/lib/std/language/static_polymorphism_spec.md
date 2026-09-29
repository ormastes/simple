# Static Polymorphism Specification

> Tests covering Static Polymorphism.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Static Polymorphism Specification

## Scenarios

### Static Polymorphism

#### dispatches a bound trait to its concrete class

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- bind trait to class and call through the trait
   - Expected: g.greet("ada") equals `hello ada`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("bind trait to class and call through the trait")
bind Greeter = PlainGreeter
val g: Greeter = PlainGreeter {}
expect(g.greet("ada")).to_equal("hello ada")
```

</details>

#### specializes a generic function per concrete type

- call the same generic fn with two implementations
   - Expected: pick_greet(PlainGreeter {}, "bob") equals `hello bob`
   - Expected: pick_greet(LoudGreeter {}, "bob") equals `HELLO bob`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("call the same generic fn with two implementations")
expect(pick_greet(PlainGreeter {}, "bob")).to_equal("hello bob")
expect(pick_greet(LoudGreeter {}, "bob")).to_equal("HELLO bob")
```

</details>

#### keeps generic data structures type-safe over their parameter

- instantiate one generic holder over two element types
   - Expected: numbers.len() equals `3`
   - Expected: words.len() equals `2`
   - Expected: numbers[1] equals `2`
   - Expected: words[1] equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("instantiate one generic holder over two element types")
val numbers = [1, 2, 3]
val words = ["a", "b"]
expect(numbers.len()).to_equal(3)
expect(words.len()).to_equal(2)
expect(numbers[1]).to_equal(2)
expect(words[1]).to_equal("b")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/std/language/static_polymorphism_spec.spl` |
| Updated | 2026-08-27 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Static Polymorphism.
- Static Polymorphism

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
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

- Canonical SPipe generation for source `671aa722fdd6ec6e0ef5d7343a79a8f48c6ea75155a69837501c83704d9861a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `671aa722fdd6ec6e0ef5d7343a79a8f48c6ea75155a69837501c83704d9861a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `671aa722fdd6ec6e0ef5d7343a79a8f48c6ea75155a69837501c83704d9861a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **83/100**; effective score: **83/100**; blockers: **0**.

SSpec documentization score: 83/100
source: test/unit/lib/std/language/static_polymorphism_spec.spl
mirror: doc/06_spec/unit/lib/std/language/static_polymorphism_spec.md (current)
findings: 7 blockers: 0
  narrative=80 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/std/language/static_polymorphism_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/std/language/static_polymorphism_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/std/language/static_polymorphism_spec.spl:1:1: warning SSDOC-NAR-001 [narrative] (-20): missing authored purpose and audience
  why: Readers need scope, audience, and intent before executable detail.
  improve: Add authored purpose, scope, and audience facts.
test/unit/lib/std/language/static_polymorphism_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/std/language/static_polymorphism_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'dispatches a bound trait to its concrete class' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/language/static_polymorphism_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'specializes a generic function per concrete type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/std/language/static_polymorphism_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps generic data structures type-safe over their parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
