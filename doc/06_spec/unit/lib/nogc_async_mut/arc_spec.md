# Arc Specification

> Tests covering Arc Type Syntax.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Arc Specification

## Scenarios

### Arc Type Syntax

#### @T type annotation

#### parses @T as atomic pointer type

- parses @T as atomic pointer type


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses @T as atomic pointer type")
# Parser test: val x: @Data
expect true
```

</details>

#### parses @T with generic parameter

- parses @T with generic parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses @T with generic parameter")
# Parser test: val x: @List<Int>
expect true
```

</details>

#### parses nested @T types

- parses nested @T types


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses nested @T types")
# Parser test: val x: @Option<@Data>
expect true
```

</details>

#### Arc allocation (new@)

#### allocates with new@ syntax

- allocates with new@ syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("allocates with new@ syntax")
# val shared: @Data = new@ Data(42)
expect true
```

</details>

#### has initial refcount of 1

- has initial refcount of 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has initial refcount of 1")
# arc.strong_count() == 1
expect true
```

</details>

#### Arc cloning

#### atomically increments refcount on clone

- atomically increments refcount on clone


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("atomically increments refcount on clone")
# val arc2 = arc1.clone()
expect true
```

</details>

#### shares data between clones

- shares data between clones


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("shares data between clones")
# arc1.borrow() == arc2.borrow()
expect true
```

</details>

#### Arc thread safety

#### can be sent across threads

- can be sent across threads


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("can be sent across threads")
# spawn { process(arc.clone()) }
expect true
```

</details>

#### maintains correct count across threads

- maintains correct count across threads


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("maintains correct count across threads")
# Concurrent clone/drop
expect true
```

</details>

#### Arc weak references

#### creates weak reference from Arc

- creates weak reference from Arc


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("creates weak reference from Arc")
# val weak = arc.downgrade()
expect true
```

</details>

#### upgrades weak to Arc atomically

- upgrades weak to Arc atomically


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("upgrades weak to Arc atomically")
# weak.upgrade() returns Option<Value>
expect true
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/arc_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Arc Type Syntax.
- Arc Type Syntax

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `b350436b3d6b208e33aefb31c7ba3aaf9cddac948e989376c3b40120c2ee51d8`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b350436b3d6b208e33aefb31c7ba3aaf9cddac948e989376c3b40120c2ee51d8`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b350436b3d6b208e33aefb31c7ba3aaf9cddac948e989376c3b40120c2ee51d8`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/unit/lib/nogc_async_mut/arc_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/arc_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=95 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/arc_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/arc_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/arc_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses @T as atomic pointer type' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/arc_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses @T with generic parameter' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/arc_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses nested @T types' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/nogc_async_mut/arc_spec.spl:63:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can be sent across threads' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
