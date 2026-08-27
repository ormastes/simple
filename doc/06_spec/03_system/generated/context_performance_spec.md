# context_performance_spec

> Test Context Performance Regression Test

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# context_performance_spec

Test Context Performance Regression Test

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/generated/context_performance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Test Context Performance Regression Test
Feature: SPipe Context Performance
Category: Testing, Performance
Status: In Progress

BUG-1: Test execution time grows exponentially (O(n²)) with nested context blocks.
This test reproduces the issue and serves as a regression test.

Reproducer for bug in src/lib/std/src/spec/runner/executor.spl:
- collect_before_each_hooks() has O(n²) complexity
- Each level recursively walks parent chain and copies all hooks
- Tests with 10+ contexts timeout (>120s)

## Scenarios

### Context Performance

#### Level 1

#### Level 2

#### Level 3

#### Level 4

#### Level 5

#### Level 6

#### Level 7

#### Level 8

#### Level 9

#### Level 10

#### executes test in deeply nested context
#### executes second test to amplify the issue
#### executes third test
#### Even deeper nesting (15 levels)

#### L1

#### L2

#### L3

#### L4

#### L5

#### L6

#### L7

#### L8

#### L9

#### L10

#### L11

#### L12

#### L13

#### L14

#### L15

#### handles extreme nesting
#### Multiple tests at each level

#### test at level 1

- test at level 1


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 1")
expect true
```

</details>

#### Level 2

#### test at level 2a

- test at level 2a


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 2a")
expect true
```

</details>

#### test at level 2b

- test at level 2b


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 2b")
expect true
```

</details>

#### Level 3

#### test at level 3a

- test at level 3a


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 3a")
expect true
```

</details>

#### test at level 3b

- test at level 3b


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 3b")
expect true
```

</details>

#### test at level 3c

- test at level 3c


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 3c")
expect true
```

</details>

#### Level 4

#### test at level 4a

- test at level 4a


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 4a")
expect true
```

</details>

#### test at level 4b

- test at level 4b


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 4b")
expect true
```

</details>

#### test at level 4c

- test at level 4c


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 4c")
expect true
```

</details>

#### test at level 4d

- test at level 4d


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 4d")
expect true
```

</details>

#### Level 5

#### test at level 5a

- test at level 5a


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 5a")
expect true
```

</details>

#### test at level 5b

- test at level 5b


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 5b")
expect true
```

</details>

#### test at level 5c

- test at level 5c


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 5c")
expect true
```

</details>

#### test at level 5d

- test at level 5d


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 5d")
expect true
```

</details>

#### test at level 5e

- test at level 5e


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("test at level 5e")
expect true
```

</details>

#### With before_each hooks

#### Nested with more hooks

#### Double nested

#### collects all parent hooks in order

- collects all parent hooks in order


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("collects all parent hooks in order")
"""
After fix: hooks should still be collected parent->child.
counter should be: 1 + 10 + 100 = 111 (or higher from previous tests)
"""
val hooks_ran = _context_perf_counter >= 100
expect hooks_ran
```

</details>

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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `756552f246f1704464fc9bc674a9161c4dcdfa5711ff943e0ee2cd8fae5d304f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `756552f246f1704464fc9bc674a9161c4dcdfa5711ff943e0ee2cd8fae5d304f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `756552f246f1704464fc9bc674a9161c4dcdfa5711ff943e0ee2cd8fae5d304f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/03_system/generated/context_performance_spec.spl
mirror: doc/06_spec/03_system/generated/context_performance_spec.md (current)
findings: 15 blockers: 0
  narrative=100 structure=30 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/generated/context_performance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/generated/context_performance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/generated/context_performance_spec.spl:51:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'executes test in deeply nested context' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/generated/context_performance_spec.spl:61:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'executes second test to amplify the issue' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/generated/context_performance_spec.spl:69:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'executes third test' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/generated/context_performance_spec.spl:93:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'handles extreme nesting' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/03_system/generated/context_performance_spec.spl:103:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test at level 1' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/generated/context_performance_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test at level 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/context_performance_spec.spl:109:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test at level 2a' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/generated/context_performance_spec.spl:109:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test at level 2a' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/context_performance_spec.spl:113:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test at level 2b' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/generated/context_performance_spec.spl:113:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'test at level 2b' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/generated/context_performance_spec.spl:119:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test at level 3a' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/generated/context_performance_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test at level 3b' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/generated/context_performance_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'test at level 3c' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
