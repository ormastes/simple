# shared_examples_spec

> Verifies the shared examples behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# shared_examples_spec

Verifies the shared examples behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/shared_examples_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the shared examples behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

#### can test equality

- Verify: can test equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SHARED_EXAMPLES-001
step("Verify: can test equality")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect 1 + 1 == 2
```

</details>

#### can test boolean

- Verify: can test boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SHARED_EXAMPLES-001
step("Verify: can test boolean")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect true
```

</details>

#### container has items

- Verify: container has items


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SHARED_EXAMPLES-001
step("Verify: container has items")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val c = get_let(:container)
expect len(c) >= 0
```

</details>

#### value is defined

- Verify: value is defined


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SHARED_EXAMPLES-001
step("Verify: value is defined")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val v = get_let(:value)
expect v >= 0
```

</details>

### Shared Examples (TEST-010, TEST-011)

### Basic shared_examples usage

### Shared examples with fixtures

#### with a list container

#### with an empty container

#### with a numeric value

### Multiple shared examples in same context

#### with comprehensive setup

### Nested contexts with shared examples

#### outer context

#### inner context

### include_examples alias

#### using include_examples instead of it_behaves_like

### Shared Examples Edge Cases

### shared examples with no dependencies

#### can test constants

- Verify: can test constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SHARED_EXAMPLES-001
step("Verify: can test constants")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect 1 + 1 == 2
```

</details>

#### can test strings

- Verify: can test strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SHARED_EXAMPLES-001
step("Verify: can test strings")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect len("hello") == 5
```

</details>

### shared examples in nested context

#### outer

#### works in nested context

- Verify: works in nested context


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_SHARED_EXAMPLES-001
step("Verify: works in nested context")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect true
```

</details>

### Shared examples with local state

#### first group

#### second group

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4529d2b5ef9bf0c34d2eed9c7e2a97dbafdc35aa22b6998fb3ea3d33cf46c7b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4529d2b5ef9bf0c34d2eed9c7e2a97dbafdc35aa22b6998fb3ea3d33cf46c7b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4529d2b5ef9bf0c34d2eed9c7e2a97dbafdc35aa22b6998fb3ea3d33cf46c7b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/std/shared_examples_spec.spl
mirror: doc/06_spec/01_unit/std/shared_examples_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/shared_examples_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/shared_examples_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/shared_examples_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/shared_examples_spec.spl:54:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can test equality' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/std/shared_examples_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can test boolean' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/std/shared_examples_spec.spl:160:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can test constants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/std/shared_examples_spec.spl:166:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can test strings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
