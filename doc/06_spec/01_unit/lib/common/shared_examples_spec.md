# Shared Examples Specification

> Tests covering Shared Examples (TEST-010, TEST-011), Basic shared_examples usage, Shared examples with fixtures, Multiple shared examples in same context, Nested contexts with shared examples, include_examples alias, Shared Examples Edge Cases, shared examples with no dependencies, shared examples in nested context, Shared examples with local state.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Shared Examples Specification

## Scenarios

#### can test equality

- can test equality


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can test equality")
expect 1 + 1 == 2
```

</details>

#### can test boolean

- can test boolean


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can test boolean")
expect true
```

</details>

#### container has items

- container has items


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("container has items")
val c = get_let(:container)
expect len(c) >= 0
```

</details>

#### value is defined

- value is defined


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("value is defined")
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

- can test constants


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can test constants")
expect 1 + 1 == 2
```

</details>

#### can test strings

- can test strings


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("can test strings")
expect len("hello") == 5
```

</details>

### shared examples in nested context

#### outer

#### works in nested context

- works in nested context


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("works in nested context")
expect true
```

</details>

### Shared examples with local state

#### first group

#### second group

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/shared_examples_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Shared Examples (TEST-010, TEST-011), Basic shared_examples usage, Shared examples with fixtures, Multiple shared examples in same context, Nested contexts with shared examples, include_examples alias, Shared Examples Edge Cases, shared examples with no dependencies, shared examples in nested context, Shared examples with local state.
- Shared Examples (TEST-010, TEST-011)
- Basic shared_examples usage
- Shared examples with fixtures
- Multiple shared examples in same context
- Nested contexts with shared examples
- include_examples alias
- Shared Examples Edge Cases
- shared examples with no dependencies
- shared examples in nested context
- Shared examples with local state

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `86e6e3db11bfccbc4d4ce00e0b28ce0312a6785e6034af0e1b909f402143d19e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `86e6e3db11bfccbc4d4ce00e0b28ce0312a6785e6034af0e1b909f402143d19e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `86e6e3db11bfccbc4d4ce00e0b28ce0312a6785e6034af0e1b909f402143d19e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/01_unit/lib/common/shared_examples_spec.spl
mirror: doc/06_spec/01_unit/lib/common/shared_examples_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/shared_examples_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/shared_examples_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/shared_examples_spec.spl:45:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can test equality' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/shared_examples_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can test equality' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/shared_examples_spec.spl:50:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can test boolean' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/shared_examples_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'can test boolean' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/shared_examples_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'container has items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/shared_examples_spec.spl:149:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can test constants' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/common/shared_examples_spec.spl:154:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can test strings' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
