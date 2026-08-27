# With Statement Basic Specification

> Tests covering with statement.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# With Statement Basic Specification

## Scenarios

### with statement

#### calls enter and cleanup on simple context manager

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- calls enter and cleanup on simple context manager


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls enter and cleanup on simple context manager")
# Define a simple context manager
class TestContext:
    entered: bool
    cleaned: bool

    fn enter() -> TestContext:
        self.entered = true
        self

    fn cleanup():
        self.cleaned = true

# Create context manager
val ctx = TestContext(entered: false, cleaned: false)

# Use with statement
with ctx as c:
    check c.entered

# Check cleanup was called
check ctx.cleaned
```

</details>

#### calls cleanup even when block completes normally

- calls cleanup even when block completes normally


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("calls cleanup even when block completes normally")
var cleanup_called = false

class TestContext:
    fn enter() -> TestContext:
        self

    fn cleanup():
        cleanup_called = true

val ctx = TestContext()

with ctx:
    val x = 42

check cleanup_called
```

</details>

#### supports variable binding with as clause

- supports variable binding with as clause


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports variable binding with as clause")
class ValueContext:
    value: text

    fn enter() -> text:
        self.value

    fn cleanup():
        ()

val ctx = ValueContext(value: "hello")

with ctx as val_:
    check val_ == "hello"
```

</details>

#### supports with statement without variable binding

- supports with statement without variable binding


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("supports with statement without variable binding")
var enter_called = false
var cleanup_called = false

class NoBindContext:
    fn enter() -> NoBindContext:
        enter_called = true
        self

    fn cleanup():
        cleanup_called = true

val ctx = NoBindContext()

with ctx:
    check enter_called

check cleanup_called
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/with_statement_basic_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering with statement.
- with statement

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

- Canonical SPipe generation for source `627dab25d128e5a3f56d73e7346a16c62f898665c9197056359a7dad31de1689`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `627dab25d128e5a3f56d73e7346a16c62f898665c9197056359a7dad31de1689`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `627dab25d128e5a3f56d73e7346a16c62f898665c9197056359a7dad31de1689`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/with_statement_basic_spec.spl
mirror: doc/06_spec/03_system/feature/features/with_statement_basic_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/with_statement_basic_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/with_statement_basic_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/with_statement_basic_spec.spl:15:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls enter and cleanup on simple context manager' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/with_statement_basic_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls cleanup even when block completes normally' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/with_statement_basic_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'supports variable binding with as clause' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
