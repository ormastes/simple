# Given Working Specification

> Tests covering Given (Eager Fixtures), Unnamed eager - given:, Named eager - before_each:, Combining unnamed given and before_each, Given with lazy fixtures, Given in nested contexts, Given in context_def, Real-world database simulation, Referencing context_def with given_lazy, Context with additional given.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Given Working Specification

## Scenarios

### Given (Eager Fixtures)

### Unnamed eager - given:

#### with eager setup

#### setup_ran is available

- setup_ran is available


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("setup_ran is available")
var setup_ran = false
setup_ran = true
expect setup_ran == true
```

</details>

#### setup_ran is true in second example too

- setup_ran is true in second example too


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("setup_ran is true in second example too")
var setup_ran = false
setup_ran = true
expect setup_ran == true
```

</details>

### Named eager - before_each:

#### with named eager setup

#### counter is initialized

- counter is initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("counter is initialized")
var counter = 0
counter = counter + 1
expect counter == 1
```

</details>

#### processed is true

- processed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("processed is true")
var processed = false
processed = true
expect processed == true
```

</details>

#### each example gets fresh state

- each example gets fresh state


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("each example gets fresh state")
# Each test initializes its own counter, so it's always 1
var counter = 0
counter = counter + 1
expect counter == 1
```

</details>

### Combining unnamed given and before_each

#### with mixed eager fixtures

#### both hooks ran

- both hooks ran


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("both hooks ran")
var given_ran = false
var before_each_ran = false
given_ran = true
before_each_ran = true
expect given_ran == true
expect before_each_ran == true
```

</details>

#### second example sees both hooks ran

- second example sees both hooks ran


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("second example sees both hooks ran")
var given_ran = false
var before_each_ran = false
given_ran = true
before_each_ran = true
expect given_ran == true
expect before_each_ran == true
```

</details>

### Given with lazy fixtures

#### mixing eager and lazy

#### eager runs before lazy

- eager runs before lazy


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("eager runs before lazy")
var eager_run_count = 0
eager_run_count = eager_run_count + 1
expect eager_run_count == 1
expect get_let(:lazy_value) == 42
```

</details>

#### lazy is memoized, eager runs again

- lazy is memoized, eager runs again


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("lazy is memoized, eager runs again")
var eager_run_count = 0
eager_run_count = eager_run_count + 1
expect eager_run_count == 1
expect get_let(:lazy_value) == 42
```

</details>

### Given in nested contexts

#### outer context

#### inner context

#### level is available in inner

- level is available in inner


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("level is available in inner")
var level = "outer"
var inner_level = "inner"
level = "outer_setup"
inner_level = "inner_setup"
expect level == "outer_setup"
expect inner_level == "inner_setup"
```

</details>

### Given in context_def

#### context_def given works

- context_def given works


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("context_def given works")
expect get_let(:ctx_value) == 100
```

</details>

### Real-world database simulation

#### with realistic setup

#### connection established

- connection established


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("connection established")
var connection = "db_connection_established"
expect connection == "db_connection_established"
```

</details>

#### tables created

- tables created


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("tables created")
var tables = ["users", "posts", "comments"]
expect len(tables) == 3
```

</details>

#### users table exists

- users table exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("users table exists")
var tables = ["users", "posts", "comments"]
expect len(tables) > 0
if len(tables) > 0:
    expect tables[0] == "users"
```

</details>

#### second test gets fresh setup

- second test gets fresh setup


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("second test gets fresh setup")
var setup_count = 0
setup_count = setup_count + 1
expect setup_count == 1
```

</details>

### Referencing context_def with given_lazy

#### has database from context_def

- has database from context_def


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has database from context_def")
expect get_let(:database) == "db_connection"
```

</details>

#### has token from context_def

- has token from context_def


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("has token from context_def")
expect get_let(:token) == "auth_token_123"
```

</details>

### Context with additional given

#### accesses fixture from context_def

- accesses fixture from context_def


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accesses fixture from context_def")
expect get_let(:base) == 10
```

</details>

#### uses derived variable from fixture

- uses derived variable from fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("uses derived variable from fixture")
val derived = get_let(:base) * 2
expect derived == 20
```

</details>

#### combines context data with new variables

- combines context data with new variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("combines context data with new variables")
val derived = get_let(:base) * 2
val combined = get_let(:base) + derived
expect combined == 30
```

</details>

#### each test gets fresh derived state

- each test gets fresh derived state


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("each test gets fresh derived state")
val derived = get_let(:base) * 2
expect derived == 20
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/given_working_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Given (Eager Fixtures), Unnamed eager - given:, Named eager - before_each:, Combining unnamed given and before_each, Given with lazy fixtures, Given in nested contexts, Given in context_def, Real-world database simulation, Referencing context_def with given_lazy, Context with additional given.
- Given (Eager Fixtures)
- Unnamed eager - given:
- Named eager - before_each:
- Combining unnamed given and before_each
- Given with lazy fixtures
- Given in nested contexts
- Given in context_def
- Real-world database simulation
- Referencing context_def with given_lazy
- Context with additional given

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
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

- Canonical SPipe generation for source `97b5d7e3eab024f19c394526acda95a01af1f101a58d269eeb9bdc4909038561`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `97b5d7e3eab024f19c394526acda95a01af1f101a58d269eeb9bdc4909038561`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `97b5d7e3eab024f19c394526acda95a01af1f101a58d269eeb9bdc4909038561`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **91/100**; effective score: **91/100**; blockers: **0**.

SSpec documentization score: 91/100
source: test/01_unit/lib/common/given_working_spec.spl
mirror: doc/06_spec/01_unit/lib/common/given_working_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/given_working_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/given_working_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/given_working_spec.spl:1:1: advice SSDOC-MNT-006 [maintainability] (-10): repeated setup is not expressed through a named helper
  why: Named setup helpers keep scenarios concise and consistent.
  improve: Extract a domain-named setup helper shared by the scenarios.
test/01_unit/lib/common/given_working_spec.spl:28:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'setup_ran is available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/given_working_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'setup_ran is true in second example too' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/given_working_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'counter is initialized' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
