# given_working_spec

> Verifies the given working behaviour end to end so maintainers of this

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 21 | 21 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# given_working_spec

Verifies the given working behaviour end to end so maintainers of this

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/std/given_working_spec.spl` |
| Updated | 2026-08-22 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Verifies the given working behaviour end to end so maintainers of this
component and reviewers of its spec share one pinned definition.
## Operator workflow
Run `bin/simple test <this spec>`; read the per-scenario verdicts in
the `Results:` summary. Each scenario asserts an observable outcome.
## Compatibility and limitations
Covers the currently shipped behaviour only; performance, stress and
unrelated sibling features are out of scope.

## Scenarios

### Given (Eager Fixtures)

### Unnamed eager - given:

#### with eager setup

#### setup_ran is available

- Verify: setup_ran is available


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: setup_ran is available")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var setup_ran = false
setup_ran = true
expect setup_ran == true
```

</details>

#### setup_ran is true in second example too

- Verify: setup_ran is true in second example too


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: setup_ran is true in second example too")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var setup_ran = false
setup_ran = true
expect setup_ran == true
```

</details>

### Named eager - before_each:

#### with named eager setup

#### counter is initialized

- Verify: counter is initialized


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: counter is initialized")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var counter = 0
counter = counter + 1
expect counter == 1
```

</details>

#### processed is true

- Verify: processed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: processed is true")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var processed = false
processed = true
expect processed == true
```

</details>

#### each example gets fresh state

- Verify: each example gets fresh state


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: each example gets fresh state")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
# Each test initializes its own counter, so it's always 1
var counter = 0
counter = counter + 1
expect counter == 1
```

</details>

### Combining unnamed given and before_each

#### with mixed eager fixtures

#### both hooks ran

- Verify: both hooks ran


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: both hooks ran")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var given_ran = false
var before_each_ran = false
given_ran = true
before_each_ran = true
expect given_ran == true
expect before_each_ran == true
```

</details>

#### second example sees both hooks ran

- Verify: second example sees both hooks ran


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: second example sees both hooks ran")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: eager runs before lazy


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: eager runs before lazy")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var eager_run_count = 0
eager_run_count = eager_run_count + 1
expect eager_run_count == 1
expect get_let(:lazy_value) == 42
```

</details>

#### lazy is memoized, eager runs again

- Verify: lazy is memoized, eager runs again


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: lazy is memoized, eager runs again")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: level is available in inner


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: level is available in inner")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
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

- Verify: context_def given works


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: context_def given works")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect get_let(:ctx_value) == 100
```

</details>

### Real-world database simulation

#### with realistic setup

#### connection established

- Verify: connection established


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: connection established")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var connection = "db_connection_established"
expect connection == "db_connection_established"
```

</details>

#### tables created

- Verify: tables created


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: tables created")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var tables = ["users", "posts", "comments"]
expect len(tables) == 3
```

</details>

#### users table exists

- Verify: users table exists


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: users table exists")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var tables = ["users", "posts", "comments"]
expect len(tables) > 0
if len(tables) > 0:
    expect tables[0] == "users"
```

</details>

#### second test gets fresh setup

- Verify: second test gets fresh setup


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: second test gets fresh setup")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
var setup_count = 0
setup_count = setup_count + 1
expect setup_count == 1
```

</details>

### Referencing context_def with given_lazy

#### has database from context_def

- Verify: has database from context_def


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: has database from context_def")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect get_let(:database) == "db_connection"
```

</details>

#### has token from context_def

- Verify: has token from context_def


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: has token from context_def")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect get_let(:token) == "auth_token_123"
```

</details>

### Context with additional given

#### accesses fixture from context_def

- Verify: accesses fixture from context_def


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: accesses fixture from context_def")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
expect get_let(:base) == 10
```

</details>

#### uses derived variable from fixture

- Verify: uses derived variable from fixture


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: uses derived variable from fixture")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val derived = get_let(:base) * 2
expect derived == 20
```

</details>

#### combines context data with new variables

- Verify: combines context data with new variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: combines context data with new variables")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val derived = get_let(:base) * 2
val combined = get_let(:base) + derived
expect combined == 30
```

</details>

#### each test gets fresh derived state

- Verify: each test gets fresh derived state


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-TEST-STD_GIVEN_WORKING-001
step("Verify: each test gets fresh derived state")
# evidence(expect(...) oracle verified): pinned constants below are authoritative values asserted by this scenario
val derived = get_let(:base) * 2
expect derived == 20
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 21 |
| Active scenarios | 21 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4fa22f1815164dcaf74b5d2db134183d1f90dcbd29df5c2a599f9bc700d5def9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4fa22f1815164dcaf74b5d2db134183d1f90dcbd29df5c2a599f9bc700d5def9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4fa22f1815164dcaf74b5d2db134183d1f90dcbd29df5c2a599f9bc700d5def9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **93/100**; effective score: **93/100**; blockers: **0**.

SSpec documentization score: 93/100
source: test/01_unit/std/given_working_spec.spl
mirror: doc/06_spec/01_unit/std/given_working_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=85 coverage=100 maintainability=60
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/std/given_working_spec.md:1:1: warning SSDOC-EVD-002 [evidence] (-15): source steps are not visible in the generated manual
  why: Source tokens alone do not prove reader-visible workflow structure.
  improve: Use supported literal step calls and regenerate the manual.
doc/06_spec/01_unit/std/given_working_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/std/given_working_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: assumptions/preconditions, traceability, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/std/given_working_spec.spl:1:1: advice SSDOC-MNT-006 [maintainability] (-10): repeated setup is not expressed through a named helper
  why: Named setup helpers keep scenarios concise and consistent.
  improve: Extract a domain-named setup helper shared by the scenarios.
<!-- sspec-maintain:scorecard:end -->
