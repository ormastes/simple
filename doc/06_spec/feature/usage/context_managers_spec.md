# Context Managers Specification

> with resource as alias:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Context Managers Specification

with resource as alias:

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #CONTEXT-MANAGER |
| Category | Language |
| Status | Implemented |
| Source | `test/feature/usage/context_managers_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
with resource as alias:
# code using alias
# __exit__ is called after this block
```

## Key Behaviors

- `__enter__()` is called on entry, its return value is bound to alias
- `__exit__()` is always called, even if an exception occurs
- Alias binding can coexist with parser special handling (e.g., cast expressions)
- Clean separation between resource acquisition and usage
- Exception safety: cleanup always happens

## Scenarios

### Context Managers

#### basic context manager protocol

#### calls __enter__ and binds result to alias

- calls __enter__ and binds result to alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls __enter__ and binds result to alias")
class Resource:
    value: i64

    fn __enter__() -> i64:
        self.value + 10

    fn __exit__(exc):
        pass

var captured = 0
with Resource(5) as alias:
    captured = alias

expect captured == 15
```

</details>

#### calls __exit__ after block completes

- calls __exit__ after block completes


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("calls __exit__ after block completes")
class Resource:
    value: i64
    exited: bool = false

    fn __enter__() -> i64:
        self.value

    fn __exit__(exc):
        exited = true

val resource = Resource(value: 42)
with resource as alias:
    pass

expect resource.exited == true
```

</details>

#### alias binding and reuse

#### reuses identifier when parser sees cast-style syntax

- reuses identifier when parser sees cast-style syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("reuses identifier when parser sees cast-style syntax")
class Resource:
    value: i64

    fn __enter__() -> i64:
        self.value + 1

    fn __exit__(exc):
        pass

var result = 0
with Resource(2) as alias:
    val inner = alias
    result = inner

expect result == 3
```

</details>

#### properly binds alias in nested contexts

- properly binds alias in nested contexts


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("properly binds alias in nested contexts")
class Resource:
    value: i64

    fn __enter__() -> i64:
        self.value * 2

    fn __exit__(exc):
        pass

var results = []
with Resource(5) as x:
    results.push(x)
    with Resource(3) as y:
        results.push(y)
    results.push(x)

expect results == [10, 6, 10]
```

</details>

#### resource cleanup

#### runs cleanup code after block

- runs cleanup code after block


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("runs cleanup code after block")
class Resource:
    cleanup_count: i64 = 0

    fn __enter__() -> i64:
        0

    fn __exit__(exc):
        cleanup_count = cleanup_count + 1

val resource = Resource()
with resource as x:
    pass

expect resource.cleanup_count == 1
```

</details>

#### runs cleanup even after multiple operations

- runs cleanup even after multiple operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("runs cleanup even after multiple operations")
class Resource:
    operations: i64 = 0
    exit_called: bool = false

    fn __enter__() -> i64:
        0

    fn __exit__(exc):
        exit_called = true

val resource = Resource()
with resource as x:
    resource.operations = 1
    resource.operations = 2
    resource.operations = 3

expect resource.operations == 3
expect resource.exit_called == true
```

</details>

#### using acquired values

#### can use alias from __enter__ return value

- can use alias from __enter__ return value


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can use alias from __enter__ return value")
class Config:
    filename: text
    content: text = ""

    fn __enter__() -> text:
        "loaded content"

    fn __exit__(exc):
        pass

var loaded = ""
with Config(filename: "test.txt") as data:
    loaded = data

expect loaded == "loaded content"
```

</details>

#### can call methods on alias

- can call methods on alias


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can call methods on alias")
class Handler:
    fn __enter__() -> Handler:
        self

    fn __exit__(exc):
        pass

    fn process() -> i64:
        42

var result = 0
with Handler() as handler:
    result = handler.process()

expect result == 42
```

</details>

#### exception handling

#### passes exception info to __exit__

- passes exception info to __exit__


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("passes exception info to __exit__")
class Resource:
    exception_passed: bool = false

    fn __enter__() -> i64:
        0

    fn __exit__(exc):
        # exc is the exception or None
        exception_passed = exc != None

val resource = Resource()
with resource as x:
    pass

# No exception occurred, so exc should be None
expect resource.exception_passed == false
```

</details>

#### always calls __exit__ for resource cleanup

- always calls __exit__ for resource cleanup


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("always calls __exit__ for resource cleanup")
class Resource:
    exit_was_called: bool = false

    fn __enter__() -> i64:
        42

    fn __exit__(exc):
        exit_was_called = true

val resource = Resource()
val result = 0
with resource as value:
    # Some operation
    val temp = value + 1

expect resource.exit_was_called == true
```

</details>

#### multiple resources

#### can nest multiple context managers

- can nest multiple context managers


<details>
<summary>Executable SSpec</summary>

Runnable source: 24 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("can nest multiple context managers")
class Resource:
    id: i64
    exited: bool = false

    fn __enter__() -> i64:
        self.id

    fn __exit__(exc):
        exited = true

val r1 = Resource(id: 1)
val r2 = Resource(id: 2)
var results = []

with r1 as x:
    results.push(x)
    with r2 as y:
        results.push(y)

expect results == [1, 2]
expect r1.exited == true
expect r2.exited == true
```

</details>

#### cleans up in reverse order

- cleans up in reverse order


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("cleans up in reverse order")
class Resource:
    id: i64
    exit_order: List<i64> = []

    fn __enter__() -> i64:
        self.id

    fn __exit__(exc):
        # Append to shared list to track order
        pass

# Ideally, exits happen in reverse: 2 then 1
# Implementation dependent on execution model
```

</details>

#### practical patterns

#### implements file-like resource pattern

- implements file-like resource pattern


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("implements file-like resource pattern")
class File:
    filename: text
    is_open: bool = false

    fn __enter__() -> text:
        is_open = true
        "file content"

    fn __exit__(exc):
        is_open = false

val file = File(filename: "data.txt")
var content = ""

with file as data:
    expect file.is_open == true
    content = data

expect file.is_open == false
expect content == "file content"
```

</details>

#### ensures state is restored on exit

- ensures state is restored on exit


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-FEATURE
step("ensures state is restored on exit")
class StateManager:
    state: text = "initial"

    fn __enter__() -> text:
        state = "active"
        state

    fn __exit__(exc):
        state = "cleaned"

val manager = StateManager()
var temp = ""

with manager as state:
    temp = state
    expect manager.state == "active"

expect manager.state == "cleaned"
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-FEATURE`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cec4c3aa5c839fa27457aaf2feb9699b237db73d9cfa1cc5cd126ba2aa30f009`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cec4c3aa5c839fa27457aaf2feb9699b237db73d9cfa1cc5cd126ba2aa30f009`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cec4c3aa5c839fa27457aaf2feb9699b237db73d9cfa1cc5cd126ba2aa30f009`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/feature/usage/context_managers_spec.spl
mirror: doc/06_spec/feature/usage/context_managers_spec.md (current)
findings: 8 blockers: 0
  narrative=100 structure=85 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/feature/usage/context_managers_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/feature/usage/context_managers_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/feature/usage/context_managers_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls __enter__ and binds result to alias' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/context_managers_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'calls __exit__ after block completes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/context_managers_spec.spl:82:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reuses identifier when parser sees cast-style syntax' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/feature/usage/context_managers_spec.spl:164:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can use alias from __enter__ return value' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/usage/context_managers_spec.spl:183:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can call methods on alias' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/feature/usage/context_managers_spec.spl:244:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'can nest multiple context managers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
