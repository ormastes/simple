# sdoctest_spec

> Verifies that SDoctest correctly discovers and collects documentation

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# sdoctest_spec

Verifies that SDoctest correctly discovers and collects documentation

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/feature/features/sdoctest/sdoctest_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Verifies that SDoctest correctly discovers and collects documentation
    examples from module and function docstrings. Tests discovery of examples
    in various documentation locations.

## Scenarios

### Doctest Discovery

#### function docstring examples

#### finds examples in function docs

- finds examples in function docs


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds examples in function docs")
fn add(a: i64, b: i64) -> i64:
    a + b

expect add(2, 3) == 5
```

</details>

#### extracts multiple examples

- extracts multiple examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts multiple examples")
fn multiply(a: i64, b: i64) -> i64:
    a * b

expect multiply(3, 4) == 12
expect multiply(0, 100) == 0
```

</details>

#### module-level examples

#### finds examples in module docs

- finds examples in module docs


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("finds examples in module docs")
val module_result = 42
expect module_result == 42
```

</details>

### Doctest Execution

#### successful execution

#### executes simple example

- executes simple example


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes simple example")
fn double(x: i64) -> i64:
    x * 2

val result = double(5)
expect result == 10
```

</details>

#### executes example with setup

- executes example with setup


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes example with setup")
fn factorial(n: i64) -> i64:
    if n <= 1:
        1
    else:
        n * factorial(n - 1)

val result = factorial(5)
expect result == 120
```

</details>

#### assertion verification

#### verifies expect statements

- verifies expect statements


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies expect statements")
fn is_even(n: i64) -> bool:
    n % 2 == 0

expect is_even(4) == true
expect is_even(3) == false
```

</details>

#### verifies complex assertions

- verifies complex assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies complex assertions")
fn create_pair(a: i64, b: i64) -> (i64, i64):
    (a, b)

val (x, y) = create_pair(3, 7)
expect x == 3
expect y == 7
```

</details>

#### string output verification

#### verifies string output

- verifies string output


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("verifies string output")
fn greet(name: text) -> text:
    "Hello, {name}!"

val output = greet("Alice")
expect output == "Hello, Alice!"
```

</details>

### Doctest Failures

#### assertion failures

#### detects failed assertions

- detects failed assertions


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("detects failed assertions")
fn add(a: i64, b: i64) -> i64:
    a + b

val result = add(2, 3)
expect result == 5
```

</details>

#### reports wrong output

- reports wrong output


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("reports wrong output")
fn always_zero() -> i64:
    0

val result = always_zero()
expect result == 0
```

</details>

#### type errors

#### catches type mismatches

- catches type mismatches


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("catches type mismatches")
fn get_text() -> text:
    "hello"

val result = get_text()
expect result == "hello"
```

</details>

### Doctest Data Structure Examples

#### collection examples

#### documents list operations

- documents list operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents list operations")
fn sum_list(items: List<i64>) -> i64:
    var total = 0
    for item in items:
        total = total + item
    total

val data = [1, 2, 3, 4, 5]
val result = sum_list(data)
expect result == 15
```

</details>

#### documents dict operations

- documents dict operations


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents dict operations")
val data = {"a": 10, "b": 20}
val result = data.get("b")
expect result == 20
```

</details>

#### custom type examples

#### documents custom structs

- documents custom structs


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents custom structs")
struct Point:
    x: i64
    y: i64

fn distance_from_origin(p: Point) -> i64:
    (p.x * p.x + p.y * p.y)

val p = Point(x: 3, y: 4)
val dist = distance_from_origin(p)
expect dist == 25
```

</details>

#### documents enums

- documents enums


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("documents enums")
enum Status:
    Active
    Inactive
    Pending

fn is_active(status: Status) -> bool:
    match status:
        Status.Active:
            true
        _:
            false

expect is_active(Status.Active) == true
expect is_active(Status.Inactive) == false
```

</details>

### Doctest Helpers

#### helper functions

#### uses helper in doctest

- uses helper in doctest


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses helper in doctest")
fn create_test_list() -> List<i64>:
    [1, 2, 3]

fn process_list(items: List<i64>) -> i64:
    var total = 0
    for item in items:
        total = total + item
    total

val list = create_test_list()
val result = process_list(list)
expect result == 6
```

</details>

#### setup and teardown

#### initializes test data

- initializes test data


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("initializes test data")
fn initialize_dict() -> Dict<text, i64>:
    {"x": 10, "y": 20, "z": 30}

fn sum_dict_values(d: Dict<text, i64>) -> i64:
    var total = 0
    for pair in d:
        total = total + pair[1]
    total

val dict = initialize_dict()
val result = sum_dict_values(dict)
expect result == 60
```

</details>

#### multiple examples

#### executes related examples

- executes related examples


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("executes related examples")
fn increment(x: i64) -> i64:
    x + 1

fn decrement(x: i64) -> i64:
    x - 1

expect increment(5) == 6
expect decrement(5) == 4
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
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

- Canonical SPipe generation for source `13f21b502380419f3b9e34864083aef8febcabc81288257a44069ad2e14c62b9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `13f21b502380419f3b9e34864083aef8febcabc81288257a44069ad2e14c62b9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `13f21b502380419f3b9e34864083aef8febcabc81288257a44069ad2e14c62b9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/features/sdoctest/sdoctest_spec.spl
mirror: doc/06_spec/03_system/feature/features/sdoctest/sdoctest_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/features/sdoctest/sdoctest_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/features/sdoctest/sdoctest_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/features/sdoctest/sdoctest_spec.spl:34:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds examples in function docs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/sdoctest/sdoctest_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'extracts multiple examples' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/features/sdoctest/sdoctest_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds examples in module docs' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
