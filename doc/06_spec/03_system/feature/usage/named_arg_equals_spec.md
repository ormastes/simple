# Named Argument with Equals Syntax Specification

> connect(host: "localhost", port: 8080)

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Named Argument with Equals Syntax Specification

connect(host: "localhost", port: 8080)

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #NAMED-ARG-EQUALS |
| Category | Syntax |
| Status | Implemented |
| Source | `test/03_system/feature/usage/named_arg_equals_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Syntax

```simple
# Colon syntax (preferred for readability)
connect(host: "localhost", port: 8080)

# Equals syntax (concise, especially for single args)
Point(x=3, y=4)

# Mixed with positional
greet("Hello", name="World")
```

## Key Behaviors

- Named arguments can appear in any order
- Named arguments can be mixed with positional arguments
- Positional arguments must come before named arguments
- Both `name: value` and `name=value` syntax are supported

## Scenarios

### Named Arguments with Equals Syntax

#### basic named arguments with equals

#### passes single named argument

- passes single named argument


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes single named argument")
fn greet(name: text) -> text:
    "Hello, {name}!"
expect greet(name="World") == "Hello, World!"
```

</details>

#### passes multiple named arguments

- passes multiple named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes multiple named arguments")
fn format_point(x: i64, y: i64) -> text:
    "({x}, {y})"
expect format_point(x=3, y=4) == "(3, 4)"
```

</details>

#### allows reordered named arguments

- allows reordered named arguments


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows reordered named arguments")
fn format_point(x: i64, y: i64) -> text:
    "({x}, {y})"
expect format_point(y=4, x=3) == "(3, 4)"
```

</details>

#### basic named arguments with colon

#### passes single named argument with colon

- passes single named argument with colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes single named argument with colon")
fn greet(name: text) -> text:
    "Hello, {name}!"
expect greet(name: "World") == "Hello, World!"
```

</details>

#### passes multiple named arguments with colon

- passes multiple named arguments with colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("passes multiple named arguments with colon")
fn format_point(x: i64, y: i64) -> text:
    "({x}, {y})"
expect format_point(x: 3, y: 4) == "(3, 4)"
```

</details>

#### allows reordered named arguments with colon

- allows reordered named arguments with colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows reordered named arguments with colon")
fn format_point(x: i64, y: i64) -> text:
    "({x}, {y})"
expect format_point(y: 4, x: 3) == "(3, 4)"
```

</details>

#### mixed positional and named arguments

#### combines positional with named equals

- combines positional with named equals


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines positional with named equals")
fn connect(host: text, port: i64) -> text:
    "{host}:{port}"
expect connect("localhost", port=8080) == "localhost:8080"
```

</details>

#### combines positional with named colon

- combines positional with named colon


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("combines positional with named colon")
fn connect(host: text, port: i64) -> text:
    "{host}:{port}"
expect connect("localhost", port: 8080) == "localhost:8080"
```

</details>

#### uses multiple positional then named

- uses multiple positional then named


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses multiple positional then named")
fn format_record(id: i64, name: text, active: bool) -> text:
    "{id}: {name} (active={active})"
expect format_record(1, "Alice", active=true) == "1: Alice (active=true)"
```

</details>

#### named arguments with default values

#### uses default when named arg omitted

- uses default when named arg omitted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses default when named arg omitted")
fn create_config(host: text, port: i64 = 80, timeout: i64 = 30) -> text:
    "{host}:{port} (timeout={timeout})"
expect create_config(host="example.com") == "example.com:80 (timeout=30)"
```

</details>

#### overrides default with named arg

- overrides default with named arg


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overrides default with named arg")
fn create_config(host: text, port: i64 = 80, timeout: i64 = 30) -> text:
    "{host}:{port} (timeout={timeout})"
expect create_config(host="example.com", port=443) == "example.com:443 (timeout=30)"
```

</details>

#### overrides multiple defaults

- overrides multiple defaults


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overrides multiple defaults")
fn create_config(host: text, port: i64 = 80, timeout: i64 = 30) -> text:
    "{host}:{port} (timeout={timeout})"
expect create_config(host="example.com", port=443, timeout=60) == "example.com:443 (timeout=60)"
```

</details>

#### overrides defaults in any order

- overrides defaults in any order


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("overrides defaults in any order")
fn create_config(host: text, port: i64 = 80, timeout: i64 = 30) -> text:
    "{host}:{port} (timeout={timeout})"
expect create_config(host="example.com", timeout=120, port=8080) == "example.com:8080 (timeout=120)"
```

</details>

#### struct construction with named arguments

#### constructs struct with equals syntax

- constructs struct with equals syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("constructs struct with equals syntax")
struct Point:
    x: i64
    y: i64
val p = Point(x=10, y=20)
expect p.x == 10
expect p.y == 20
```

</details>

#### constructs struct with colon syntax

- constructs struct with colon syntax


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("constructs struct with colon syntax")
struct Point:
    x: i64
    y: i64
val p = Point(x: 10, y: 20)
expect p.x == 10
expect p.y == 20
```

</details>

#### allows reordered struct fields

- allows reordered struct fields


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("allows reordered struct fields")
struct Point:
    x: i64
    y: i64
val p = Point(y=20, x=10)
expect p.x == 10
expect p.y == 20
```

</details>

#### constructs complex struct

- constructs complex struct


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("constructs complex struct")
struct Person:
    name: text
    age: i64
    active: bool
val person = Person(name="Alice", age=30, active=true)
expect person.name == "Alice"
expect person.age == 30
expect person.active == true
```

</details>

#### edge cases

#### handles single character parameter names

- handles single character parameter names


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles single character parameter names")
fn f(a: i64, b: i64) -> i64:
    a + b
expect f(a=1, b=2) == 3
```

</details>

#### handles longer parameter names

- handles longer parameter names


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles longer parameter names")
fn calculate(first_operand: i64, second_operand: i64) -> i64:
    first_operand * second_operand
expect calculate(first_operand=5, second_operand=6) == 30
```

</details>

#### handles underscored parameter names

- handles underscored parameter names


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles underscored parameter names")
fn process(input_value: i64, max_retries: i64) -> i64:
    input_value * max_retries
expect process(input_value=10, max_retries=3) == 30
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

- Canonical SPipe generation for source `db6e8472a0436b34a5d4d63567d167ca1fa47aebae8eec9f4fdb01f11aff35c2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `db6e8472a0436b34a5d4d63567d167ca1fa47aebae8eec9f4fdb01f11aff35c2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `db6e8472a0436b34a5d4d63567d167ca1fa47aebae8eec9f4fdb01f11aff35c2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/usage/named_arg_equals_spec.spl
mirror: doc/06_spec/03_system/feature/usage/named_arg_equals_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/usage/named_arg_equals_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/usage/named_arg_equals_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/usage/named_arg_equals_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes single named argument' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/named_arg_equals_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'passes multiple named arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/usage/named_arg_equals_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'allows reordered named arguments' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
