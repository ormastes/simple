# Named Argument with Equals Syntax Specification

> connect(host: "localhost", port: 8080)

<!-- sdn-diagram:id=named_arg_equals_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=named_arg_equals_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

named_arg_equals_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=named_arg_equals_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

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
| Updated | 2026-06-01 |
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

1. fn greet
2. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text) -> text:
    "Hello, {name}!"
expect greet(name="World") == "Hello, World!"
```

</details>

#### passes multiple named arguments

1. fn format point
2. "
3. expect format point


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn format_point(x: i64, y: i64) -> text:
    "({x}, {y})"
expect format_point(x=3, y=4) == "(3, 4)"
```

</details>

#### allows reordered named arguments

1. fn format point
2. "
3. expect format point


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn format_point(x: i64, y: i64) -> text:
    "({x}, {y})"
expect format_point(y=4, x=3) == "(3, 4)"
```

</details>

#### basic named arguments with colon

#### passes single named argument with colon

1. fn greet
2. expect greet


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn greet(name: text) -> text:
    "Hello, {name}!"
expect greet(name: "World") == "Hello, World!"
```

</details>

#### passes multiple named arguments with colon

1. fn format point
2. "
3. expect format point


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn format_point(x: i64, y: i64) -> text:
    "({x}, {y})"
expect format_point(x: 3, y: 4) == "(3, 4)"
```

</details>

#### allows reordered named arguments with colon

1. fn format point
2. "
3. expect format point


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn format_point(x: i64, y: i64) -> text:
    "({x}, {y})"
expect format_point(y: 4, x: 3) == "(3, 4)"
```

</details>

#### mixed positional and named arguments

#### combines positional with named equals

1. fn connect
2. expect connect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn connect(host: text, port: i64) -> text:
    "{host}:{port}"
expect connect("localhost", port=8080) == "localhost:8080"
```

</details>

#### combines positional with named colon

1. fn connect
2. expect connect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn connect(host: text, port: i64) -> text:
    "{host}:{port}"
expect connect("localhost", port: 8080) == "localhost:8080"
```

</details>

#### uses multiple positional then named

1. fn format record
2. "{id}: {name}
3. expect format record


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn format_record(id: i64, name: text, active: bool) -> text:
    "{id}: {name} (active={active})"
expect format_record(1, "Alice", active=true) == "1: Alice (active=true)"
```

</details>

#### named arguments with default values

#### uses default when named arg omitted

1. fn create config
2. "{host}:{port}
3. expect create config


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_config(host: text, port: i64 = 80, timeout: i64 = 30) -> text:
    "{host}:{port} (timeout={timeout})"
expect create_config(host="example.com") == "example.com:80 (timeout=30)"
```

</details>

#### overrides default with named arg

1. fn create config
2. "{host}:{port}
3. expect create config


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_config(host: text, port: i64 = 80, timeout: i64 = 30) -> text:
    "{host}:{port} (timeout={timeout})"
expect create_config(host="example.com", port=443) == "example.com:443 (timeout=30)"
```

</details>

#### overrides multiple defaults

1. fn create config
2. "{host}:{port}
3. expect create config


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_config(host: text, port: i64 = 80, timeout: i64 = 30) -> text:
    "{host}:{port} (timeout={timeout})"
expect create_config(host="example.com", port=443, timeout=60) == "example.com:443 (timeout=60)"
```

</details>

#### overrides defaults in any order

1. fn create config
2. "{host}:{port}
3. expect create config


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn create_config(host: text, port: i64 = 80, timeout: i64 = 30) -> text:
    "{host}:{port} (timeout={timeout})"
expect create_config(host="example.com", timeout=120, port=8080) == "example.com:8080 (timeout=120)"
```

</details>

#### struct construction with named arguments

#### constructs struct with equals syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64
val p = Point(x=10, y=20)
expect p.x == 10
expect p.y == 20
```

</details>

#### constructs struct with colon syntax

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64
val p = Point(x: 10, y: 20)
expect p.x == 10
expect p.y == 20
```

</details>

#### allows reordered struct fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
struct Point:
    x: i64
    y: i64
val p = Point(y=20, x=10)
expect p.x == 10
expect p.y == 20
```

</details>

#### constructs complex struct

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

1. fn f
2. expect f


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn f(a: i64, b: i64) -> i64:
    a + b
expect f(a=1, b=2) == 3
```

</details>

#### handles longer parameter names

1. fn calculate
2. expect calculate


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn calculate(first_operand: i64, second_operand: i64) -> i64:
    first_operand * second_operand
expect calculate(first_operand=5, second_operand=6) == 30
```

</details>

#### handles underscored parameter names

1. fn process
2. expect process


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
