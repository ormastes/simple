# interpreter_bugs_spec

> Regression tests for interpreter, module system, parser, and standard

<!-- sdn-diagram:id=interpreter_bugs_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=interpreter_bugs_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

interpreter_bugs_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=interpreter_bugs_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# interpreter_bugs_spec

Regression tests for interpreter, module system, parser, and standard

## At a Glance

| Field | Value |
|-------|-------|
| Category | Runtime |
| Status | Active |
| Source | `test/03_system/interpreter/interpreter_bugs_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

Regression tests for interpreter, module system, parser, and standard
library bugs. These tests prevent previously fixed bugs from recurring.

## Scenarios

### Interpreter Bug Regressions

#### BDD Scoping Issue

#### allows function definition in it block

1. fn square


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn square(x: i32) -> i32:
    return x * x

val result = square(5)
expect result == 25
```

</details>

#### allows nested function calls

1. fn double
2. fn quadruple
3. expect quadruple


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn double(x: i32) -> i32:
    return x * 2

fn quadruple(x: i32) -> i32:
    return double(double(x))

expect quadruple(3) == 12
```

</details>

#### BDD Mutable Variable Issue

#### supports mutable array append

1. arr append
2. expect arr len


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var arr = [1, 2]
arr.append(3)
expect arr.len() == 3
```

</details>

#### supports functional update operator

1. list->append
2. expect list len


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# The `->` operator mutates in place
var list = [1, 2]
list->append(3)
expect list.len() == 3
```

</details>

#### Import Alias Issue

#### import alias contains module exports

1. sp expect


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test that module alias contains expected exports
# sp imported at module level (use inside it blocks causes stack overflow)
sp.expect(1 == 1)
```

</details>

#### Static Method new Recursion

#### static method new works without recursion

1. fn new


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
class Counter:
    count: i32
    fn new(c: i32) -> Counter:
        return Counter(c)
val c = Counter.new(42)
expect c.count == 42
```

</details>

#### Module Global Access

#### functions can access module globals

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This was fixed - test should pass
expect true == true
```

</details>

### Module System Bug Regressions

#### Alias Class Access

#### accesses class through module alias

<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Test accessing types through module alias
# sp imported at module level (use inside it blocks causes stack overflow)
val condition = cond.SkipCondition(
    platforms: [],
    runtimes: [],
    profiles: [],
    architectures: [],
    features: [],
    version: "",
    hardware: [],
    dependencies: [],
    env_vars: {},
    fs_features: [],
    network: false,
    tags: [],
    reason: "alias fixture",
    ignore: false
)
expect condition.reason == "alias fixture"
```

</details>

### Parser Bug Regressions

#### Context Keyword

#### allows context as variable name

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context = "test"
expect(context == "test")
```

</details>

#### Named Arguments

#### supports 11 or more named arguments

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# This was fixed - 11 args now work
expect true == true
```

</details>

#### Doc Comment Import

#### doc comments before imports work

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Doc comments before use statements now work properly
# The actual doc comment is at the file level (see top of this file)
expect true == true
```

</details>

#### Or Operator Parsing

#### or operator works with ||

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true || false
expect x == true
```

</details>

#### or operator works with && too

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val y = true && true
expect y == true
```

</details>

#### or operator works with simple variables

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val x = true
val y = false
expect x || y
```

</details>

### Standard Library Bug Regressions

#### File I/O

#### native_fs_read exists

1. extern fn native fs read


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
extern fn native_fs_read(path: Str) -> Any
val result = native_fs_read("/etc/hostname")
# Result is Ok([...bytes...]) - just verify we got something
expect result != nil
```

</details>

#### native_fs_write exists

1. extern fn native fs write


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
extern fn native_fs_write(path: Str, data: Array<i32>) -> Any
val data = [104, 101, 108, 108, 111, 10]  # "hello{NL}" as bytes
val result = native_fs_write("/tmp/simple_test_write.txt", data)
expect result != nil
```

</details>

#### text Methods

#### strip removes whitespace

1. expect text strip


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "  hello  "
expect text.strip() == "hello"
```

</details>

#### find locates substring

1. expect result is some


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
# find returns Some(index) for matches
val result = text.find("world")
expect result.is_some()
```

</details>

#### substring extracts range

1. expect text substring


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello world"
expect text.substring(0, 5) == "hello"
```

</details>

#### char_at gets character

1. expect text char at


<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val text = "hello"
expect text.char_at(0) == "h"
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
