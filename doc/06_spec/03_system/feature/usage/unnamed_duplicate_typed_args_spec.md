# Unnamed Duplicate Typed Arguments Warning Specification

> This lint warns when a function has multiple parameters of the same type that

<!-- sdn-diagram:id=unnamed_duplicate_typed_args_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=unnamed_duplicate_typed_args_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

unnamed_duplicate_typed_args_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=unnamed_duplicate_typed_args_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Unnamed Duplicate Typed Arguments Warning Specification

This lint warns when a function has multiple parameters of the same type that

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #LINT-001 |
| Category | Lint |
| Status | Implemented |
| Source | `test/03_system/feature/usage/unnamed_duplicate_typed_args_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

This lint warns when a function has multiple parameters of the same type that
are passed positionally without named arguments. This helps prevent argument
order mistakes at call sites by encouraging explicit naming.

## Scenarios

### Unnamed Duplicate Typed Args Warning

#### functions with duplicate typed params

#### warns on positional call with two text params

1. fn copy text


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# When a function has fn foo(a: text, b: text)
# calling foo(x, y) should warn, but foo(a=x, b=y) should not
fn copy_text(src: text, dest: text) -> text:
    dest

# Named arguments - no warning
val result = copy_text(src="source", dest="destination")
expect result == "destination"
```

</details>

#### accepts named arguments without warning

1. fn swap
2.


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn swap(left: i64, right: i64) -> (i64, i64):
    (right, left)

# Named call prevents accidental swapping
val (a, b) = swap(left=1, right=2)
expect a == 2
expect b == 1
```

</details>

#### works with mixed named and positional args

1. fn range check


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn range_check(value: i64, min: i64, max: i64) -> bool:
    value >= min && value <= max

# First positional, rest named
val ok = range_check(5, min=0, max=10)
expect ok == true
```

</details>

#### no warning cases

#### does not warn on single parameter

1. fn single
2. expect single


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn single(x: text) -> text:
    x
expect single("hello") == "hello"
```

</details>

#### does not warn on different typed params

1. fn mixed
2. expect mixed


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn mixed(name: text, count: i64) -> text:
    "{name}: {count}"
expect mixed("items", 5) == "items: 5"
```

</details>

#### does not warn when all params are named

1. fn coords
2. expect coords


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn coords(x: i64, y: i64, z: i64) -> i64:
    x + y + z
expect coords(x=1, y=2, z=3) == 6
```

</details>

#### real world examples

#### copy function with named args

1. fn copy file


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn copy_file(source: text, dest: text) -> text:
    "Copied {source} to {dest}"

# Using named args prevents confusing source/dest
val msg = copy_file(source="/a/b.txt", dest="/c/d.txt")
expect msg == "Copied /a/b.txt to /c/d.txt"
```

</details>

#### compare function with named args

1. fn compare
2. expect compare


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn compare(expected: text, actual: text) -> bool:
    expected == actual

# Named args clarify which is expected vs actual
expect compare(expected="hello", actual="hello") == true
```

</details>

#### move function with named args

1. fn move item


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
fn move_item(from_pos: i64, to_pos: i64) -> i64:
    to_pos - from_pos

# Clear intent with named args
val distance = move_item(from_pos=0, to_pos=10)
expect distance == 10
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
