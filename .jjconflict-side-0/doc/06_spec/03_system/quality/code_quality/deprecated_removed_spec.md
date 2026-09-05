# Deprecated Items Removed Spec

> Canary spec for AC-5: verifies that the replacement APIs for all 13 real `@deprecated` items work correctly after Team G removes the deprecated methods.

<!-- sdn-diagram:id=deprecated_removed_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=deprecated_removed_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

deprecated_removed_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=deprecated_removed_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deprecated Items Removed Spec

Canary spec for AC-5: verifies that the replacement APIs for all 13 real `@deprecated` items work correctly after Team G removes the deprecated methods.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-allow-suppressions |
| Category | Testing |
| Difficulty | 1/5 |
| Status | In Progress |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/deprecated_removed_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Canary spec for AC-5: verifies that the replacement APIs for all 13 real
`@deprecated` items work correctly after Team G removes the deprecated methods.

NOTE: These specs verify the *replacement method works*. They cannot directly
assert that the deprecated method is gone — that is a grep gate at phase 7-verify:
  `rg -F '@deprecated' src/lib/nogc_sync_mut/ src/compiler_rust/lib/std/src/`
should return zero results after Team G completes.

These specs exercise Set.has / intersect / diff / sym_diff, Map.has,
String.upper / lower / each, List.each, and Path.ext.
They WILL PASS right now (replacement methods already exist). Their purpose
is to lock the replacement contract so it cannot regress.

## Scenarios

### AC-5 Set deprecated replacements

#### AC-5: Set.has returns true for a member element

1. var s = Set new
2. s insert
   - Expected: s.has("Alice") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Set.new()
s.insert("Alice")
expect(s.has("Alice")).to_equal(true)
```

</details>

#### AC-5: Set.has returns false for a missing element

1. var s = Set new
2. s insert
   - Expected: s.has("Bob") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Set.new()
s.insert("Alice")
expect(s.has("Bob")).to_equal(false)
```

</details>

#### AC-5: Set.intersect returns common elements only

1. var a = Set new
2. a insert
3. a insert
4. var b = Set new
5. b insert
6. b insert
   - Expected: result.has("y") is true
   - Expected: result.has("x") is false
   - Expected: result.has("z") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Set.new()
a.insert("x")
a.insert("y")
var b = Set.new()
b.insert("y")
b.insert("z")
val result = set_intersection(a, b)
expect(result.has("y")).to_equal(true)
expect(result.has("x")).to_equal(false)
expect(result.has("z")).to_equal(false)
```

</details>

#### AC-5: Set.diff returns elements only in self

1. var a = Set new
2. a insert
3. a insert
4. var b = Set new
5. b insert
6. b insert
   - Expected: result.has("x") is true
   - Expected: result.has("y") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Set.new()
a.insert("x")
a.insert("y")
var b = Set.new()
b.insert("y")
b.insert("z")
val result = set_difference(a, b)
expect(result.has("x")).to_equal(true)
expect(result.has("y")).to_equal(false)
```

</details>

#### AC-5: Set.sym_diff returns elements in exactly one set

1. var a = Set new
2. a insert
3. a insert
4. var b = Set new
5. b insert
6. b insert
   - Expected: result.has("x") is true
   - Expected: result.has("z") is true
   - Expected: result.has("y") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var a = Set.new()
a.insert("x")
a.insert("y")
var b = Set.new()
b.insert("y")
b.insert("z")
val result = set_symmetric_difference(a, b)
expect(result.has("x")).to_equal(true)
expect(result.has("z")).to_equal(true)
expect(result.has("y")).to_equal(false)
```

</details>

### AC-5 Map deprecated replacements

#### AC-5: Map.has returns true when key present

1. var m = Map new
2. m insert
   - Expected: m.has("name") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = Map.new()
m.insert("name", "Alice")
expect(m.has("name")).to_equal(true)
```

</details>

#### AC-5: Map.has returns false when key absent

1. var m = Map new
2. m insert
   - Expected: m.has("age") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var m = Map.new()
m.insert("name", "Alice")
expect(m.has("age")).to_equal(false)
```

</details>

### AC-5 String deprecated replacements

#### AC-5: String.upper converts to uppercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
expect(s.upper()).to_equal("HELLO")
```

</details>

#### AC-5: String.lower converts to lowercase

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "WORLD"
expect(s.lower()).to_equal("world")
```

</details>

#### AC-5: String.each iterates over characters

1. seen push
   - Expected: seen.len() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
var seen: [text] = []
each(s, \c:
    seen.push(c.to_string())
)
expect(seen.len()).to_equal(3)
```

</details>

### AC-5 List deprecated replacements

#### AC-5: List.each iterates over all elements

1. seen push
   - Expected: sum equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val items = [1, 2, 3]
var seen: [i64] = []
items.each(\n:
    seen.push(n)
)
var sum = 0
for n in seen:
    sum = sum + n
expect(sum).to_equal(6)
```

</details>

### AC-5 Path deprecated replacements

#### AC-5: Path.ext returns the file extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(extension("report.md")).to_equal("md")
```

</details>

#### AC-5: Path.ext returns empty string for no extension

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(extension("Makefile")).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
