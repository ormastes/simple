# text.chars() Deprecation Replacement Spec

> Canary spec locking the replacement APIs for the deprecated `text.chars()` method. All migration waves are complete: automatically rewrites `for x in s.chars()` → `for x in s` at AST level, eliminating the `List<char>` allocation without requiring source changes.

<!-- sdn-diagram:id=chars_deprecated_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=chars_deprecated_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

chars_deprecated_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=chars_deprecated_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# text.chars() Deprecation Replacement Spec

Canary spec locking the replacement APIs for the deprecated `text.chars()` method. All migration waves are complete: automatically rewrites `for x in s.chars()` → `for x in s` at AST level, eliminating the `List<char>` allocation without requiring source changes.

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | fix-foreach-deprecated, fix-char-at |
| Category | Testing |
| Difficulty | 1/5 |
| Status | Complete |
| Requirements | N/A |
| Plan | N/A |
| Design | N/A |
| Research | N/A |
| Source | `test/03_system/quality/code_quality/chars_deprecated_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Canary spec locking the replacement APIs for the deprecated `text.chars()` method.
All migration waves are complete:
- Pattern B/C (indexed access `chars()[i]`, stored `val cs = s.chars(); cs[i]`) — migrated to `s.get(i)`.
- Pattern D (`.chars().first()/.last()/.filter()/.reverse()/.enumerate()`) — migrated to direct API.
- Pattern A (`for ch in s.chars()`) — handled by `collection_desugar.spl` Pattern F: the compiler
  automatically rewrites `for x in s.chars()` → `for x in s` at AST level, eliminating the
  `List<char>` allocation without requiring source changes.

Replacements for `text.chars()` usage:
- Iteration: `for ch in s` (preferred — text implements Iterable<char>; auto-desugared from `s.chars()`)
- Callback iteration: `s.each(fn)` (use when callback is a named function)
- Indexed iteration: `s.each_with_index(fn)` (replaces enumerate patterns)
- Random access: `s.get(i)` returns `Option<char>` (replaces `s.chars()[i]`)

`text.chars()` remains `@deprecated` because non-for patterns (`.chars().len()`,
`.chars().map(...)`) still allocate. These specs lock the replacement contract
so regressions are caught.

## Scenarios

### text.each(fn) visits every character (replaces chars() iteration)

#### text.each(fn) visits every character in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_join_via_each("abc")).to_equal("abc")
```

</details>

#### text.each(fn) on empty string calls fn zero times

1. seen push
   - Expected: seen.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
var seen: [i64] = []
each(s, \c:
    seen.push(1)
)
expect(seen.len()).to_equal(0)
```

</details>

#### text.each(fn) counts characters correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_count_via_each("hello")).to_equal(5)
```

</details>

### for ch in string iterates characters without chars()

#### for ch in string visits every character

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "xyz"
var count = 0
for ch in s:
    count = count + 1
expect(count).to_equal(3)
```

</details>

#### for ch in string accumulates characters in order

1. result = result + ch to string
   - Expected: result equals `hi`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hi"
var result = ""
for ch in s:
    result = result + ch.to_string()
expect(result).to_equal("hi")
```

</details>

#### for ch in empty string executes zero iterations

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = ""
var count = 0
for ch in s:
    count = count + 1
expect(count).to_equal(0)
```

</details>

### text.each_with_index provides index alongside character

#### text.each_with_index passes correct index and character

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# indices for "abc" are 0,1,2 — sum = 3
expect(_sum_indices_via_each_with_index("abc")).to_equal(3)
```

</details>

### for ch in s.chars() produces same result as for ch in s (Pattern F)

#### for ch in s.chars() accumulates same string as for ch in s

1. from chars = from chars + ch to string
2. from s = from s + ch to string
   - Expected: from_chars equals `from_s`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "hello"
var from_chars = ""
for ch in s.chars():
    from_chars = from_chars + ch.to_string()
var from_s = ""
for ch in s:
    from_s = from_s + ch.to_string()
expect(from_chars).to_equal(from_s)
```

</details>

#### for ch in s.chars() on empty string iterates zero times

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var count = 0
for ch in "".chars():
    count = count + 1
expect(count).to_equal(0)
```

</details>

#### for ch in s.chars() visits characters in forward order

1. result = result + ch to string
   - Expected: result equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val s = "abc"
var result = ""
for ch in s.chars():
    result = result + ch.to_string()
expect(result).to_equal("abc")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
