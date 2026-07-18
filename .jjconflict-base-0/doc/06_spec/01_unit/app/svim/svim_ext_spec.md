# svim_ext_spec

> svim extension modules specification

<!-- sdn-diagram:id=svim_ext_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=svim_ext_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

svim_ext_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=svim_ext_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 20 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# svim_ext_spec

svim extension modules specification

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/svim/svim_ext_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

svim extension modules specification

Self-contained tests for search repeat, text-object, quickfix traversal,
and language bridge helpers. All types are defined inline.

## Scenarios

### svim search_repeat

#### finds pattern at start of string

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = search_find_next("hello world", 0, "hello")
expect(idx).to_equal(0)
```

</details>

#### finds pattern after start offset

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = search_find_next("abcabc", 1, "abc")
expect(idx).to_equal(3)
```

</details>

#### returns -1 when pattern not found

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = search_find_next("hello", 0, "xyz")
expect(idx).to_equal(-1)
```

</details>

#### search_next wraps around to beginning

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = search_next("abcabc", 3, "abc")
expect(idx).to_equal(0)
```

</details>

#### search_prev finds occurrence before current col

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val idx = search_prev("abcabc", 3, "abc")
expect(idx).to_equal(0)
```

</details>

### svim text_object

#### inner_word returns full word bounds

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = inner_word("hello world", 2)
expect(bounds[0]).to_equal(0)
expect(bounds[1]).to_equal(5)
```

</details>

#### inner_word handles col at word boundary

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = inner_word("foo bar", 4)
expect(bounds[0]).to_equal(4)
expect(bounds[1]).to_equal(7)
```

</details>

#### around_word includes trailing space

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = around_word("foo bar", 0)
expect(bounds[0]).to_equal(0)
expect(bounds[1]).to_equal(4)
```

</details>

#### inner_line strips leading and trailing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = inner_line("  hello  ")
expect(bounds[0]).to_equal(2)
expect(bounds[1]).to_equal(7)
```

</details>

#### inner_word on empty string returns 0 0

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val bounds = inner_word("", 0)
expect(bounds[0]).to_equal(0)
expect(bounds[1]).to_equal(0)
```

</details>

### svim quickfix_traversal

#### new traversal starts at index 0 with empty entries

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val qt = QfTraversal.new()
expect(qt.entry_count()).to_equal(0)
expect(qt.current_index).to_equal(0)
```

</details>

#### next advances to second entry

1. QfEntry
2. QfEntry
   - Expected: moved is true
   - Expected: qt.current_index equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var qt = QfTraversal.from_list([
    QfEntry(row: 1, col: 0, severity: "error", message: "e1"),
    QfEntry(row: 2, col: 0, severity: "warn", message: "w1")
])
val moved = qt.next_entry()
expect(moved).to_equal(true)
expect(qt.current_index).to_equal(1)
```

</details>

#### prev returns to previous entry

1. QfEntry
2. QfEntry
3. qt next entry
   - Expected: moved is true
   - Expected: qt.current_index equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var qt = QfTraversal.from_list([
    QfEntry(row: 1, col: 0, severity: "error", message: "e1"),
    QfEntry(row: 2, col: 0, severity: "warn", message: "w1")
])
qt.next_entry()
val moved = qt.prev_entry()
expect(moved).to_equal(true)
expect(qt.current_index).to_equal(0)
```

</details>

#### jump_index sets current index

1. QfEntry
2. QfEntry
3. QfEntry
   - Expected: ok is true
   - Expected: qt.current_entry().message equals `c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var qt = QfTraversal.from_list([
    QfEntry(row: 0, col: 0, severity: "error", message: "a"),
    QfEntry(row: 1, col: 0, severity: "error", message: "b"),
    QfEntry(row: 2, col: 0, severity: "warn", message: "c")
])
val ok = qt.jump_index(2)
expect(ok).to_equal(true)
expect(qt.current_entry().message).to_equal("c")
```

</details>

#### qf_filter_severity returns only matching severity

1. QfEntry
2. QfEntry
3. QfEntry
   - Expected: errors.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = [
    QfEntry(row: 0, col: 0, severity: "error", message: "e1"),
    QfEntry(row: 1, col: 0, severity: "warn", message: "w1"),
    QfEntry(row: 2, col: 0, severity: "error", message: "e2")
]
val errors = qf_filter_severity(entries, "error")
expect(errors.len()).to_equal(2)
```

</details>

### svim language_bridge_ext

#### bridge_diag preserves row col severity message

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pd = ParseDiag(row: 3, col: 5, severity: "error", message: "unexpected token", source: "parser")
val bd = bridge_diag(pd)
expect(bd.row).to_equal(3)
expect(bd.col).to_equal(5)
expect(bd.severity).to_equal("error")
expect(bd.message).to_equal("unexpected token")
```

</details>

#### bridge_qf label includes source and 1-based line col

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pd = ParseDiag(row: 0, col: 0, severity: "error", message: "boom", source: "myfile.spl")
val bq = bridge_qf(pd)
expect(bq.label).to_equal("myfile.spl:1:1: error")
```

</details>

#### bridge_all_diags converts list

1. ParseDiag
2. ParseDiag
   - Expected: bds.len() equals `2`
   - Expected: bds[1].row equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pds = [
    ParseDiag(row: 0, col: 0, severity: "error", message: "a", source: "f.spl"),
    ParseDiag(row: 1, col: 2, severity: "warn", message: "b", source: "f.spl")
]
val bds = bridge_all_diags(pds)
expect(bds.len()).to_equal(2)
expect(bds[1].row).to_equal(1)
```

</details>

#### bridge_has_errors returns true when errors present

1. ParseDiag
2. ParseDiag
   - Expected: has is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pds = [
    ParseDiag(row: 0, col: 0, severity: "error", message: "x", source: "s"),
    ParseDiag(row: 1, col: 0, severity: "warn", message: "y", source: "s")
]
val has = bridge_has_errors(pds)
expect(has).to_equal(true)
```

</details>

#### bridge_has_errors returns false with no errors

1. ParseDiag
   - Expected: has == false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pds = [
    ParseDiag(row: 0, col: 0, severity: "warn", message: "x", source: "s")
]
val has = bridge_has_errors(pds)
expect(has == false).to_equal(true)
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
