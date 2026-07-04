# Mcp T32 Window Snapshot Specification

> 1. var store = snapshot store default

<!-- sdn-diagram:id=mcp_t32_window_snapshot_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_t32_window_snapshot_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_t32_window_snapshot_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_t32_window_snapshot_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 45 | 45 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp T32 Window Snapshot Specification

## Scenarios

### T32 MCP Window Snapshot/Diff

#### snapshot store

#### stores snapshot for new window

1. var store = snapshot store default
2. store = ss store
   - Expected: ss_has(store, "sess1/core0/register") is true
   - Expected: ss_size(store) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_default()
store = ss_store(store, "sess1/core0/register", "Registers", "PC 0x08001234\nSP 0x20001000", 1000)
expect(ss_has(store, "sess1/core0/register")).to_equal(true)
expect(ss_size(store)).to_equal(1)
```

</details>

#### retrieves content by key

1. var store = snapshot store default
2. store = ss store
   - Expected: content equals `PC 0x08001234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_default()
store = ss_store(store, "sess1/core0/register", "Registers", "PC 0x08001234", 1000)
val content = ss_get(store, "sess1/core0/register")
expect(content).to_equal("PC 0x08001234")
```

</details>

#### returns empty for unknown key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = snapshot_store_default()
val content = ss_get(store, "nonexistent/key")
expect(content).to_equal("")
```

</details>

#### returns empty hash for unknown key

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = snapshot_store_default()
val hash = ss_get_hash(store, "nonexistent/key")
expect(hash).to_equal("")
```

</details>

#### updates existing snapshot and changes hash

1. var store = snapshot store default
2. store = ss store
3. store = ss store
   - Expected: hash1 == hash2 is false
   - Expected: ss_size(store) equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_default()
store = ss_store(store, "sess1/core0/register", "Registers", "PC 0x08001234", 1000)
val hash1 = ss_get_hash(store, "sess1/core0/register")
store = ss_store(store, "sess1/core0/register", "Registers", "PC 0x08001238", 2000)
val hash2 = ss_get_hash(store, "sess1/core0/register")
expect(hash1 == hash2).to_equal(false)
expect(ss_size(store)).to_equal(1)
```

</details>

#### hash is consistent for same content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = ws_simple_hash("PC 0x08001234\nSP 0x20001000")
val h2 = ws_simple_hash("PC 0x08001234\nSP 0x20001000")
expect(h1).to_equal(h2)
```

</details>

#### hash differs for different content

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h1 = ws_simple_hash("PC 0x08001234")
val h2 = ws_simple_hash("PC 0x08001238")
expect(h1 == h2).to_equal(false)
```

</details>

#### djb2 hash produces nonzero for nonempty content

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val h = ws_djb2_hash("hello")
expect(h > 0).to_equal(true)
```

</details>

#### respects max capacity of 3

1. var store = snapshot store new
2. store = ss store
3. store = ss store
4. store = ss store
   - Expected: ss_size(store) equals `3`
5. store = ss store
   - Expected: ss_size(store) equals `3`
   - Expected: ss_has(store, "k1") is false
   - Expected: ss_has(store, "k4") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_new(3, 300)
store = ss_store(store, "k1", "t1", "c1", 100)
store = ss_store(store, "k2", "t2", "c2", 200)
store = ss_store(store, "k3", "t3", "c3", 300)
expect(ss_size(store)).to_equal(3)
store = ss_store(store, "k4", "t4", "c4", 400)
expect(ss_size(store)).to_equal(3)
# Oldest (k1 at ts=100) should be evicted
expect(ss_has(store, "k1")).to_equal(false)
expect(ss_has(store, "k4")).to_equal(true)
```

</details>

#### evicts oldest on capacity overflow preserving newest

1. var store = snapshot store new
2. store = ss store
3. store = ss store
4. store = ss store
   - Expected: ss_size(store) equals `2`
   - Expected: ss_has(store, "a") is false
   - Expected: ss_has(store, "b") is true
   - Expected: ss_has(store, "c") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_new(2, 300)
store = ss_store(store, "a", "ta", "ca", 10)
store = ss_store(store, "b", "tb", "cb", 20)
store = ss_store(store, "c", "tc", "cc", 30)
expect(ss_size(store)).to_equal(2)
expect(ss_has(store, "a")).to_equal(false)
expect(ss_has(store, "b")).to_equal(true)
expect(ss_has(store, "c")).to_equal(true)
```

</details>

#### structured row diff

#### identical rows produce empty diff

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "PC 0x08001234\nSP 0x20001000\nLR 0x08000100"
val after = "PC 0x08001234\nSP 0x20001000\nLR 0x08000100"
val diffs = diff_labeled_rows(before, after)
expect(diffs.len()).to_equal(0)
```

</details>

#### single label value change detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "PC 0x08001234\nSP 0x20001000"
val after = "PC 0x08001238\nSP 0x20001000"
val diffs = diff_labeled_rows(before, after)
expect(diffs.len()).to_equal(1)
expect(diffs[0].label).to_equal("PC")
expect(diffs[0].kind).to_equal("changed")
```

</details>

#### multiple changed labels detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "PC 0x08001234\nSP 0x20001000\nLR 0x08000100"
val after = "PC 0x08001238\nSP 0x20002000\nLR 0x08000100"
val diffs = diff_labeled_rows(before, after)
expect(diffs.len()).to_equal(2)
```

</details>

#### new label added detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "PC 0x08001234"
val after = "PC 0x08001234\nFP 0x20003000"
val diffs = diff_labeled_rows(before, after)
expect(diffs.len()).to_equal(1)
expect(diffs[0].label).to_equal("FP")
expect(diffs[0].kind).to_equal("added")
```

</details>

#### removed label detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "PC 0x08001234\nSP 0x20001000"
val after = "PC 0x08001234"
val diffs = diff_labeled_rows(before, after)
expect(diffs.len()).to_equal(1)
expect(diffs[0].label).to_equal("SP")
expect(diffs[0].kind).to_equal("removed")
```

</details>

#### diff entry has correct old and new values

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "PC 0x08001234\nSP 0x20001000"
val after = "PC 0x08001238\nSP 0x20001000"
val diffs = diff_labeled_rows(before, after)
expect(diffs[0].old_value).to_equal("0x08001234")
expect(diffs[0].new_value).to_equal("0x08001238")
```

</details>

#### empty before state is full capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = ""
val after = "PC 0x08001234\nSP 0x20001000"
val diffs = diff_labeled_rows(before, after)
expect(diffs.len()).to_equal(2)
expect(diffs[0].kind).to_equal("added")
expect(diffs[1].kind).to_equal("added")
```

</details>

#### change_count matches actual changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "PC 0x08001234\nSP 0x20001000\nLR 0x08000100\nR0 0x00000001"
val after = "PC 0x08001238\nSP 0x20001000\nLR 0x08000200\nR0 0x00000001"
val diffs = diff_labeled_rows(before, after)
expect(diffs.len()).to_equal(2)
```

</details>

#### removed entry has empty new_value

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "PC 0x08001234\nSP 0x20001000"
val after = "PC 0x08001234"
val diffs = diff_labeled_rows(before, after)
val removed = diffs[0]
expect(removed.old_value).to_equal("0x20001000")
expect(removed.new_value).to_equal("")
```

</details>

#### table diff

#### identical tables produce empty diff

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "addr|value|symbol\n0x1000|0xDEAD|main\n0x1004|0xBEEF|loop"
val after = "addr|value|symbol\n0x1000|0xDEAD|main\n0x1004|0xBEEF|loop"
val result = diff_tables(before, after)
expect(result.changed).to_equal(false)
expect(result.cells.len()).to_equal(0)
```

</details>

#### changed cell detected with row and col context

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "addr|value\n0x1000|0xDEAD\n0x1004|0xBEEF"
val after = "addr|value\n0x1000|0xDEAD\n0x1004|0xCAFE"
val result = diff_tables(before, after)
expect(result.changed).to_equal(true)
expect(result.cells.len()).to_equal(1)
expect(result.cells[0].row).to_equal(2)
expect(result.cells[0].col).to_equal(1)
expect(result.cells[0].old_value).to_equal("0xBEEF")
expect(result.cells[0].new_value).to_equal("0xCAFE")
```

</details>

#### row added detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "addr|value\n0x1000|0xDEAD"
val after = "addr|value\n0x1000|0xDEAD\n0x1004|0xBEEF"
val result = diff_tables(before, after)
expect(result.changed).to_equal(true)
expect(result.rows_added).to_equal(1)
```

</details>

#### row removed detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "addr|value\n0x1000|0xDEAD\n0x1004|0xBEEF"
val after = "addr|value\n0x1000|0xDEAD"
val result = diff_tables(before, after)
expect(result.changed).to_equal(true)
expect(result.rows_removed).to_equal(1)
```

</details>

#### mixed changes with add modify and remove

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "h1|h2\nA|1\nB|2\nC|3"
val after = "h1|h2\nA|1\nB|9\nD|4\nE|5"
val result = diff_tables(before, after)
expect(result.changed).to_equal(true)
# B row: col1 changed 2->9, C row vs D row: both cols differ
expect(result.cells.len()).to_be_greater_than(0)
expect(result.rows_added).to_equal(1)
```

</details>

#### empty table to populated is first capture

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = ""
val after = "addr|value\n0x1000|0xDEAD\n0x1004|0xBEEF"
val result = diff_tables(before, after)
expect(result.changed).to_equal(true)
expect(result.rows_added).to_be_greater_than(0)
```

</details>

#### multiple cell changes across rows

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "a|b|c\n1|2|3\n4|5|6"
val after = "a|b|c\n1|X|3\n4|5|Y"
val result = diff_tables(before, after)
expect(result.cells.len()).to_equal(2)
```

</details>

#### text diff fallback

#### identical text returns changed false

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "line1\nline2\nline3"
val after = "line1\nline2\nline3"
val result = diff_text_fallback(before, after, 8000)
expect(result.changed).to_equal(false)
expect(result.summary).to_equal("no changes")
```

</details>

#### single line change detected

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "PC 0x08001234\nSP 0x20001000"
val after = "PC 0x08001238\nSP 0x20001000"
val result = diff_text_fallback(before, after, 8000)
expect(result.changed).to_equal(true)
expect(result.changed_lines).to_equal(1)
```

</details>

#### multi-line change with context

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val before = "line1\nline2\nline3\nline4"
val after = "line1\nchanged2\nline3\nchanged4"
val result = diff_text_fallback(before, after, 8000)
expect(result.changed).to_equal(true)
expect(result.changed_lines).to_equal(2)
```

</details>

#### large diff truncated to token budget

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# Build a string that exceeds budget when divided by 4
var large_content = ""
var i = 0
while i < 500:
    large_content = large_content + "AAAA BBBB CCCC DDDD EEEE FFFF GGGG HHHH\n"
    i = i + 1
val result = diff_text_fallback("short", large_content, 100)
expect(result.changed).to_equal(true)
expect(result.truncated).to_equal(true)
```

</details>

#### small diff not truncated

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = diff_text_fallback("a", "b", 8000)
expect(result.changed).to_equal(true)
expect(result.truncated).to_equal(false)
```

</details>

#### mode selection

#### mode summary returns one-line status for change

1. var store = snapshot store default
2. store = ss store
   - Expected: result.mode equals `summary`
   - Expected: result.changed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_default()
store = ss_store(store, "s/c/reg", "Registers", "PC 0x1234", 1000)
val result = window_capture_with_mode(store, "s/c/reg", "Registers", "PC 0x5678", "summary", 1050)
expect(result.mode).to_equal("summary")
expect(result.changed).to_equal(true)
expect(result.content).to_contain("changed")
```

</details>

#### mode diff returns structured diff

1. var store = snapshot store default
2. store = ss store
   - Expected: result.mode equals `diff`
   - Expected: result.changed is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_default()
store = ss_store(store, "s/c/reg", "Registers", "PC 0x1234\nSP 0x2000", 1000)
val result = window_capture_with_mode(store, "s/c/reg", "Registers", "PC 0x5678\nSP 0x2000", "diff", 1050)
expect(result.mode).to_equal("diff")
expect(result.changed).to_equal(true)
expect(result.change_count).to_be_greater_than(0)
```

</details>

#### mode full returns complete content

1. var store = snapshot store default
2. store = ss store
   - Expected: result.mode equals `full`
   - Expected: result.content equals `PC 0x5678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_default()
store = ss_store(store, "s/c/reg", "Registers", "PC 0x1234", 1000)
val result = window_capture_with_mode(store, "s/c/reg", "Registers", "PC 0x5678", "full", 1050)
expect(result.mode).to_equal("full")
expect(result.content).to_equal("PC 0x5678")
```

</details>

#### mode diff with no changes returns changed false

1. var store = snapshot store default
2. store = ss store
   - Expected: result.changed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_default()
store = ss_store(store, "s/c/reg", "Registers", "PC 0x1234", 1000)
val result = window_capture_with_mode(store, "s/c/reg", "Registers", "PC 0x1234", "diff", 1050)
expect(result.changed).to_equal(false)
```

</details>

#### first capture in diff mode returns full content

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = snapshot_store_default()
val result = window_capture_with_mode(store, "s/c/reg", "Registers", "PC 0x1234", "diff", 1000)
expect(result.changed).to_equal(true)
expect(result.content).to_equal("PC 0x1234")
```

</details>

#### first capture in summary mode returns first capture label

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = snapshot_store_default()
val result = window_capture_with_mode(store, "s/c/reg", "Registers", "PC 0x1234", "summary", 1000)
expect(result.content).to_contain("first capture")
```

</details>

#### first capture in full mode returns full content

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = snapshot_store_default()
val result = window_capture_with_mode(store, "s/c/reg", "Registers", "PC 0x1234\nSP 0x2000", "full", 1000)
expect(result.changed).to_equal(true)
expect(result.content).to_contain("PC 0x1234")
```

</details>

#### mode full with no changes still returns content

1. var store = snapshot store default
2. store = ss store
   - Expected: result.changed is false
   - Expected: result.content equals `PC 0x1234`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_default()
store = ss_store(store, "s/c/reg", "Registers", "PC 0x1234", 1000)
val result = window_capture_with_mode(store, "s/c/reg", "Registers", "PC 0x1234", "full", 1050)
expect(result.changed).to_equal(false)
expect(result.content).to_equal("PC 0x1234")
```

</details>

#### TTL and eviction

#### snapshot within TTL is not expired

1. var store = snapshot store new
2. store = ss store
   - Expected: ss_is_expired(store, "s/c/reg", 1100) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_new(200, 300)
store = ss_store(store, "s/c/reg", "Registers", "PC 0x1234", 1000)
expect(ss_is_expired(store, "s/c/reg", 1100)).to_equal(false)
```

</details>

#### expired snapshot is detected

1. var store = snapshot store new
2. store = ss store
   - Expected: ss_is_expired(store, "s/c/reg", 1400) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_new(200, 300)
store = ss_store(store, "s/c/reg", "Registers", "PC 0x1234", 1000)
expect(ss_is_expired(store, "s/c/reg", 1400)).to_equal(true)
```

</details>

#### expired snapshot treated as first capture in diff mode

1. var store = snapshot store new
2. store = ss store
   - Expected: result.changed is true
   - Expected: result.content equals `PC 0x5678`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_new(200, 60)
store = ss_store(store, "s/c/reg", "Registers", "PC 0x1234", 1000)
# Capture at ts=1100 with TTL=60: 1100-1000=100 > 60 -> expired
val result = window_capture_with_mode(store, "s/c/reg", "Registers", "PC 0x5678", "diff", 1100)
expect(result.changed).to_equal(true)
# First capture returns full content, not diff
expect(result.content).to_equal("PC 0x5678")
```

</details>

#### cleanup removes expired entries

1. var store = snapshot store new
2. store = ss store
3. store = ss store
4. store = ss store
5. store = ss cleanup expired
   - Expected: ss_has(store, "k1") is false
   - Expected: ss_has(store, "k3") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var store = snapshot_store_new(200, 100)
store = ss_store(store, "k1", "t1", "c1", 1000)
store = ss_store(store, "k2", "t2", "c2", 1050)
store = ss_store(store, "k3", "t3", "c3", 1200)
# At ts=1150: k1 expired (150>100), k2 expired (100 not > 100, boundary), k3 alive
store = ss_cleanup_expired(store, 1150)
expect(ss_has(store, "k1")).to_equal(false)
expect(ss_has(store, "k3")).to_equal(true)
```

</details>

#### TTL configurable per store

1. var short ttl = snapshot store new
2. short ttl = ss store
3. var long ttl = snapshot store new
4. long ttl = ss store
   - Expected: ss_is_expired(short_ttl, "k1", 1050) is true
   - Expected: ss_is_expired(long_ttl, "k1", 1050) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var short_ttl = snapshot_store_new(200, 10)
short_ttl = ss_store(short_ttl, "k1", "t1", "c1", 1000)
var long_ttl = snapshot_store_new(200, 1000)
long_ttl = ss_store(long_ttl, "k1", "t1", "c1", 1000)
# At ts=1050: short TTL expired, long TTL alive
expect(ss_is_expired(short_ttl, "k1", 1050)).to_equal(true)
expect(ss_is_expired(long_ttl, "k1", 1050)).to_equal(false)
```

</details>

#### nonexistent key is treated as expired

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val store = snapshot_store_default()
expect(ss_is_expired(store, "nonexistent", 9999)).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_t32/mcp_t32_window_snapshot_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- T32 MCP Window Snapshot/Diff

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 45 |
| Active scenarios | 45 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
