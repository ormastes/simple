# Claude Full CircularBuffer

> Mirrors `tmp/claude/claude-code-main/src/utils/CircularBuffer.ts` for fixed-size

<!-- sdn-diagram:id=CircularBuffer_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=CircularBuffer_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

CircularBuffer_spec -> std
CircularBuffer_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=CircularBuffer_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full CircularBuffer

Mirrors `tmp/claude/claude-code-main/src/utils/CircularBuffer.ts` for fixed-size

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/CircularBuffer_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Mirrors `tmp/claude/claude-code-main/src/utils/CircularBuffer.ts` for fixed-size
rolling-window behavior: append, append many, overflow eviction, recent reads,
array conversion, length, and clear.

## Scenarios

### Claude full utils CircularBuffer

#### stores items in insertion order until capacity

- Add fewer items than capacity and read them back oldest to newest
- buffer add
- buffer add
   - Expected: buffer.length() equals `2`
   - Expected: buffer.toArray() equals `["a", "b"]`
   - Expected: buffer.getRecent(5) equals `["a", "b"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Add fewer items than capacity and read them back oldest to newest")
val buffer = circularBufferNew(3)
buffer.add("a")
buffer.add("b")

expect(buffer.length()).to_equal(2)
expect(buffer.toArray()).to_equal(["a", "b"])
expect(buffer.getRecent(5)).to_equal(["a", "b"])
```

</details>

#### evicts the oldest items when full

- Fill the buffer, overflow it, and preserve newest capacity items
- buffer addAll
   - Expected: buffer.length() equals `3`
   - Expected: buffer.toArray() equals `["c", "d", "e"]`
   - Expected: buffer.getRecent(2) equals `["d", "e"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Fill the buffer, overflow it, and preserve newest capacity items")
val buffer = CircularBuffer.new(3)
buffer.addAll(["a", "b", "c", "d", "e"])

expect(buffer.length()).to_equal(3)
expect(buffer.toArray()).to_equal(["c", "d", "e"])
expect(buffer.getRecent(2)).to_equal(["d", "e"])
```

</details>

#### returns empty arrays for empty, zero recent count, and clear

- Exercise the empty and cleared states
   - Expected: buffer.toArray() equals `[]`
   - Expected: buffer.getRecent(1) equals `[]`
- buffer addAll
   - Expected: buffer.getRecent(0) equals `[]`
- buffer clear
   - Expected: buffer.length() equals `0`
   - Expected: buffer.toArray() equals `[]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Exercise the empty and cleared states")
val buffer = CircularBuffer.new(2)
expect(buffer.toArray()).to_equal([])
expect(buffer.getRecent(1)).to_equal([])

buffer.addAll(["x", "y"])
expect(buffer.getRecent(0)).to_equal([])
buffer.clear()

expect(buffer.length()).to_equal(0)
expect(buffer.toArray()).to_equal([])
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
