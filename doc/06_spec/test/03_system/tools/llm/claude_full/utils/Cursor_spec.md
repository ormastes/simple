# Claude Full Cursor

> Checks cursor, wrapped line, and measured text surfaces.

<!-- sdn-diagram:id=Cursor_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=Cursor_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

Cursor_spec -> std
Cursor_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=Cursor_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Cursor

Checks cursor, wrapped line, and measured text surfaces.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/utils/Cursor_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks cursor, wrapped line, and measured text surfaces.

## Scenarios

### Claude full Cursor

#### should clamp offsets and compute wrapped positions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val measured = MeasuredText.new("abcdef", 3)
val cursor = Cursor.new(measured, 99, 0)
expect(cursor.offset).to_equal(6)
expect(measured.getWrappedText()).to_equal(["abc", "def"])
expect(measured.getPositionFromOffset(4).line).to_equal(1)
expect(measured.getOffsetFromPosition(Position.new(1, 1))).to_equal(4)
```

</details>

#### should move and edit text

- var cursor = Cursor fromText
   - Expected: cursor.left().offset equals `0`
   - Expected: cursor.right().offset equals `2`
- cursor = cursor insert
   - Expected: cursor.text() equals `aZbc`
   - Expected: cursor.backspace().text() equals `abc`
   - Expected: cursor.del().text() equals `aZc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var cursor = Cursor.fromText("abc", 4, 1, 0)
expect(cursor.left().offset).to_equal(0)
expect(cursor.right().offset).to_equal(2)
cursor = cursor.insert("Z")
expect(cursor.text()).to_equal("aZbc")
expect(cursor.backspace().text()).to_equal("abc")
expect(cursor.del().text()).to_equal("aZc")
```

</details>

#### should expose viewport line and wrapped line helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cursor = Cursor.fromText("abcdefghi", 4, 5, 0)
expect(cursor.getViewportStartLine(2)).to_equal(0)
expect(cursor.getViewportCharEnd(2)).to_equal(6)
val line = WrappedLine.new("abc", 0, false, true)
expect(line.length()).to_equal(4)
expect(line.text).to_equal("abc")
```

</details>

#### should expose vim classification and source size

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(isVimWordChar("_")).to_equal(true)
expect(isVimWhitespace(" ")).to_equal(true)
expect(isVimPunctuation("!")).to_equal(true)
expect(cursorSourceLinesModeled()).to_equal(1530)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
