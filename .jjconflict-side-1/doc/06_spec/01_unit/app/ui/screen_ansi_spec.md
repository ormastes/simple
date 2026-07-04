# Screen Ansi Specification

> 1. var s = Screen new

<!-- sdn-diagram:id=screen_ansi_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=screen_ansi_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

screen_ansi_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=screen_ansi_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 20 | 17 | 0 | 3 |

<details>
<summary>Full Scenario Manual</summary>

# Screen Ansi Specification

## Scenarios

#### {pending}{ch} _(pending)_
#### {pending}{ch} _(pending)_
####  _(pending)_
### Screen.put_text ANSI style splice

### compound RESET+STYLE prefix tokens

#### col 0 is BOLD, col 2 is CYAN, col 4 is unstyled after overwrite

1. var s = Screen new
2. s = s put styled
3. s = s put styled
4. s = s put text
5. expect style at col
6. expect char at col
7. expect style at col
8. expect char at col
9. expect style at col
10. expect char at col


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_styled(0, 0, "AB", BOLD)
s = s.put_styled(0, 2, "CD", CYAN)
s = s.put_text(0, 4, "X")
val line = s.buffer[0]
# col 0: A with BOLD
expect style_at_col(line, 0) to_equal(BOLD)
expect char_at_col(line, 0) to_equal("A")
# col 2: C with CYAN (compound token parsed correctly)
expect style_at_col(line, 2).contains("\u{001b}[36m") to_equal(true)
expect char_at_col(line, 2) to_equal("C")
# col 4: X should be unstyled (gap RESET cleared prefix CYAN)
expect style_at_col(line, 4) to_equal("")
expect char_at_col(line, 4) to_equal("X")
```

</details>

#### mid-block overwrite inside CYAN preserves CYAN for suffix

1. var s = Screen new
2. s = s put styled
3. s = s put styled
4. s = s put text
5. expect style at col
6. expect style at col
7. expect char at col


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_styled(0, 0, "AB", BOLD)
s = s.put_styled(0, 2, "CDEF", CYAN)
s = s.put_text(0, 3, "X")
val line = s.buffer[0]
# col 2: C with CYAN (prefix, unchanged)
expect style_at_col(line, 2).contains("\u{001b}[36m") to_equal(true)
# col 4: E should still be CYAN (suffix style restored)
expect style_at_col(line, 4).contains("\u{001b}[36m") to_equal(true)
expect char_at_col(line, 4) to_equal("E")
```

</details>

### suffix style restore across block boundary

#### keeps CYAN on suffix B after overwriting across BOLD/CYAN boundary

1. var s = Screen new
2. s = s put styled
3. s = s put styled
4. s = s put text
5. expect style at col
6. expect char at col
7. expect style at col
8. expect char at col
9. expect style at col


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_styled(0, 0, "AAA", BOLD)
s = s.put_styled(0, 3, "BBB", CYAN)
s = s.put_text(0, 2, "XX")
val line = s.buffer[0]
# col 0: A still BOLD
expect style_at_col(line, 0) to_equal(BOLD)
# col 2: X (overwrite) should be unstyled
expect char_at_col(line, 2) to_equal("X")
expect style_at_col(line, 2) to_equal("")
# col 4: B should be CYAN (style restored for suffix)
expect char_at_col(line, 4) to_equal("B")
expect style_at_col(line, 4).contains("\u{001b}[36m") to_equal(true)
```

</details>

#### restores CYAN when overwriting the first char of a CYAN block

1. var s = Screen new
2. s = s put styled
3. s = s put text
4. expect char at col
5. expect char at col
6. expect style at col


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_styled(0, 3, "HELLO", CYAN)
s = s.put_text(0, 3, "X")
val line = s.buffer[0]
# col 3: X is the overwrite — unstyled
expect char_at_col(line, 3) to_equal("X")
# col 4: E should still be CYAN
expect char_at_col(line, 4) to_equal("E")
expect style_at_col(line, 4).contains("\u{001b}[36m") to_equal(true)
```

</details>

### partial overwrite inside styled block

#### suffix keeps BOLD, overwritten char does not

1. var s = Screen new
2. s = s put styled
3. s = s put text
4. expect style at col
5. expect char at col
6. expect style at col
7. expect char at col
8. expect style at col
9. expect style at col


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_styled(0, 0, "ABCDE", BOLD)
s = s.put_text(0, 2, "X")
val line = s.buffer[0]
# col 0: A is BOLD (prefix)
expect style_at_col(line, 0) to_equal(BOLD)
# col 2: X is overwrite — should NOT be BOLD
expect char_at_col(line, 2) to_equal("X")
expect style_at_col(line, 2) to_equal("")
# col 3: C should still be BOLD (suffix style restored)
expect char_at_col(line, 3) to_equal("C")
expect style_at_col(line, 3) to_equal(BOLD)
# col 4: D should still be BOLD
expect style_at_col(line, 4) to_equal(BOLD)
```

</details>

### RESET not lost past styled block end

#### BOLD does not bleed into plain overwrite at boundary

1. var s = Screen new
2. s = s put styled
3. s = s put text
4. expect style at col
5. expect char at col
6. expect style at col
7. expect style at col


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_styled(0, 0, "AB", BOLD)
s = s.put_text(0, 2, "XY")
val line = s.buffer[0]
# col 0: A is BOLD
expect style_at_col(line, 0) to_equal(BOLD)
# col 2: X must be unstyled
expect char_at_col(line, 2) to_equal("X")
expect style_at_col(line, 2) to_equal("")
# col 3: Y must be unstyled
expect style_at_col(line, 3) to_equal("")
```

</details>

### cross-row style leak prevention

#### row ends with RESET after full-width styled write + partial overwrite

1. var s = Screen new
2. s = s put styled
3. s = s put text
4. expect ends with reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(5, 2)
s = s.put_styled(0, 0, "ABCDE", BOLD)
s = s.put_text(0, 3, "X")
expect ends_with_reset(s.buffer[0]) to_equal(true)
```

</details>

#### row ends with RESET after end-of-line styled write + overwrite

1. var s = Screen new
2. s = s put styled
3. s = s put text
4. expect ends with reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 2)
s = s.put_styled(0, 7, "ABC", CYAN)
s = s.put_text(0, 8, "X")
expect ends_with_reset(s.buffer[0]) to_equal(true)
```

</details>

#### row 1 is not affected by row 0 style

1. var s = Screen new
2. s = s put styled
3. s = s put text
4. s = s put text
5. expect style at col


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(5, 2)
s = s.put_styled(0, 0, "HELLO", BOLD)
s = s.put_text(0, 2, "X")
s = s.put_text(1, 0, "plain")
# row 1 col 0 should be unstyled
expect style_at_col(s.buffer[1], 0) to_equal("")
```

</details>

### visible width stability

#### stable after 5 overlapping writes

1. var s = Screen new
2. s = s put styled
3. s = s put text
4. s = s put text
5. s = s put styled
6. s = s put text
7. expect visible width


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_styled(0, 0, "ABCDE", BOLD)
s = s.put_text(0, 1, "X")
s = s.put_text(0, 3, "Y")
s = s.put_styled(0, 5, "ZZ", CYAN)
s = s.put_text(0, 7, "W")
expect visible_width(s.buffer[0]) to_equal(10)
```

</details>

#### stable after three styled blocks + gap overwrite

1. var s = Screen new
2. s = s put styled
3. s = s put styled
4. s = s put styled
5. s = s put text
6. expect visible width


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(20, 1)
s = s.put_styled(0, 0, "AAA", BOLD)
s = s.put_styled(0, 5, "BBB", CYAN)
s = s.put_styled(0, 10, "CCC", DIM)
s = s.put_text(0, 3, "X")
expect visible_width(s.buffer[0]) to_equal(20)
```

</details>

#### clips plain text at the right edge without growing the row

1. var s = Screen new
2. s = s put text
3. expect visible width
4. expect char at col
5. expect char at col
6. expect char at col


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_text(0, 8, "ABCDE")
expect visible_width(s.buffer[0]) to_equal(10)
expect char_at_col(s.buffer[0], 8) to_equal("A")
expect char_at_col(s.buffer[0], 9) to_equal("B")
expect char_at_col(s.buffer[0], 10) to_equal("")
```

</details>

#### clips styled text at the right edge and terminates style

1. var s = Screen new
2. s = s put styled
3. expect visible width
4. expect char at col
5. expect char at col
6. expect char at col
7. expect style at col
8. expect ends with reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_styled(0, 7, "ABCDE", CYAN)
val line = s.buffer[0]
expect visible_width(line) to_equal(10)
expect char_at_col(line, 7) to_equal("A")
expect char_at_col(line, 9) to_equal("C")
expect char_at_col(line, 10) to_equal("")
expect style_at_col(line, 7).contains("\u{001b}[36m") to_equal(true)
expect ends_with_reset(line) to_equal(true)
```

</details>

### round-trip stability

#### two successive overwrites on same row produce correct styles

1. var s = Screen new
2. s = s put styled
3. s = s put styled
4. s = s put text
5. s = s put text
6. expect style at col
7. expect char at col
8. expect style at col
9. expect style at col
10. expect style at col
11. expect char at col
12. expect style at col
13. expect style at col
14. expect visible width
15. expect ends with reset


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(10, 1)
s = s.put_styled(0, 0, "ABCDE", BOLD)
s = s.put_styled(0, 5, "FGHIJ", CYAN)
# First overwrite: plain X at col 3
s = s.put_text(0, 3, "X")
# Second overwrite: plain Y at col 7 (reads the spliced line)
s = s.put_text(0, 7, "Y")
val line = s.buffer[0]
# col 0: BOLD A
expect style_at_col(line, 0) to_equal(BOLD)
# col 3: X unstyled
expect char_at_col(line, 3) to_equal("X")
expect style_at_col(line, 3) to_equal("")
# col 4: D still BOLD (suffix restored from first overwrite)
expect style_at_col(line, 4) to_equal(BOLD)
# col 5: F still CYAN
expect style_at_col(line, 5).contains("\u{001b}[36m") to_equal(true)
# col 7: Y unstyled
expect char_at_col(line, 7) to_equal("Y")
expect style_at_col(line, 7) to_equal("")
# col 8: I still CYAN (suffix restored from second overwrite)
expect style_at_col(line, 8).contains("\u{001b}[36m") to_equal(true)
# visible width must be 10
expect visible_width(line) to_equal(10)
# line must end with RESET
expect ends_with_reset(line) to_equal(true)
```

</details>

### plain text and styled text contiguity

#### plain text is contiguous for .contains()

1. var s = Screen new
2. s = s put text
3. s = s put text
4. expect s buffer[0] contains
5. expect s buffer[0] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(20, 1)
s = s.put_text(0, 0, "Hello")
s = s.put_text(0, 10, "World")
expect s.buffer[0].contains("Hello") to_equal(true)
expect s.buffer[0].contains("World") to_equal(true)
```

</details>

#### styled text is contiguous within a single put_styled

1. var s = Screen new
2. s = s put styled
3. s = s put styled
4. expect s buffer[0] contains
5. expect s buffer[0] contains


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(20, 1)
s = s.put_styled(0, 0, "Bold", BOLD)
s = s.put_styled(0, 10, "Cyan", CYAN)
expect s.buffer[0].contains("Bold") to_equal(true)
expect s.buffer[0].contains("Cyan") to_equal(true)
```

</details>

### Unicode box drawing

#### draw_box renders corners and borders at correct positions

1. var s = Screen new
2. s = s draw box
3. expect char at col
4. expect char at col
5. expect char at col
6. expect char at col
7. expect char at col
8. expect char at col


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = Screen.new(20, 5)
s = s.draw_box(0, 0, 20, 5, "Test")
expect char_at_col(s.buffer[0], 0) to_equal("\u{250c}")
expect char_at_col(s.buffer[0], 19) to_equal("\u{2510}")
expect char_at_col(s.buffer[4], 0) to_equal("\u{2514}")
expect char_at_col(s.buffer[4], 19) to_equal("\u{2518}")
# Sides
expect char_at_col(s.buffer[2], 0) to_equal("\u{2502}")
expect char_at_col(s.buffer[2], 19) to_equal("\u{2502}")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/01_unit/app/ui/screen_ansi_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Screen.put_text ANSI style splice
- compound RESET+STYLE prefix tokens
- suffix style restore across block boundary
- partial overwrite inside styled block
- RESET not lost past styled block end
- cross-row style leak prevention
- visible width stability
- round-trip stability
- plain text and styled text contiguity
- Unicode box drawing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 20 |
| Active scenarios | 17 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 3 |


</details>
