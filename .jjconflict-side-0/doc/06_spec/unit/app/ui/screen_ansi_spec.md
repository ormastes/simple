# Screen Ansi Specification

> Tests covering Screen.put_text ANSI style splice, compound RESET+STYLE prefix tokens, suffix style restore across block boundary, partial overwrite inside styled block, RESET not lost past styled block end, cross-row style leak prevention, visible width stability, round-trip stability, plain text and styled text contiguity, Unicode box drawing.

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

- col 0 is BOLD, col 2 is CYAN, col 4 is unstyled after overwrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("col 0 is BOLD, col 2 is CYAN, col 4 is unstyled after overwrite")
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

- mid-block overwrite inside CYAN preserves CYAN for suffix


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("mid-block overwrite inside CYAN preserves CYAN for suffix")
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

- keeps CYAN on suffix B after overwriting across BOLD/CYAN boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps CYAN on suffix B after overwriting across BOLD/CYAN boundary")
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

- restores CYAN when overwriting the first char of a CYAN block


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("restores CYAN when overwriting the first char of a CYAN block")
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

- suffix keeps BOLD, overwritten char does not


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("suffix keeps BOLD, overwritten char does not")
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

- BOLD does not bleed into plain overwrite at boundary


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("BOLD does not bleed into plain overwrite at boundary")
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

- row ends with RESET after full-width styled write + partial overwrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row ends with RESET after full-width styled write + partial overwrite")
var s = Screen.new(5, 2)
s = s.put_styled(0, 0, "ABCDE", BOLD)
s = s.put_text(0, 3, "X")
expect ends_with_reset(s.buffer[0]) to_equal(true)
```

</details>

#### row ends with RESET after end-of-line styled write + overwrite

- row ends with RESET after end-of-line styled write + overwrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row ends with RESET after end-of-line styled write + overwrite")
var s = Screen.new(10, 2)
s = s.put_styled(0, 7, "ABC", CYAN)
s = s.put_text(0, 8, "X")
expect ends_with_reset(s.buffer[0]) to_equal(true)
```

</details>

#### row 1 is not affected by row 0 style

- row 1 is not affected by row 0 style


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("row 1 is not affected by row 0 style")
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

- stable after 5 overlapping writes


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stable after 5 overlapping writes")
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

- stable after three styled blocks + gap overwrite


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stable after three styled blocks + gap overwrite")
var s = Screen.new(20, 1)
s = s.put_styled(0, 0, "AAA", BOLD)
s = s.put_styled(0, 5, "BBB", CYAN)
s = s.put_styled(0, 10, "CCC", DIM)
s = s.put_text(0, 3, "X")
expect visible_width(s.buffer[0]) to_equal(20)
```

</details>

#### clips plain text at the right edge without growing the row

- clips plain text at the right edge without growing the row


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clips plain text at the right edge without growing the row")
var s = Screen.new(10, 1)
s = s.put_text(0, 8, "ABCDE")
expect visible_width(s.buffer[0]) to_equal(10)
expect char_at_col(s.buffer[0], 8) to_equal("A")
expect char_at_col(s.buffer[0], 9) to_equal("B")
expect char_at_col(s.buffer[0], 10) to_equal("")
```

</details>

#### clips styled text at the right edge and terminates style

- clips styled text at the right edge and terminates style


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("clips styled text at the right edge and terminates style")
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

- two successive overwrites on same row produce correct styles


<details>
<summary>Executable SSpec</summary>

Runnable source: 28 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("two successive overwrites on same row produce correct styles")
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

- plain text is contiguous for .contains()


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("plain text is contiguous for .contains()")
var s = Screen.new(20, 1)
s = s.put_text(0, 0, "Hello")
s = s.put_text(0, 10, "World")
expect s.buffer[0].contains("Hello") to_equal(true)
expect s.buffer[0].contains("World") to_equal(true)
```

</details>

#### styled text is contiguous within a single put_styled

- styled text is contiguous within a single put_styled


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("styled text is contiguous within a single put_styled")
var s = Screen.new(20, 1)
s = s.put_styled(0, 0, "Bold", BOLD)
s = s.put_styled(0, 10, "Cyan", CYAN)
expect s.buffer[0].contains("Bold") to_equal(true)
expect s.buffer[0].contains("Cyan") to_equal(true)
```

</details>

### Unicode box drawing

#### draw_box renders corners and borders at correct positions

- draw_box renders corners and borders at correct positions


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("draw_box renders corners and borders at correct positions")
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
| Source | `test/unit/app/ui/screen_ansi_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Screen.put_text ANSI style splice, compound RESET+STYLE prefix tokens, suffix style restore across block boundary, partial overwrite inside styled block, RESET not lost past styled block end, cross-row style leak prevention, visible width stability, round-trip stability, plain text and styled text contiguity, Unicode box drawing.
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3f1a75ad417a6e9f3b83893c8c97df85be5c3af58485642474fb1fefd0e64cb2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3f1a75ad417a6e9f3b83893c8c97df85be5c3af58485642474fb1fefd0e64cb2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3f1a75ad417a6e9f3b83893c8c97df85be5c3af58485642474fb1fefd0e64cb2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/app/ui/screen_ansi_spec.spl
mirror: doc/06_spec/unit/app/ui/screen_ansi_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/ui/screen_ansi_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/ui/screen_ansi_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/ui/screen_ansi_spec.spl:124:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'col 0 is BOLD, col 2 is CYAN, col 4 is unstyled after overwrite' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/screen_ansi_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'mid-block overwrite inside CYAN preserves CYAN for suffix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/ui/screen_ansi_spec.spl:158:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps CYAN on suffix B after overwriting across BOLD/CYAN boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
