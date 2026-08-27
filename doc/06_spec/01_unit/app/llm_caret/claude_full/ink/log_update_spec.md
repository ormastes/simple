# Log Update Specification

> Tests covering ink VirtualScreen, ink LogUpdate.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Log Update Specification

## Scenarios

### ink VirtualScreen

#### starts at the supplied origin with an empty diff
#### appends patches and advances the cursor by the declared delta

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var s = VirtualScreen.new(LogPoint.new(0, 0), 80)
s.txn([LogDiffOp.stdout("abc")], 3, 0)
s.txn([LogDiffOp.carriageReturn(), LogDiffOp.newline()], -3, 1)
expect(s.diff.len()).to_equal(3)
expect(s.cursor.x).to_equal(0)
expect(s.cursor.y).to_equal(1)
expect(s.diff[0].kind).to_equal("stdout")
expect(s.diff[1].kind).to_equal("carriageReturn")
```

</details>

#### does not alias the origin point it was constructed from

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var origin = LogPoint.new(1, 1)
var s = VirtualScreen.new(origin, 80)
s.txn([LogDiffOp.stdout("x")], 5, 5)
expect(origin.x).to_equal(1)
expect(origin.y).to_equal(1)
```

</details>

### ink LogUpdate

#### renders a non-TTY frame as a single trimmed stdout write

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ops = nonTty().renderFullFrame(logFrame(["a  ", "b"], 80, 10))
expect(ops.len()).to_equal(1)
expect(ops[0].kind).to_equal("stdout")
expect(ops[0].content).to_equal("a\nb")
```

</details>

#### renders an empty frame as no operations at all

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(nonTty().renderFullFrame(logFrame([], 80, 10)).len()).to_equal(0)
```

</details>

#### emits a bare newline for a non-TTY previous-output render

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ops = nonTty().renderPreviousOutput_DEPRECATED(logFrame(["a"], 80, 10))
expect(ops.len()).to_equal(1)
expect(ops[0].content).to_equal("\n")
```

</details>

#### restores a hidden cursor when the frame is done and clears previous output

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lu = LogUpdate.defaultTTY()
lu.previousOutput = "stale"
val ops = lu.getRenderOpsForDone(logFrame(["a"], 80, 10).withCursor(0, 1, false))
expect(ops.len()).to_equal(1)
expect(ops[0].kind).to_equal("cursorShow")
expect(lu.previousOutput).to_equal("")
```

</details>

#### emits nothing extra when the cursor is already visible

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LogUpdate.defaultTTY().getRenderOpsForDone(logFrame(["a"], 80, 10)).len()).to_equal(0)
```

</details>

#### falls back to a full clear+redraw when the viewport width changes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prev = logFrame(["a"], 80, 10)
val next = logFrame(["a"], 60, 10)
val ops = LogUpdate.defaultTTY().render(prev, next, false, false)
expect(ops[0].kind).to_equal("clearTerminal")
expect(ops[0].reason).to_equal("resize")
```

</details>

#### falls back to a full clear+redraw when the viewport shrinks vertically

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ops = LogUpdate.defaultTTY().render(logFrame(["a"], 80, 10), logFrame(["a"], 80, 8), false, false)
expect(ops[0].kind).to_equal("clearTerminal")
expect(ops[0].reason).to_equal("resize")
```

</details>

#### emits a stdout op for a line that actually changed

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prev = logFrame(["hello"], 80, 10)
val next = logFrame(["world"], 80, 10)
expect(stdoutText(LogUpdate.defaultTTY().render(prev, next, true, false)).contains("world")).to_equal(true)
```

</details>

#### emits no stdout text when the frame is unchanged

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val frame = logFrame(["hello"], 80, 10)
expect(stdoutText(LogUpdate.defaultTTY().render(frame, frame, true, false))).to_equal("")
```

</details>

#### clears the surplus rows when the next frame has fewer lines

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prev = logFrame(["a", "b", "c"], 80, 10)
val next = logFrame(["a"], 80, 10)
val kinds = diffKinds(LogUpdate.defaultTTY().render(prev, next, true, false))
expect(kinds.len() > 0).to_equal(true)
expect(kinds[0]).to_equal("clear")
```

</details>

#### prepends a scroll op only when DECSTBM is safe and a delta exists

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val prev = logFrame(["a"], 80, 10)
val next = logFrame(["a"], 80, 10).withScroll(1, 9, 2)
val withScroll = LogUpdate.defaultTTY().render(prev, next, true, true)
expect(stdoutText(withScroll).contains("scroll:1:9:2")).to_equal(true)
val without = LogUpdate.defaultTTY().render(prev, next, true, false)
expect(stdoutText(without).contains("scroll:")).to_equal(false)
```

</details>

#### reset clears the retained previous output

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var lu = LogUpdate.defaultTTY()
lu.previousOutput = "stale"
lu.reset()
expect(lu.previousOutput).to_equal("")
```

</details>

#### joins frame lines with newlines after trimming trailing spaces

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(joinTrimmedLines(["a  ", "  b  ", ""])).to_equal("a\n  b\n")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/llm_caret/claude_full/ink/log_update_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ink VirtualScreen, ink LogUpdate.
- ink VirtualScreen
- ink LogUpdate

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b8319ee248f65b50fe0863057ee160c1343313c31ab9739a196e81b688ff76a6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b8319ee248f65b50fe0863057ee160c1343313c31ab9739a196e81b688ff76a6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b8319ee248f65b50fe0863057ee160c1343313c31ab9739a196e81b688ff76a6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **77/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/llm_caret/claude_full/ink/log_update_spec.spl
mirror: doc/06_spec/01_unit/app/llm_caret/claude_full/ink/log_update_spec.md (current)
findings: 9 blockers: 1
  narrative=100 structure=60 oracle=70
  traceability=60 evidence=100 coverage=100 maintainability=55
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=77; blocker cap makes effective=49
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/log_update_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/llm_caret/claude_full/ink/log_update_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/llm_caret/claude_full/ink/log_update_spec.spl:1:1: advice SSDOC-MNT-001 [maintainability] (-15): multiple scenarios form a flat, unfolded presentation
  why: Long flat dumps obscure the primary workflow.
  improve: Group secondary detail and keep the primary workflow visible.
test/01_unit/app/llm_caret/claude_full/ink/log_update_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/llm_caret/claude_full/ink/log_update_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/llm_caret/claude_full/ink/log_update_spec.spl:21:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'starts at the supplied origin with an empty diff' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/log_update_spec.spl:30:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'appends patches and advances the cursor by the declared delta' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/log_update_spec.spl:41:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'does not alias the origin point it was constructed from' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/llm_caret/claude_full/ink/log_update_spec.spl:51:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'renders a non-TTY frame as a single trimmed stdout write' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
<!-- sspec-maintain:scorecard:end -->
