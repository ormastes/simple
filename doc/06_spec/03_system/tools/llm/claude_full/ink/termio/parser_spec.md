# Claude Full Termio Parser

> Purpose: should classify emoji, wide, and multi-codepoint graphemes

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Termio Parser

Purpose: should classify emoji, wide, and multi-codepoint graphemes

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should classify emoji, wide, and multi-codepoint graphemes
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Termio Parser

Checks ANSI parser parity: grapheme width, CSI actions, OSC link state, SGR
style state, BEL handling, and incomplete streaming sequences.

## Scenarios

### Claude full termio parser

#### should classify emoji, wide, and multi-codepoint graphemes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should classify emoji, wide, and multi-codepoint graphemes
- Verify: should classify emoji, wide, and multi-codepoint graphemes
- Measure grapheme display widths
   - Expected: isEmoji(128512) is true
   - Expected: isEastAsianWide(4352) is true
   - Expected: hasMultipleCodepoints("ab") is true
   - Expected: graphemeWidth("a") equals `1`
   - Expected: graphemeWidth("ab") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify emoji, wide, and multi-codepoint graphemes")
step("Verify: should classify emoji, wide, and multi-codepoint graphemes")
# @req: REQ-TOOLS-Pars-001
step("Measure grapheme display widths")
expect(isEmoji(128512)).to_equal(true)
expect(isEastAsianWide(4352)).to_equal(true)
expect(hasMultipleCodepoints("ab")).to_equal(true)
expect(graphemeWidth("a")).to_equal(1)  # oracle: value fixed by the spec contract
expect(graphemeWidth("ab")).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### should parse CSI parameters with semicolon and colon separators

- should parse CSI parameters with semicolon and colon separators
- Verify: should parse CSI parameters with semicolon and colon separators
- Parse CSI params
   - Expected: params[0] equals `12`
   - Expected: params[1] equals `0`
   - Expected: params[2] equals `4`
   - Expected: params[3] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse CSI parameters with semicolon and colon separators")
step("Verify: should parse CSI parameters with semicolon and colon separators")
# @req: REQ-TOOLS-Pars-001
step("Parse CSI params")
val params = parseCSIParams("12;;4:5")
expect(params[0]).to_equal(12)  # oracle: value fixed by the spec contract
expect(params[1]).to_equal(0)  # oracle: value fixed by the spec contract
expect(params[2]).to_equal(4)  # oracle: value fixed by the spec contract
expect(params[3]).to_equal(5)  # oracle: value fixed by the spec contract
```

</details>

#### should parse cursor movement and position CSI sequences

- should parse cursor movement and position CSI sequences
- Verify: should parse cursor movement and position CSI sequences
- Parse cursor controls
   - Expected: parseCSI("\u001B[3A").direction equals `up`
   - Expected: parseCSI("\u001B[2;4H").actionType equals `position`
   - Expected: parseCSI("\u001B[2;4H").row equals `2`
   - Expected: parseCSI("\u001B[2;4H").col equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse cursor movement and position CSI sequences")
step("Verify: should parse cursor movement and position CSI sequences")
# @req: REQ-TOOLS-Pars-001
step("Parse cursor controls")
expect(parseCSI("\u001B[3A").direction).to_equal("up")
expect(parseCSI("\u001B[2;4H").actionType).to_equal("position")
expect(parseCSI("\u001B[2;4H").row).to_equal(2)  # oracle: value fixed by the spec contract
expect(parseCSI("\u001B[2;4H").col).to_equal(4)  # oracle: value fixed by the spec contract
```

</details>

#### should parse erase, scroll, cursor style, and private modes

- should parse erase, scroll, cursor style, and private modes
- Verify: should parse erase, scroll, cursor style, and private modes
- Parse non-text CSI controls
   - Expected: parseCSI("\u001B[2J").region equals `all`
   - Expected: parseCSI("\u001B[3S").actionType equals `up`
   - Expected: parseCSI("\u001B[5 q").direction equals `bar`
   - Expected: hidden.type equals `cursor`
   - Expected: hidden.actionType equals `hide`
   - Expected: paste.type equals `mode`
   - Expected: paste.enabled is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should parse erase, scroll, cursor style, and private modes")
step("Verify: should parse erase, scroll, cursor style, and private modes")
# @req: REQ-TOOLS-Pars-001
step("Parse non-text CSI controls")
expect(parseCSI("\u001B[2J").region).to_equal("all")
expect(parseCSI("\u001B[3S").actionType).to_equal("up")
expect(parseCSI("\u001B[5 q").direction).to_equal("bar")
val hidden = parseCSI("\u001B[?25l")
expect(hidden.type).to_equal("cursor")
expect(hidden.actionType).to_equal("hide")
val paste = parseCSI("\u001B[?2004h")
expect(paste.type).to_equal("mode")
expect(paste.enabled).to_equal(true)
```

</details>

#### should identify sequence families

- should identify sequence families
- Verify: should identify sequence families
- Identify escape prefixes
   - Expected: identifySequence("\u001B[31m") equals `csi`
   - Expected: identifySequence("\u001B]8;;url\u0007") equals `osc`
   - Expected: identifySequence("\u001BOA") equals `ss3`
   - Expected: identifySequence("x") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should identify sequence families")
step("Verify: should identify sequence families")
# @req: REQ-TOOLS-Pars-001
step("Identify escape prefixes")
expect(identifySequence("\u001B[31m")).to_equal("csi")
expect(identifySequence("\u001B]8;;url\u0007")).to_equal("osc")
expect(identifySequence("\u001BOA")).to_equal("ss3")
expect(identifySequence("x")).to_equal("unknown")
```

</details>

#### should maintain style state while feeding text

- should maintain style state while feeding text
- Verify: should maintain style state while feeding text
- Feed SGR and text
   - Expected: actions.len() equals `1`
   - Expected: actions[0].type equals `text`
   - Expected: actions[0].textValue equals `red`
   - Expected: actions[0].styleParams equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should maintain style state while feeding text")
step("Verify: should maintain style state while feeding text")
# @req: REQ-TOOLS-Pars-001
step("Feed SGR and text")
val parser = Parser.new()
val actions = parser.feed("\u001B[31mred")
expect(actions.len()).to_equal(1)  # oracle: value fixed by the spec contract
expect(actions[0].type).to_equal("text")
expect(actions[0].textValue).to_equal("red")
expect(actions[0].styleParams).to_equal("31")
```

</details>

#### should emit bell actions embedded in text

- should emit bell actions embedded in text
- Verify: should emit bell actions embedded in text
- Feed text with BEL
   - Expected: actions.len() equals `3`
   - Expected: actions[0].textValue equals `a`
   - Expected: actions[1].type equals `bell`
   - Expected: actions[2].textValue equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should emit bell actions embedded in text")
step("Verify: should emit bell actions embedded in text")
# @req: REQ-TOOLS-Pars-001
step("Feed text with BEL")
val parser = Parser.new()
val actions = parser.feed("a\u0007b")
expect(actions.len()).to_equal(3)  # oracle: value fixed by the spec contract
expect(actions[0].textValue).to_equal("a")
expect(actions[1].type).to_equal("bell")
expect(actions[2].textValue).to_equal("b")
```

</details>

#### should maintain OSC link state

- should maintain OSC link state
- Verify: should maintain OSC link state
- Feed link start and end OSC
   - Expected: start[0].type equals `link`
   - Expected: start[0].actionType equals `start`
   - Expected: parser.inLink is true
   - Expected: parser.linkUrl equals `https://example.com`
   - Expected: stop[0].actionType equals `end`
   - Expected: parser.inLink is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should maintain OSC link state")
step("Verify: should maintain OSC link state")
# @req: REQ-TOOLS-Pars-001
step("Feed link start and end OSC")
val parser = Parser.new()
val start = parser.feed("\u001B]8;;https://example.com\u0007")
expect(start[0].type).to_equal("link")
expect(start[0].actionType).to_equal("start")
expect(parser.inLink).to_equal(true)
expect(parser.linkUrl).to_equal("https://example.com")
val stop = parser.feed("\u001B]8;;\u0007")
expect(stop[0].actionType).to_equal("end")
expect(parser.inLink).to_equal(false)
```

</details>

#### should buffer incomplete escape sequences across feeds

- should buffer incomplete escape sequences across feeds
- Verify: should buffer incomplete escape sequences across feeds
- Feed partial CSI then complete it
   - Expected: parser.feed("\u001B[").len() equals `0`
   - Expected: actions[0].type equals `erase`
   - Expected: actions[0].region equals `all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should buffer incomplete escape sequences across feeds")
step("Verify: should buffer incomplete escape sequences across feeds")
# @req: REQ-TOOLS-Pars-001
step("Feed partial CSI then complete it")
val parser = Parser.new()
expect(parser.feed("\u001B[").len()).to_equal(0)  # oracle: value fixed by the spec contract
val actions = parser.feed("2K")
expect(actions[0].type).to_equal("erase")
expect(actions[0].region).to_equal("all")
```

</details>

#### should reset parser state

- should reset parser state
- Verify: should reset parser state
- Reset style and link state
   - Expected: parser.style.params equals ``
   - Expected: parser.inLink is false
   - Expected: parser.pending equals ``
   - Expected: parserSourceLinesModeled() equals `394`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should reset parser state")
step("Verify: should reset parser state")
# @req: REQ-TOOLS-Pars-001
step("Reset style and link state")
val parser = Parser.new()
parser.feed("\u001B[31m\u001B]8;;url\u0007")
parser.reset()
expect(parser.style.params).to_equal("")
expect(parser.inLink).to_equal(false)
expect(parser.pending).to_equal("")
expect(parserSourceLinesModeled()).to_equal(394)  # oracle: value fixed by the spec contract
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Pars-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d73c5470fdd13e0ffcd8abf3ff16bc2ca8e64447db3ec6d1c8c001fdb1e3ed39`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d73c5470fdd13e0ffcd8abf3ff16bc2ca8e64447db3ec6d1c8c001fdb1e3ed39`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d73c5470fdd13e0ffcd8abf3ff16bc2ca8e64447db3ec6d1c8c001fdb1e3ed39`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/termio/parser_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/termio/parser_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/termio/parser_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify emoji, wide, and multi-codepoint graphemes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should classify emoji, wide, and multi-codepoint graphemes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse CSI parameters with semicolon and colon separators' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse CSI parameters with semicolon and colon separators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl:49:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse cursor movement and position CSI sequences' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should parse cursor movement and position CSI sequences' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should parse erase, scroll, cursor style, and private modes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl:76:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should identify sequence families' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl:87:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should maintain style state while feeding text' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
