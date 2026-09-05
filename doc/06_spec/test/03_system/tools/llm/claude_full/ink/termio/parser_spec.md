# Claude Full Termio Parser

> Checks ANSI parser parity: grapheme width, CSI actions, OSC link state, SGR

<!-- sdn-diagram:id=parser_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=parser_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

parser_spec -> std
parser_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=parser_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Termio Parser

Checks ANSI parser parity: grapheme width, CSI actions, OSC link state, SGR

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/termio/parser_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks ANSI parser parity: grapheme width, CSI actions, OSC link state, SGR
style state, BEL handling, and incomplete streaming sequences.

## Scenarios

### Claude full termio parser

#### should classify emoji, wide, and multi-codepoint graphemes

- Measure grapheme display widths
   - Expected: isEmoji(128512) is true
   - Expected: isEastAsianWide(4352) is true
   - Expected: hasMultipleCodepoints("ab") is true
   - Expected: graphemeWidth("a") equals `1`
   - Expected: graphemeWidth("ab") equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Measure grapheme display widths")
expect(isEmoji(128512)).to_equal(true)
expect(isEastAsianWide(4352)).to_equal(true)
expect(hasMultipleCodepoints("ab")).to_equal(true)
expect(graphemeWidth("a")).to_equal(1)
expect(graphemeWidth("ab")).to_equal(2)
```

</details>

#### should parse CSI parameters with semicolon and colon separators

- Parse CSI params
   - Expected: params[0] equals `12`
   - Expected: params[1] equals `0`
   - Expected: params[2] equals `4`
   - Expected: params[3] equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse CSI params")
val params = parseCSIParams("12;;4:5")
expect(params[0]).to_equal(12)
expect(params[1]).to_equal(0)
expect(params[2]).to_equal(4)
expect(params[3]).to_equal(5)
```

</details>

#### should parse cursor movement and position CSI sequences

- Parse cursor controls
   - Expected: parseCSI("\u001B[3A").direction equals `up`
   - Expected: parseCSI("\u001B[2;4H").actionType equals `position`
   - Expected: parseCSI("\u001B[2;4H").row equals `2`
   - Expected: parseCSI("\u001B[2;4H").col equals `4`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Parse cursor controls")
expect(parseCSI("\u001B[3A").direction).to_equal("up")
expect(parseCSI("\u001B[2;4H").actionType).to_equal("position")
expect(parseCSI("\u001B[2;4H").row).to_equal(2)
expect(parseCSI("\u001B[2;4H").col).to_equal(4)
```

</details>

#### should parse erase, scroll, cursor style, and private modes

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

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Identify escape prefixes
   - Expected: identifySequence("\u001B[31m") equals `csi`
   - Expected: identifySequence("\u001B]8;;url\u0007") equals `osc`
   - Expected: identifySequence("\u001BOA") equals `ss3`
   - Expected: identifySequence("x") equals `unknown`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Identify escape prefixes")
expect(identifySequence("\u001B[31m")).to_equal("csi")
expect(identifySequence("\u001B]8;;url\u0007")).to_equal("osc")
expect(identifySequence("\u001BOA")).to_equal("ss3")
expect(identifySequence("x")).to_equal("unknown")
```

</details>

#### should maintain style state while feeding text

- Feed SGR and text
   - Expected: actions.len() equals `1`
   - Expected: actions[0].type equals `text`
   - Expected: actions[0].textValue equals `red`
   - Expected: actions[0].styleParams equals `31`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Feed SGR and text")
val parser = Parser.new()
val actions = parser.feed("\u001B[31mred")
expect(actions.len()).to_equal(1)
expect(actions[0].type).to_equal("text")
expect(actions[0].textValue).to_equal("red")
expect(actions[0].styleParams).to_equal("31")
```

</details>

#### should emit bell actions embedded in text

- Feed text with BEL
   - Expected: actions.len() equals `3`
   - Expected: actions[0].textValue equals `a`
   - Expected: actions[1].type equals `bell`
   - Expected: actions[2].textValue equals `b`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Feed text with BEL")
val parser = Parser.new()
val actions = parser.feed("a\u0007b")
expect(actions.len()).to_equal(3)
expect(actions[0].textValue).to_equal("a")
expect(actions[1].type).to_equal("bell")
expect(actions[2].textValue).to_equal("b")
```

</details>

#### should maintain OSC link state

- Feed link start and end OSC
   - Expected: start[0].type equals `link`
   - Expected: start[0].actionType equals `start`
   - Expected: parser.inLink is true
   - Expected: parser.linkUrl equals `https://example.com`
   - Expected: stop[0].actionType equals `end`
   - Expected: parser.inLink is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Feed partial CSI then complete it
   - Expected: parser.feed("\u001B[").len() equals `0`
   - Expected: actions[0].type equals `erase`
   - Expected: actions[0].region equals `all`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Feed partial CSI then complete it")
val parser = Parser.new()
expect(parser.feed("\u001B[").len()).to_equal(0)
val actions = parser.feed("2K")
expect(actions[0].type).to_equal("erase")
expect(actions[0].region).to_equal("all")
```

</details>

#### should reset parser state

- Reset style and link state
- parser feed
- parser reset
   - Expected: parser.style.params equals ``
   - Expected: parser.inLink is false
   - Expected: parser.pending equals ``
   - Expected: parserSourceLinesModeled() equals `394`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Reset style and link state")
val parser = Parser.new()
parser.feed("\u001B[31m\u001B]8;;url\u0007")
parser.reset()
expect(parser.style.params).to_equal("")
expect(parser.inLink).to_equal(false)
expect(parser.pending).to_equal("")
expect(parserSourceLinesModeled()).to_equal(394)
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
