# Claude Full Native Color Diff

> Purpose: should detect color modes and syntax themes

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Native Color Diff

Purpose: should detect color modes and syntax themes

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should detect color modes and syntax themes
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Native Color Diff

Checks color-diff public API parity: color mode, ANSI escape conversion,
hunk rendering, file rendering, syntax theme, and native-module surface.

## Scenarios

### Claude full native color diff

#### should detect color modes and syntax themes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should detect color modes and syntax themes
- Verify: should detect color modes and syntax themes
- Select color mode and syntax theme
   - Expected: detectColorMode("ansi-dark", "truecolor") equals `ansi`
   - Expected: detectColorMode("dark", "24bit") equals `truecolor`
   - Expected: detectColorMode("light", "") equals `color256`
   - Expected: defaultSyntaxThemeName("dark") equals `Monokai Extended`
   - Expected: getSyntaxTheme("light").theme equals `GitHub`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should detect color modes and syntax themes")
step("Verify: should detect color modes and syntax themes")
# @req: REQ-TOOLS-Inde-001
step("Select color mode and syntax theme")
expect(detectColorMode("ansi-dark", "truecolor")).to_equal("ansi")
expect(detectColorMode("dark", "24bit")).to_equal("truecolor")
expect(detectColorMode("light", "")).to_equal("color256")
expect(defaultSyntaxThemeName("dark")).to_equal("Monokai Extended")
expect(getSyntaxTheme("light").theme).to_equal("GitHub")
```

</details>

#### should convert colors to terminal escapes

- should convert colors to terminal escapes
- Verify: should convert colors to terminal escapes
- Convert palette, default, truecolor, and 256-color escapes
   - Expected: colorToEscape(ansiIdx(3), true, "ansi") equals `\u001B[33m`
   - Expected: colorToEscape(Color.defaultBg(), false, "ansi") equals `\u001B[49m`
   - Expected: colorToEscape(rgb(1, 2, 3), true, "truecolor") equals `\u001B[38;2;1;2;3m`
   - Expected: colorToEscape(rgb(255, 255, 255), true, "color256") equals `\u001B[38;5;231m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should convert colors to terminal escapes")
step("Verify: should convert colors to terminal escapes")
# @req: REQ-TOOLS-Inde-001
step("Convert palette, default, truecolor, and 256-color escapes")
expect(colorToEscape(ansiIdx(3), true, "ansi")).to_equal("\u001B[33m")
expect(colorToEscape(Color.defaultBg(), false, "ansi")).to_equal("\u001B[49m")
expect(colorToEscape(rgb(1, 2, 3), true, "truecolor")).to_equal("\u001B[38;2;1;2;3m")
expect(colorToEscape(rgb(255, 255, 255), true, "color256")).to_equal("\u001B[38;5;231m")
```

</details>

#### should tokenize and pair adjacent diff lines

- should tokenize and pair adjacent diff lines
- Verify: should tokenize and pair adjacent diff lines
- Find word diff inputs
   - Expected: tokenize("a b").len() equals `3`
   - Expected: pairs[0].start equals `0`
   - Expected: pairs[0].end equals `1`
   - Expected: wordDiffStrings("old", "new").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should tokenize and pair adjacent diff lines")
step("Verify: should tokenize and pair adjacent diff lines")
# @req: REQ-TOOLS-Inde-001
step("Find word diff inputs")
expect(tokenize("a b").len()).to_equal(3)  # oracle: value fixed by the spec contract
val pairs = findAdjacentPairs(["-", "+", " "])
expect(pairs[0].start).to_equal(0)  # oracle: value fixed by the spec contract
expect(pairs[0].end).to_equal(1)  # oracle: value fixed by the spec contract
expect(wordDiffStrings("old", "new").len()).to_equal(2)  # oracle: value fixed by the spec contract
```

</details>

#### should render ColorDiff hunks with old and new line numbers

- should render ColorDiff hunks with old and new line numbers
- Verify: should render ColorDiff hunks with old and new line numbers
- Render a changed hunk


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render ColorDiff hunks with old and new line numbers")
step("Verify: should render ColorDiff hunks with old and new line numbers")
# @req: REQ-TOOLS-Inde-001
step("Render a changed hunk")
val hunk = Hunk.new(10, 1, 20, 1, ["-old", "+new", " same"])
val diff = ColorDiff.new(hunk, "", "src/app.ts", "")
val lines = diff.render("dark", 80, false)
expect(lines[0]).to_contain("-old")
expect(lines[0]).to_contain("10")
expect(lines[1]).to_contain("+new")
expect(lines[1]).to_contain("20")
expect(lines[2]).to_contain("typescript")
```

</details>

#### should dim deleted ColorDiff lines when requested

- should dim deleted ColorDiff lines when requested
- Verify: should dim deleted ColorDiff lines when requested
- Render dim deleted hunk


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should dim deleted ColorDiff lines when requested")
step("Verify: should dim deleted ColorDiff lines when requested")
# @req: REQ-TOOLS-Inde-001
step("Render dim deleted hunk")
val hunk = Hunk.new(1, 1, 1, 0, ["-gone"])
val lines = ColorDiff.new(hunk, "", "x.ts", "").render("ansi", 80, true)
expect(lines[0]).to_contain("\u001B[2m")
```

</details>

#### should render ColorFile lines and drop trailing empty line

- should render ColorFile lines and drop trailing empty line
- Verify: should render ColorFile lines and drop trailing empty line
- Render a whole file
   - Expected: lines.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should render ColorFile lines and drop trailing empty line")
step("Verify: should render ColorFile lines and drop trailing empty line")
# @req: REQ-TOOLS-Inde-001
step("Render a whole file")
val file = ColorFile.new("one\ntwo\n", "README.md")
val lines = file.render("light", 80, false)
expect(lines.len()).to_equal(2)  # oracle: value fixed by the spec contract
expect(lines[0]).to_contain("1 one")
expect(lines[0]).to_contain("markdown")
expect(lines[1]).to_contain("2 two")
```

</details>

#### should expose native module and source constants

- should expose native module and source constants
- Verify: should expose native module and source constants
- Pin public surface
   - Expected: native.hasColorDiff is true
   - Expected: native.hasColorFile is true
   - Expected: native.hasSyntaxTheme is true
   - Expected: hljs() equals `lazy-highlight-js`
   - Expected: colorDiffSourceLinesModeled() equals `999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose native module and source constants")
step("Verify: should expose native module and source constants")
# @req: REQ-TOOLS-Inde-001
step("Pin public surface")
val native = getNativeModule()
expect(native.hasColorDiff).to_equal(true)
expect(native.hasColorFile).to_equal(true)
expect(native.hasSyntaxTheme).to_equal(true)
expect(hljs()).to_equal("lazy-highlight-js")
expect(colorDiffSourceLinesModeled()).to_equal(999)  # oracle: value fixed by the spec contract
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
- `REQ-TOOLS-Inde-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6a316d48bde604e8f14dc31ffd07f3c9bb390d314f00325e36676c321165cd8b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6a316d48bde604e8f14dc31ffd07f3c9bb390d314f00325e36676c321165cd8b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6a316d48bde604e8f14dc31ffd07f3c9bb390d314f00325e36676c321165cd8b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl:25:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should detect color modes and syntax themes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl:25:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should detect color modes and syntax themes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl:37:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should convert colors to terminal escapes' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should convert colors to terminal escapes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl:48:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should tokenize and pair adjacent diff lines' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl:48:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should tokenize and pair adjacent diff lines' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl:60:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render ColorDiff hunks with old and new line numbers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl:75:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should dim deleted ColorDiff lines when requested' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should render ColorFile lines and drop trailing empty line' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
