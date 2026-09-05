# Claude Full Native Color Diff

> Checks color-diff public API parity: color mode, ANSI escape conversion,

<!-- sdn-diagram:id=index_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=index_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

index_spec -> std
index_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=index_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Native Color Diff

Checks color-diff public API parity: color mode, ANSI escape conversion,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/native-ts/color-diff/index_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks color-diff public API parity: color mode, ANSI escape conversion,
hunk rendering, file rendering, syntax theme, and native-module surface.

## Scenarios

### Claude full native color diff

#### should detect color modes and syntax themes

- Select color mode and syntax theme
   - Expected: detectColorMode("ansi-dark", "truecolor") equals `ansi`
   - Expected: detectColorMode("dark", "24bit") equals `truecolor`
   - Expected: detectColorMode("light", "") equals `color256`
   - Expected: defaultSyntaxThemeName("dark") equals `Monokai Extended`
   - Expected: getSyntaxTheme("light").theme equals `GitHub`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Select color mode and syntax theme")
expect(detectColorMode("ansi-dark", "truecolor")).to_equal("ansi")
expect(detectColorMode("dark", "24bit")).to_equal("truecolor")
expect(detectColorMode("light", "")).to_equal("color256")
expect(defaultSyntaxThemeName("dark")).to_equal("Monokai Extended")
expect(getSyntaxTheme("light").theme).to_equal("GitHub")
```

</details>

#### should convert colors to terminal escapes

- Convert palette, default, truecolor, and 256-color escapes
   - Expected: colorToEscape(ansiIdx(3), true, "ansi") equals `\u001B[33m`
   - Expected: colorToEscape(Color.defaultBg(), false, "ansi") equals `\u001B[49m`
   - Expected: colorToEscape(rgb(1, 2, 3), true, "truecolor") equals `\u001B[38;2;1;2;3m`
   - Expected: colorToEscape(rgb(255, 255, 255), true, "color256") equals `\u001B[38;5;231m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Convert palette, default, truecolor, and 256-color escapes")
expect(colorToEscape(ansiIdx(3), true, "ansi")).to_equal("\u001B[33m")
expect(colorToEscape(Color.defaultBg(), false, "ansi")).to_equal("\u001B[49m")
expect(colorToEscape(rgb(1, 2, 3), true, "truecolor")).to_equal("\u001B[38;2;1;2;3m")
expect(colorToEscape(rgb(255, 255, 255), true, "color256")).to_equal("\u001B[38;5;231m")
```

</details>

#### should tokenize and pair adjacent diff lines

- Find word diff inputs
   - Expected: tokenize("a b").len() equals `3`
   - Expected: pairs[0].start equals `0`
   - Expected: pairs[0].end equals `1`
   - Expected: wordDiffStrings("old", "new").len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Find word diff inputs")
expect(tokenize("a b").len()).to_equal(3)
val pairs = findAdjacentPairs(["-", "+", " "])
expect(pairs[0].start).to_equal(0)
expect(pairs[0].end).to_equal(1)
expect(wordDiffStrings("old", "new").len()).to_equal(2)
```

</details>

#### should render ColorDiff hunks with old and new line numbers

- Render a changed hunk


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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

- Render dim deleted hunk


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render dim deleted hunk")
val hunk = Hunk.new(1, 1, 1, 0, ["-gone"])
val lines = ColorDiff.new(hunk, "", "x.ts", "").render("ansi", 80, true)
expect(lines[0]).to_contain("\u001B[2m")
```

</details>

#### should render ColorFile lines and drop trailing empty line

- Render a whole file
   - Expected: lines.len() equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Render a whole file")
val file = ColorFile.new("one\ntwo\n", "README.md")
val lines = file.render("light", 80, false)
expect(lines.len()).to_equal(2)
expect(lines[0]).to_contain("1 one")
expect(lines[0]).to_contain("markdown")
expect(lines[1]).to_contain("2 two")
```

</details>

#### should expose native module and source constants

- Pin public surface
   - Expected: native.hasColorDiff is true
   - Expected: native.hasColorFile is true
   - Expected: native.hasSyntaxTheme is true
   - Expected: hljs() equals `lazy-highlight-js`
   - Expected: colorDiffSourceLinesModeled() equals `999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin public surface")
val native = getNativeModule()
expect(native.hasColorDiff).to_equal(true)
expect(native.hasColorFile).to_equal(true)
expect(native.hasSyntaxTheme).to_equal(true)
expect(hljs()).to_equal("lazy-highlight-js")
expect(colorDiffSourceLinesModeled()).to_equal(999)
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
