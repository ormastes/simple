# Claude Full Screen Pools

> Checks screen interning pools and encoded style IDs.

<!-- sdn-diagram:id=screen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=screen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

screen_spec -> std
screen_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=screen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Screen Pools

Checks screen interning pools and encoded style IDs.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/screen_spec.spl` |
| Updated | 2026-07-05 |
| Generator | `simple spipe-docgen` (Simple) |

Checks screen interning pools and encoded style IDs.

## Scenarios

### Claude full screen pools

#### should intern space, spacer, ASCII, and non-ASCII characters

- Intern characters through shared CharPool
   - Expected: pool.get(emptyCharIndex()) equals ` `
   - Expected: pool.get(spacerCharIndex()) equals ``
   - Expected: pool.intern("a") equals `a`
   - Expected: pool.asciiLookup(97) equals `a`
   - Expected: pool.intern("🙂") equals `emoji`
   - Expected: pool.get(999) equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Intern characters through shared CharPool")
val pool = charPoolNew()
expect(pool.get(emptyCharIndex())).to_equal(" ")
expect(pool.get(spacerCharIndex())).to_equal("")
val a = pool.intern("a")
expect(pool.intern("a")).to_equal(a)
expect(pool.asciiLookup(97)).to_equal(a)
val emoji = pool.intern("🙂")
expect(pool.intern("🙂")).to_equal(emoji)
expect(pool.get(999)).to_equal(" ")
```

</details>

#### should intern hyperlinks with zero as no-link

- Intern hyperlink strings
   - Expected: pool.intern("") equals `0`
   - Expected: pool.intern("https://example.test") equals `link`
   - Expected: pool.get(0) equals ``
   - Expected: pool.get(link) equals `https://example.test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Intern hyperlink strings")
val pool = hyperlinkPoolNew()
expect(pool.intern("")).to_equal(0)
val link = pool.intern("https://example.test")
expect(pool.intern("https://example.test")).to_equal(link)
expect(pool.get(0)).to_equal("")
expect(pool.get(link)).to_equal("https://example.test")
```

</details>

#### should encode visible-on-space styles in bit zero

- Intern foreground and inverse styles
   - Expected: pool.none equals `0`
   - Expected: fg & 1 equals `0`
   - Expected: inverse & 1 equals `1`
   - Expected: pool.get(inverse)[0].endCode equals `\u001B[27m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Intern foreground and inverse styles")
val pool = stylePoolNew()
val fg = pool.intern([fgCode("\u001B[31m")])
val inverse = pool.intern([inverseCode()])
expect(pool.none).to_equal(0)
expect(fg & 1).to_equal(0)
expect(inverse & 1).to_equal(1)
expect(pool.get(inverse)[0].endCode).to_equal("\u001B[27m")
```

</details>

#### should cache transitions and inverse overlays

- Compute transition and inverse style twice
   - Expected: pool.withInverse(fg) equals `inverse`
   - Expected: pool.transition(fg, inverse) equals `transition`
   - Expected: pool.transitionKeys.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Compute transition and inverse style twice")
val pool = stylePoolNew()
val fg = pool.intern([fgCode("\u001B[31m")])
val inverse = pool.withInverse(fg)
expect(pool.withInverse(fg)).to_equal(inverse)
val transition = pool.transition(fg, inverse)
expect(pool.transition(fg, inverse)).to_equal(transition)
expect(pool.transitionKeys.len()).to_equal(1)
```

</details>

#### should build current match style without stacking duplicate markers

- Apply current-match overlay
   - Expected: pool.withCurrentMatch(base) equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply current-match overlay")
val pool = stylePoolNew()
val base = pool.intern([fgCode("\u001B[32m"), bgCode("\u001B[44m")])
val match = pool.withCurrentMatch(base)
expect(pool.withCurrentMatch(base)).to_equal(match)
val codes = styleKey(pool.get(match))
expect(codes).to_contain("\u001B[33m")
expect(codes).to_contain("\u001B[7m")
expect(codes).to_contain("\u001B[1m")
expect(codes).to_contain("\u001B[4m")
```

</details>

#### should use inverse fallback and configured selection background

- Apply selection background overlay
   - Expected: fallback equals `pool.withInverse(base)`
- pool setSelectionBg
   - Expected: pool.withSelectionBg(base) equals `selected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Apply selection background overlay")
val pool = stylePoolNew()
val base = pool.intern([fgCode("\u001B[32m"), bgCode("\u001B[44m"), inverseCode()])
val fallback = pool.withSelectionBg(base)
expect(fallback).to_equal(pool.withInverse(base))
pool.setSelectionBg(Some(bgCode("\u001B[48;5;10m")))
val selected = pool.withSelectionBg(base)
expect(pool.withSelectionBg(base)).to_equal(selected)
val codes = styleKey(pool.get(selected))
expect(codes).to_contain("\u001B[48;5;10m")
expect(codes).to_contain("\u001B[32m")
```

</details>

#### should expose packed cell constants

- Pin packed word and width constants
   - Expected: cellWidthNarrow() equals `0`
   - Expected: cellWidthWide() equals `1`
   - Expected: cellWidthSpacerTail() equals `2`
   - Expected: cellWidthSpacerHead() equals `3`
   - Expected: packWord1(3, 4, 2) equals `(3 << 17) | (4 << 2) | 2`
   - Expected: screenPoolSourceLinesModeled() equals `260`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Pin packed word and width constants")
expect(cellWidthNarrow()).to_equal(0)
expect(cellWidthWide()).to_equal(1)
expect(cellWidthSpacerTail()).to_equal(2)
expect(cellWidthSpacerHead()).to_equal(3)
expect(packWord1(3, 4, 2)).to_equal((3 << 17) | (4 << 2) | 2)
expect(screenPoolSourceLinesModeled()).to_equal(260)
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
