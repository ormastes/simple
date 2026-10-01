# Claude Full Screen Pools

> Purpose: should intern space, spacer, ASCII, and non-ASCII characters

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Claude Full Screen Pools

Purpose: should intern space, spacer, ASCII, and non-ASCII characters

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/tools/llm/claude_full/ink/screen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: should intern space, spacer, ASCII, and non-ASCII characters
Audience: compiler and tooling engineers who maintain this spec

# Claude Full Screen Pools

Checks screen interning pools and encoded style IDs.

## Scenarios

### Claude full screen pools

#### should intern space, spacer, ASCII, and non-ASCII characters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should intern space, spacer, ASCII, and non-ASCII characters
- Verify: should intern space, spacer, ASCII, and non-ASCII characters
- Intern characters through shared CharPool
   - Expected: pool.get(emptyCharIndex()) equals ` `
   - Expected: pool.get(spacerCharIndex()) equals ``
   - Expected: pool.intern("a") equals `a`
   - Expected: pool.asciiLookup(97) equals `a`
   - Expected: pool.intern("🙂") equals `emoji`
   - Expected: pool.get(999) equals ` `


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should intern space, spacer, ASCII, and non-ASCII characters")
step("Verify: should intern space, spacer, ASCII, and non-ASCII characters")
# @req: REQ-TOOLS-Scre-001
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

- should intern hyperlinks with zero as no-link
- Verify: should intern hyperlinks with zero as no-link
- Intern hyperlink strings
   - Expected: pool.intern("") equals `0`
   - Expected: pool.intern("https://example.test") equals `link`
   - Expected: pool.get(0) equals ``
   - Expected: pool.get(link) equals `https://example.test`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should intern hyperlinks with zero as no-link")
step("Verify: should intern hyperlinks with zero as no-link")
# @req: REQ-TOOLS-Scre-001
step("Intern hyperlink strings")
val pool = hyperlinkPoolNew()
expect(pool.intern("")).to_equal(0)  # oracle: value fixed by the spec contract
val link = pool.intern("https://example.test")
expect(pool.intern("https://example.test")).to_equal(link)
expect(pool.get(0)).to_equal("")
expect(pool.get(link)).to_equal("https://example.test")
```

</details>

#### should encode visible-on-space styles in bit zero

- should encode visible-on-space styles in bit zero
- Verify: should encode visible-on-space styles in bit zero
- Intern foreground and inverse styles
   - Expected: pool.none equals `0`
   - Expected: fg & 1 equals `0`
   - Expected: inverse & 1 equals `1`
   - Expected: pool.get(inverse)[0].endCode equals `\u001B[27m`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should encode visible-on-space styles in bit zero")
step("Verify: should encode visible-on-space styles in bit zero")
# @req: REQ-TOOLS-Scre-001
step("Intern foreground and inverse styles")
val pool = stylePoolNew()
val fg = pool.intern([fgCode("\u001B[31m")])
val inverse = pool.intern([inverseCode()])
expect(pool.none).to_equal(0)  # oracle: value fixed by the spec contract
expect(fg & 1).to_equal(0)  # oracle: value fixed by the spec contract
expect(inverse & 1).to_equal(1)  # oracle: value fixed by the spec contract
expect(pool.get(inverse)[0].endCode).to_equal("\u001B[27m")
```

</details>

#### should cache transitions and inverse overlays

- should cache transitions and inverse overlays
- Verify: should cache transitions and inverse overlays
- Compute transition and inverse style twice
   - Expected: pool.withInverse(fg) equals `inverse`
   - Expected: pool.transition(fg, inverse) equals `transition`
   - Expected: pool.transitionKeys.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should cache transitions and inverse overlays")
step("Verify: should cache transitions and inverse overlays")
# @req: REQ-TOOLS-Scre-001
step("Compute transition and inverse style twice")
val pool = stylePoolNew()
val fg = pool.intern([fgCode("\u001B[31m")])
val inverse = pool.withInverse(fg)
expect(pool.withInverse(fg)).to_equal(inverse)
val transition = pool.transition(fg, inverse)
expect(pool.transition(fg, inverse)).to_equal(transition)
expect(pool.transitionKeys.len()).to_equal(1)  # oracle: value fixed by the spec contract
```

</details>

#### should build current match style without stacking duplicate markers

- should build current match style without stacking duplicate markers
- Verify: should build current match style without stacking duplicate markers
- Apply current-match overlay
   - Expected: pool.withCurrentMatch(base) equals `match`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should build current match style without stacking duplicate markers")
step("Verify: should build current match style without stacking duplicate markers")
# @req: REQ-TOOLS-Scre-001
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

- should use inverse fallback and configured selection background
- Verify: should use inverse fallback and configured selection background
- Apply selection background overlay
   - Expected: fallback equals `pool.withInverse(base)`
   - Expected: pool.withSelectionBg(base) equals `selected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should use inverse fallback and configured selection background")
step("Verify: should use inverse fallback and configured selection background")
# @req: REQ-TOOLS-Scre-001
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

- should expose packed cell constants
- Verify: should expose packed cell constants
- Pin packed word and width constants
   - Expected: cellWidthNarrow() equals `0`
   - Expected: cellWidthWide() equals `1`
   - Expected: cellWidthSpacerTail() equals `2`
   - Expected: cellWidthSpacerHead() equals `3`
   - Expected: packWord1(3, 4, 2) equals `(3 << 17) | (4 << 2) | 2`
   - Expected: screenPoolSourceLinesModeled() equals `260`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should expose packed cell constants")
step("Verify: should expose packed cell constants")
# @req: REQ-TOOLS-Scre-001
step("Pin packed word and width constants")
expect(cellWidthNarrow()).to_equal(0)  # oracle: value fixed by the spec contract
expect(cellWidthWide()).to_equal(1)  # oracle: value fixed by the spec contract
expect(cellWidthSpacerTail()).to_equal(2)  # oracle: value fixed by the spec contract
expect(cellWidthSpacerHead()).to_equal(3)  # oracle: value fixed by the spec contract
expect(packWord1(3, 4, 2)).to_equal((3 << 17) | (4 << 2) | 2)
expect(screenPoolSourceLinesModeled()).to_equal(260)  # oracle: value fixed by the spec contract
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
- `REQ-TOOLS-Scre-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2642fcf6915dafe80a837aa2c50823b1e623495b9c1321e8519c972fae8c09f5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2642fcf6915dafe80a837aa2c50823b1e623495b9c1321e8519c972fae8c09f5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2642fcf6915dafe80a837aa2c50823b1e623495b9c1321e8519c972fae8c09f5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/tools/llm/claude_full/ink/screen_spec.spl
mirror: doc/06_spec/03_system/tools/llm/claude_full/ink/screen_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/tools/llm/claude_full/ink/screen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/tools/llm/claude_full/ink/screen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/tools/llm/claude_full/ink/screen_spec.spl:24:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should intern space, spacer, ASCII, and non-ASCII characters' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/screen_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should intern space, spacer, ASCII, and non-ASCII characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/screen_spec.spl:40:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should intern hyperlinks with zero as no-link' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/screen_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should intern hyperlinks with zero as no-link' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/screen_spec.spl:53:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should encode visible-on-space styles in bit zero' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/screen_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should encode visible-on-space styles in bit zero' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/tools/llm/claude_full/ink/screen_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should cache transitions and inverse overlays' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/screen_spec.spl:81:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should build current match style without stacking duplicate markers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/tools/llm/claude_full/ink/screen_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should use inverse fallback and configured selection background' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
