# DOM Gradient / Background Shorthand Parsing — Coverage Closure

> Purpose: Prove that sb_dom_split_ws / find_char_in / find_last_space (closure).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# DOM Gradient / Background Shorthand Parsing — Coverage Closure

Purpose: Prove that sb_dom_split_ws / find_char_in / find_last_space (closure).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/dom_color_named_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that sb_dom_split_ws / find_char_in / find_last_space (closure).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### sb_dom_split_ws / find_char_in / find_last_space (closure)

#### splits on mixed whitespace and handles empty input

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- splits on mixed whitespace and handles empty input
- Verify: splits on mixed whitespace and handles empty input
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `a`
   - Expected: parts[2] equals `c`
   - Expected: sb_dom_split_ws("").len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits on mixed whitespace and handles empty input")
step("Verify: splits on mixed whitespace and handles empty input")
# @req: REQ-BROWSER-ENGINE-DOM-COLOR-NAMED-COVERAGE-CLOSURE-SPEC-SPL-001
val parts = sb_dom_split_ws(" a\tb\nc ")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(parts[0]).to_equal("a")
expect(parts[2]).to_equal("c")
expect(sb_dom_split_ws("").len()).to_equal(0)
```

</details>

#### finds a character or reports the sentinel

- finds a character or reports the sentinel
- Verify: finds a character or reports the sentinel
   - Expected: find_char_in("abc", "b", 0) equals `1`
   - Expected: find_char_in("abc", "b", 2) equals `999999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("finds a character or reports the sentinel")
step("Verify: finds a character or reports the sentinel")
expect(find_char_in("abc", "b", 0)).to_equal(1)
expect(find_char_in("abc", "b", 2)).to_equal(999999999)
```

</details>

#### returns the last top-level space, ignoring spaces inside parens

- returns the last top-level space, ignoring spaces inside parens
- Verify: returns the last top-level space, ignoring spaces inside parens
   - Expected: find_last_space("rgba(0, 0, 0, 1) 50%") equals `16`
   - Expected: find_last_space("abc") equals `999999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the last top-level space, ignoring spaces inside parens")
step("Verify: returns the last top-level space, ignoring spaces inside parens")
expect(find_last_space("rgba(0, 0, 0, 1) 50%")).to_equal(16)
expect(find_last_space("abc")).to_equal(999999999)
```

</details>

### split_top_level_commas (closure)

#### splits only commas outside parentheses and trims parts

- splits only commas outside parentheses and trims parts
- Verify: splits only commas outside parentheses and trims parts
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `90deg`
   - Expected: parts[1] equals `rgba(1,2,3,0.5)`
   - Expected: parts[2] equals `#fff`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits only commas outside parentheses and trims parts")
step("Verify: splits only commas outside parentheses and trims parts")
val parts = split_top_level_commas("90deg, rgba(1,2,3,0.5), #fff")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(parts[0]).to_equal("90deg")
expect(parts[1]).to_equal("rgba(1,2,3,0.5)")
expect(parts[2]).to_equal("#fff")
```

</details>

#### drops an empty tail

- drops an empty tail
- Verify: drops an empty tail
   - Expected: split_top_level_commas("a,").len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("drops an empty tail")
step("Verify: drops an empty tail")
expect(split_top_level_commas("a,").len()).to_equal(1)
```

</details>

### strip_stop_position (closure)

#### strips trailing % and px stop positions

- strips trailing % and px stop positions
- Verify: strips trailing % and px stop positions
   - Expected: strip_stop_position("red 50%") equals `red`
   - Expected: strip_stop_position("rgba(0,0,0,0.2) 10px") equals `rgba(0,0,0,0.2)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("strips trailing % and px stop positions")
step("Verify: strips trailing % and px stop positions")
expect(strip_stop_position("red 50%")).to_equal("red")
expect(strip_stop_position("rgba(0,0,0,0.2) 10px")).to_equal("rgba(0,0,0,0.2)")
```

</details>

#### leaves colors without stop positions alone

- leaves colors without stop positions alone
- Verify: leaves colors without stop positions alone
   - Expected: strip_stop_position("red") equals `red`
   - Expected: strip_stop_position("to bottom") equals `to bottom`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("leaves colors without stop positions alone")
step("Verify: leaves colors without stop positions alone")
expect(strip_stop_position("red")).to_equal("red")
expect(strip_stop_position("to bottom")).to_equal("to bottom")
```

</details>

### parse_linear_gradient (closure)

#### parses an explicit angle with two hex colors

- parses an explicit angle with two hex colors
- Verify: parses an explicit angle with two hex colors
   - Expected: g.gradient_set is true
   - Expected: g.gradient_angle equals `90`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses an explicit angle with two hex colors")
step("Verify: parses an explicit angle with two hex colors")
val g = parse_linear_gradient("linear-gradient(90deg, #007AFF, #30D158)")
expect(g.gradient_set).to_equal(true)
expect(g.gradient_angle).to_equal(90)  # oracle: 90 — named expected value from the requirement
```

</details>

#### maps direction keywords to angles

- maps direction keywords to angles
- Verify: maps direction keywords to angles
   - Expected: parse_linear_gradient("linear-gradient(to top, #000, #fff)").gradient_angle equals `0`
   - Expected: parse_linear_gradient("linear-gradient(to right, #000, #fff)").gradient_angle equals `90`
   - Expected: parse_linear_gradient("linear-gradient(to left, #000, #fff)").gradient_angle equals `270`
   - Expected: parse_linear_gradient("linear-gradient(to bottom, #000, #fff)").gradient_angle equals `180`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("maps direction keywords to angles")
step("Verify: maps direction keywords to angles")
expect(parse_linear_gradient("linear-gradient(to top, #000, #fff)").gradient_angle).to_equal(0)
expect(parse_linear_gradient("linear-gradient(to right, #000, #fff)").gradient_angle).to_equal(90)
expect(parse_linear_gradient("linear-gradient(to left, #000, #fff)").gradient_angle).to_equal(270)
expect(parse_linear_gradient("linear-gradient(to bottom, #000, #fff)").gradient_angle).to_equal(180)
```

</details>

#### defaults to 180deg when the first part is already a color

- defaults to 180deg when the first part is already a color
- Verify: defaults to 180deg when the first part is already a color
   - Expected: g.gradient_set is true
   - Expected: g.gradient_angle equals `180`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("defaults to 180deg when the first part is already a color")
step("Verify: defaults to 180deg when the first part is already a color")
val g = parse_linear_gradient("linear-gradient(#000, #fff)")
expect(g.gradient_set).to_equal(true)
expect(g.gradient_angle).to_equal(180)  # oracle: 180 — named expected value from the requirement
```

</details>

#### rejects malformed input (no paren, unbalanced, too few parts)

- rejects malformed input (no paren, unbalanced, too few parts)
- Verify: rejects malformed input (no paren, unbalanced, too few parts)
   - Expected: parse_linear_gradient("none").gradient_set is false
   - Expected: parse_linear_gradient("linear-gradient(90deg, #000").gradient_set is false
   - Expected: parse_linear_gradient("linear-gradient(90deg)").gradient_set is false
   - Expected: parse_linear_gradient("linear-gradient(90deg, #000)").gradient_set is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("rejects malformed input (no paren, unbalanced, too few parts)")
step("Verify: rejects malformed input (no paren, unbalanced, too few parts)")
expect(parse_linear_gradient("none").gradient_set).to_equal(false)
expect(parse_linear_gradient("linear-gradient(90deg, #000").gradient_set).to_equal(false)
expect(parse_linear_gradient("linear-gradient(90deg)").gradient_set).to_equal(false)
expect(parse_linear_gradient("linear-gradient(90deg, #000)").gradient_set).to_equal(false)
```

</details>

#### parses rgba stops with stop positions

- parses rgba stops with stop positions
- Verify: parses rgba stops with stop positions
   - Expected: g.gradient_set is true
   - Expected: g.gradient_angle equals `180`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses rgba stops with stop positions")
step("Verify: parses rgba stops with stop positions")
val g = parse_linear_gradient("linear-gradient(180deg, rgba(255,255,255,0.09) 0%, rgba(255,255,255,0.02) 100%)")
expect(g.gradient_set).to_equal(true)
expect(g.gradient_angle).to_equal(180)  # oracle: 180 — named expected value from the requirement
```

</details>

### dom_background_shorthand_color_value (closure)

#### returns hex / functional / keyword color tokens

- returns hex / functional / keyword color tokens
- Verify: returns hex / functional / keyword color tokens
   - Expected: dom_background_shorthand_color_value("#ff0000 url(x.png)") equals `#ff0000`
   - Expected: dom_background_shorthand_color_value("url(x.png) rgba(1,2,3,0.5)") equals `rgba(1,2,3,0.5)`
   - Expected: dom_background_shorthand_color_value("transparent") equals `transparent`
   - Expected: dom_background_shorthand_color_value("red") equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns hex / functional / keyword color tokens")
step("Verify: returns hex / functional / keyword color tokens")
expect(dom_background_shorthand_color_value("#ff0000 url(x.png)")).to_equal("#ff0000")
expect(dom_background_shorthand_color_value("url(x.png) rgba(1,2,3,0.5)")).to_equal("rgba(1,2,3,0.5)")
expect(dom_background_shorthand_color_value("transparent")).to_equal("transparent")
expect(dom_background_shorthand_color_value("red")).to_equal("red")
```

</details>

#### returns empty for gradients, empty input, and non-color values

- returns empty for gradients, empty input, and non-color values
- Verify: returns empty for gradients, empty input, and non-color values
   - Expected: dom_background_shorthand_color_value("linear-gradient(90deg, #000, #fff)") equals ``
   - Expected: dom_background_shorthand_color_value("") equals ``
   - Expected: dom_background_shorthand_color_value("url(x.png)") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns empty for gradients, empty input, and non-color values")
step("Verify: returns empty for gradients, empty input, and non-color values")
expect(dom_background_shorthand_color_value("linear-gradient(90deg, #000, #fff)")).to_equal("")
expect(dom_background_shorthand_color_value("")).to_equal("")
expect(dom_background_shorthand_color_value("url(x.png)")).to_equal("")
```

</details>

### dom_background_token_from (closure)

#### extracts a token, keeping paren groups intact

- extracts a token, keeping paren groups intact
- Verify: extracts a token, keeping paren groups intact
   - Expected: dom_background_token_from("rgba(1, 2, 3, 1) red", 0) equals `rgba(1, 2, 3, 1)`
   - Expected: dom_background_token_from("red blue", 4) equals `blue`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("extracts a token, keeping paren groups intact")
step("Verify: extracts a token, keeping paren groups intact")
expect(dom_background_token_from("rgba(1, 2, 3, 1) red", 0)).to_equal("rgba(1, 2, 3, 1)")
expect(dom_background_token_from("red blue", 4)).to_equal("blue")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-BROWSER-ENGINE-DOM-COLOR-NAMED-COVERAGE-CLOSURE-SPEC-SPL-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3dce4a532b8f3928b3b93384f6a5a5576437c99c61e3bd12639a02aea3b6e2d5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3dce4a532b8f3928b3b93384f6a5a5576437c99c61e3bd12639a02aea3b6e2d5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3dce4a532b8f3928b3b93384f6a5a5576437c99c61e3bd12639a02aea3b6e2d5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/dom_color_named_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/dom_color_named_coverage_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/dom_color_named_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/dom_color_named_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/dom_color_named_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 10 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/dom_color_named_coverage_closure_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'splits on mixed whitespace and handles empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/dom_color_named_coverage_closure_spec.spl:55:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a character or reports the sentinel' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/dom_color_named_coverage_closure_spec.spl:62:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the last top-level space, ignoring spaces inside parens' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
