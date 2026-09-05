# Style Block Processor — Coverage Closure (U4.3, part 2: style_block.spl)

> Purpose: Prove that css_decl_property / css_decl_value / css_decls_contain (U4.3 closure).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Style Block Processor — Coverage Closure (U4.3, part 2: style_block.spl)

Purpose: Prove that css_decl_property / css_decl_value / css_decls_contain (U4.3 closure).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/style_block_coverage_closure_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that css_decl_property / css_decl_value / css_decls_contain (U4.3 closure).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### css_decl_property / css_decl_value / css_decls_contain (U4.3 closure)

#### reads the property and value fields through the accessor functions

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the property and value fields through the accessor functions
- Verify: reads the property and value fields through the accessor functions
   - Expected: css_decl_property(decl) equals `color`
   - Expected: css_decl_value(decl) equals `red`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("reads the property and value fields through the accessor functions")
step("Verify: reads the property and value fields through the accessor functions")
# @req: REQ-BROWSER-ENGINE-001
val decl = CssDecl(property: "color", value: "red")
expect(css_decl_property(decl)).to_equal("color")
expect(css_decl_value(decl)).to_equal("red")
```

</details>

#### finds a matching property/value pair and reports absence for a non-matching one (both-directions oracle)

- finds a matching property/value pair and reports absence for a non-matching one (both-directions oracle)
- Verify: finds a matching property/value pair and reports absence for a non-matching one (both-directions oracle)
   - Expected: css_decls_contain(decls, "display", "block") is true
   - Expected: css_decls_contain(decls, "display", "flex") is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("finds a matching property/value pair and reports absence for a non-matching one (both-directions oracle)")
step("Verify: finds a matching property/value pair and reports absence for a non-matching one (both-directions oracle)")
val decls = [CssDecl(property: "color", value: "red"), CssDecl(property: "display", value: "block")]
expect(css_decls_contain(decls, "display", "block")).to_equal(true)
expect(css_decls_contain(decls, "display", "flex")).to_equal(false)
```

</details>

### sb_find (U4.3 closure)

#### returns the index of the first occurrence at or after start

- returns the index of the first occurrence at or after start
- Verify: returns the index of the first occurrence at or after start
   - Expected: sb_find("a.b.c", ".", 0) equals `1`
   - Expected: sb_find("a.b.c", ".", 2) equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the index of the first occurrence at or after start")
step("Verify: returns the index of the first occurrence at or after start")
expect(sb_find("a.b.c", ".", 0)).to_equal(1)
expect(sb_find("a.b.c", ".", 2)).to_equal(3)
```

</details>

#### returns the sentinel 999999999 when the target is absent (both-directions oracle)

- returns the sentinel 999999999 when the target is absent (both-directions oracle)
- Verify: returns the sentinel 999999999 when the target is absent (both-directions oracle)
   - Expected: sb_find("abc", "z", 0) equals `999999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the sentinel 999999999 when the target is absent (both-directions oracle)")
step("Verify: returns the sentinel 999999999 when the target is absent (both-directions oracle)")
expect(sb_find("abc", "z", 0)).to_equal(999999999)
```

</details>

### sb_split_char (U4.3 closure)

#### splits on every occurrence of the delimiter, keeping empty segments

- splits on every occurrence of the delimiter, keeping empty segments
- Verify: splits on every occurrence of the delimiter, keeping empty segments
   - Expected: parts.len() equals `4`
   - Expected: parts[0] equals `div`
   - Expected: parts[1] equals `span`
   - Expected: parts[2] equals ``
   - Expected: parts[3] equals `p`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits on every occurrence of the delimiter, keeping empty segments")
step("Verify: splits on every occurrence of the delimiter, keeping empty segments")
val parts = sb_split_char("div,span,,p", ",")
expect(parts.len()).to_equal(4)  # oracle: 4 — named expected value from the requirement
expect(parts[0]).to_equal("div")
expect(parts[1]).to_equal("span")
expect(parts[2]).to_equal("")
expect(parts[3]).to_equal("p")
```

</details>

### sb_split_selector_list (U4.3 closure)

#### splits top-level commas but not commas nested inside parens

- splits top-level commas but not commas nested inside parens
- Verify: splits top-level commas but not commas nested inside parens
   - Expected: parts.len() equals `3`
   - Expected: parts[0] equals `div`
   - Expected: parts[1] equals ` :is(a, b)`
   - Expected: parts[2] equals ` span`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits top-level commas but not commas nested inside parens")
step("Verify: splits top-level commas but not commas nested inside parens")
val parts = sb_split_selector_list("div, :is(a, b), span")
expect(parts.len()).to_equal(3)  # oracle: 3 — named expected value from the requirement
expect(parts[0]).to_equal("div")
expect(parts[1]).to_equal(" :is(a, b)")
expect(parts[2]).to_equal(" span")
```

</details>

### sb_find_top_level_child_combinator (U4.3 closure)

#### finds a top-level '>' and ignores one nested inside parens

- finds a top-level '>' and ignores one nested inside parens
- Verify: finds a top-level '>' and ignores one nested inside parens
   - Expected: sb_find_top_level_child_combinator("div > span") equals `4`
   - Expected: sb_find_top_level_child_combinator(":is(a > b) span") equals `999999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("finds a top-level '>' and ignores one nested inside parens")
step("Verify: finds a top-level '>' and ignores one nested inside parens")
expect(sb_find_top_level_child_combinator("div > span")).to_equal(4)
expect(sb_find_top_level_child_combinator(":is(a > b) span")).to_equal(999999999)
```

</details>

### sb_split_ws (U4.3 closure)

#### splits on runs of whitespace and drops empty segments

- splits on runs of whitespace and drops empty segments
- Verify: splits on runs of whitespace and drops empty segments
   - Expected: parts.len() equals `2`
   - Expected: parts[0] equals `div`
   - Expected: parts[1] equals `span`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("splits on runs of whitespace and drops empty segments")
step("Verify: splits on runs of whitespace and drops empty segments")
val parts = sb_split_ws("  div   span  ")
expect(parts.len()).to_equal(2)  # oracle: 2 — named expected value from the requirement
expect(parts[0]).to_equal("div")
expect(parts[1]).to_equal("span")
```

</details>

### sb_skip_ws_comments (U4.3 closure)

#### skips whitespace and a CSS comment, stopping at the next real token

- skips whitespace and a CSS comment, stopping at the next real token
- Verify: skips whitespace and a CSS comment, stopping at the next real token
   - Expected: sb_skip_ws_comments("  /* c */ div", 0) equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("skips whitespace and a CSS comment, stopping at the next real token")
step("Verify: skips whitespace and a CSS comment, stopping at the next real token")
expect(sb_skip_ws_comments("  /* c */ div", 0)).to_equal(10)
```

</details>

#### returns start unchanged when there is nothing to skip (both-directions oracle)

- returns start unchanged when there is nothing to skip (both-directions oracle)
- Verify: returns start unchanged when there is nothing to skip (both-directions oracle)
   - Expected: sb_skip_ws_comments("div", 0) equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns start unchanged when there is nothing to skip (both-directions oracle)")
step("Verify: returns start unchanged when there is nothing to skip (both-directions oracle)")
expect(sb_skip_ws_comments("div", 0)).to_equal(0)
```

</details>

### sb_parse_int (U4.3 closure)

#### parses a positive and a negative integer

- parses a positive and a negative integer
- Verify: parses a positive and a negative integer
   - Expected: sb_parse_int("42") equals `42`
   - Expected: sb_parse_int("-7") equals `-7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("parses a positive and a negative integer")
step("Verify: parses a positive and a negative integer")
expect(sb_parse_int("42")).to_equal(42)
expect(sb_parse_int("-7")).to_equal(-7)
```

</details>

#### returns 0 for empty or non-numeric text (both-directions oracle)

- returns 0 for empty or non-numeric text (both-directions oracle)
- Verify: returns 0 for empty or non-numeric text (both-directions oracle)
   - Expected: sb_parse_int("") equals `0`
   - Expected: sb_parse_int("abc") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns 0 for empty or non-numeric text (both-directions oracle)")
step("Verify: returns 0 for empty or non-numeric text (both-directions oracle)")
expect(sb_parse_int("")).to_equal(0)
expect(sb_parse_int("abc")).to_equal(0)
```

</details>

### find_matching_brace (U4.3 closure)

#### finds the matching close brace across nested braces

- finds the matching close brace across nested braces
- Verify: finds the matching close brace across nested braces
   - Expected: find_matching_brace("div { .a { color: red; } }", 4) equals `25`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("finds the matching close brace across nested braces")
step("Verify: finds the matching close brace across nested braces")
expect(find_matching_brace("div { .a { color: red; } }", 4)).to_equal(25)
```

</details>

#### returns the sentinel 999999999 when the brace never closes (both-directions oracle)

- returns the sentinel 999999999 when the brace never closes (both-directions oracle)
- Verify: returns the sentinel 999999999 when the brace never closes (both-directions oracle)
   - Expected: find_matching_brace("div { color: red;", 4) equals `999999999`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-BROWSER_ENGINE
step("returns the sentinel 999999999 when the brace never closes (both-directions oracle)")
step("Verify: returns the sentinel 999999999 when the brace never closes (both-directions oracle)")
expect(find_matching_brace("div { color: red;", 4)).to_equal(999999999)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-BROWSER_ENGINE`
- `REQ-BROWSER-ENGINE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bd49865ce62d8165ac60e47fbc901dd504bf466a56a525911ba49ddc21019bea`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bd49865ce62d8165ac60e47fbc901dd504bf466a56a525911ba49ddc21019bea`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bd49865ce62d8165ac60e47fbc901dd504bf466a56a525911ba49ddc21019bea`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/browser_engine/style_block_coverage_closure_spec.spl
mirror: doc/06_spec/01_unit/browser_engine/style_block_coverage_closure_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/browser_engine/style_block_coverage_closure_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/browser_engine/style_block_coverage_closure_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/browser_engine/style_block_coverage_closure_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 13 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/browser_engine/style_block_coverage_closure_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the property and value fields through the accessor functions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/style_block_coverage_closure_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds a matching property/value pair and reports absence for a non-matching one (both-directions oracle)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/browser_engine/style_block_coverage_closure_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns the index of the first occurrence at or after start' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
