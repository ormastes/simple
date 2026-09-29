# pptx_tables_spec

> Purpose: Prove that PPTX tables: export emits a:tbl in a graphicFrame.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# pptx_tables_spec

Purpose: Prove that PPTX tables: export emits a:tbl in a graphicFrame.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/pptx_tables_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that PPTX tables: export emits a:tbl in a graphicFrame.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### PPTX tables: export emits a:tbl in a graphicFrame

#### emits a p:graphicFrame with a:tbl, 3 a:gridCol and 3 a:tr for a 3x(1+2) table

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- emits a p:graphicFrame with a:tbl, 3 a:gridCol and 3 a:tr for a 3x(1+2) table
- Verify: emits a p:graphicFrame with a:tbl, 3 a:gridCol and 3 a:tr for a 3x(1+2) table
   - Expected: _count_occurrences(slide1, "<a:gridCol ") equals `3`
   - Expected: _count_occurrences(slide1, "<a:tr ") equals `3`
   - Expected: _count_occurrences(slide1, "<a:tc>") equals `9`
   - Expected: _count_occurrences(slide1, "<a:rPr b=\"1\"/>") equals `3`
   - Expected: _count_occurrences(slide1, "<a:srgbClr val=\"D9E2F3\"/>") equals `3`
   - Expected: test_result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("emits a p:graphicFrame with a:tbl, 3 a:gridCol and 3 a:tr for a 3x(1+2) table")
step("Verify: emits a p:graphicFrame with a:tbl, 3 a:gridCol and 3 a:tr for a 3x(1+2) table")
# @req: REQ-APP-OFFICE-001
val deck = parse_deck(_DECK_SRC)
val pptx = deck_to_pptx_bytes(deck)
val slide1 = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide1).to_contain("<p:graphicFrame>")
expect(slide1).to_contain("uri=\"http://schemas.openxmlformats.org/drawingml/2006/table\"")
expect(slide1).to_contain("<a:tbl>")
expect(_count_occurrences(slide1, "<a:gridCol ")).to_equal(3)
expect(_count_occurrences(slide1, "<a:tr ")).to_equal(3)
# every row is full: 9 cells, txBody-before-tcPr order
expect(_count_occurrences(slide1, "<a:tc>")).to_equal(9)
# header styling: bold run + light solid fill on the 3 header cells
expect(_count_occurrences(slide1, "<a:rPr b=\"1\"/>")).to_equal(3)
expect(_count_occurrences(slide1, "<a:srgbClr val=\"D9E2F3\"/>")).to_equal(3)
# cell texts land in a:t runs
expect(slide1).to_contain("<a:t>h1</a:t>")
expect(slide1).to_contain("<a:t>f</a:t>")
# persist for the system-unzip cross-check (ground truth)
val out_path = "{_SCRATCH}/pptx_tables_spec_3col.pptx"
File.write_bytes(out_path, pptx)
val test_result = run("unzip", ["-t", out_path])
expect(test_result.exit_code).to_equal(0)  # oracle: 0 — named expected value from the requirement
```

</details>

#### escapes cell text and system unzip validates the archive

- escapes cell text and system unzip validates the archive
- Verify: escapes cell text and system unzip validates the archive
   - Expected: test_result.exit_code equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("escapes cell text and system unzip validates the archive")
step("Verify: escapes cell text and system unzip validates the archive")
val deck = parse_deck("Esc\n| A&B | <ok> |\n| --- | --- |\n| x | y |")
val pptx = deck_to_pptx_bytes(deck)
val slide1 = zip_extract_text(pptx, "ppt/slides/slide1.xml")
expect(slide1).to_contain("<a:t>A&amp;B</a:t>")
expect(slide1).to_contain("<a:t>&lt;ok&gt;</a:t>")
val out_path = "{_SCRATCH}/pptx_tables_spec.pptx"
File.write_bytes(out_path, pptx)
val test_result = run("unzip", ["-t", out_path])
expect(test_result.exit_code).to_equal(0)  # oracle: 0 — named expected value from the requirement
# system cross-check: unzip -p shows the a:tbl in the slide part
val cat_result = run("unzip", ["-p", out_path, "ppt/slides/slide1.xml"])
expect(cat_result.stdout).to_contain("<a:tbl>")
expect(cat_result.stdout).to_contain("<a:gridCol ")
```

</details>

### PPTX tables: import round-trip

#### preserves the table block in position through deck -> pptx -> deck

- preserves the table block in position through deck -> pptx -> deck
- Verify: preserves the table block in position through deck -> pptx -> deck
   - Expected: deck_to_text(deck) equals `_DECK_SRC`
   - Expected: deck2.len() equals `1`
   - Expected: deck_to_text(deck2) equals `_DECK_SRC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves the table block in position through deck -> pptx -> deck")
step("Verify: preserves the table block in position through deck -> pptx -> deck")
val deck = parse_deck(_DECK_SRC)
expect(deck_to_text(deck)).to_equal(_DECK_SRC)
val pptx = deck_to_pptx_bytes(deck)
val deck2 = pptx_bytes_to_deck(pptx)
expect(deck2.len()).to_equal(1)  # oracle: 1 — named expected value from the requirement
expect(deck_to_text(deck2)).to_equal(_DECK_SRC)
```

</details>

#### round-trips escaped cell text through the pptx package

- round-trips escaped cell text through the pptx package
- Verify: round-trips escaped cell text through the pptx package
   - Expected: deck_to_text(deck2) equals `src`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("round-trips escaped cell text through the pptx package")
step("Verify: round-trips escaped cell text through the pptx package")
val src = "Esc\n| A&B | <ok> |\n| --- | --- |\n| x | y |"
val deck = parse_deck(src)
val pptx = deck_to_pptx_bytes(deck)
val deck2 = pptx_bytes_to_deck(pptx)
expect(deck_to_text(deck2)).to_equal(src)
```

</details>

### PPTX tables: HTML render

#### renders a border-collapse table with a bold th header row

- renders a border-collapse table with a bold th header row
- Verify: renders a border-collapse table with a bold th header row
   - Expected: _count_occurrences(html, "<th ") equals `3`
   - Expected: _count_occurrences(html, "<td ") equals `6`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("renders a border-collapse table with a bold th header row")
step("Verify: renders a border-collapse table with a bold th header row")
val deck = parse_deck(_DECK_SRC)
val html = render_slide_html(deck[0])
expect(html).to_contain("<table style=\"border-collapse: collapse;")
expect(_count_occurrences(html, "<th ")).to_equal(3)
expect(_count_occurrences(html, "<td ")).to_equal(6)
expect(html).to_contain("font-weight: bold")
expect(html).to_contain(">h1</th>")
expect(html).to_contain(">f</td>")
# separator row is deck notation — never rendered
expect(html.contains("---")).to_be(false)
```

</details>

#### escapes cell text in the rendered table

- escapes cell text in the rendered table
- Verify: escapes cell text in the rendered table


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("escapes cell text in the rendered table")
step("Verify: escapes cell text in the rendered table")
val deck = parse_deck("Esc\n| A&B | <ok> |\n| --- | --- |\n| x | y |")
val html = render_slide_html(deck[0])
expect(html).to_contain(">A&amp;B</th>")
expect(html).to_contain(">&lt;ok&gt;</th>")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-APP`
- `REQ-APP-OFFICE-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `efabd8738696e77e1a06c6e983066b8cb2d529a44b07c45052297f728d10d9c6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `efabd8738696e77e1a06c6e983066b8cb2d529a44b07c45052297f728d10d9c6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `efabd8738696e77e1a06c6e983066b8cb2d529a44b07c45052297f728d10d9c6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/app/office/pptx_tables_spec.spl
mirror: doc/06_spec/01_unit/app/office/pptx_tables_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/pptx_tables_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/pptx_tables_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/pptx_tables_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/office/pptx_tables_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a p:graphicFrame with a:tbl, 3 a:gridCol and 3 a:tr for a 3x(1+2) table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/pptx_tables_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes cell text and system unzip validates the archive' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/pptx_tables_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves the table block in position through deck -> pptx -> deck' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
