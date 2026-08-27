# Html Builder Specification

> Tests covering html builder helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Builder Specification

## Scenarios

### html builder helpers

#### escapes html special characters

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- escapes html special characters
   - Expected: html_escape("<a b=\"c&d\">'x'</a>") equals `&lt;a b=&quot;c&amp;d&quot;&gt;&#39;x&#39;&lt;/a&gt;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes html special characters")
expect(html_escape("<a b=\"c&d\">'x'</a>")).to_equal("&lt;a b=&quot;c&amp;d&quot;&gt;&#39;x&#39;&lt;/a&gt;")
```

</details>

#### builds a complete html page with escaped title

- builds a complete html page with escaped title


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds a complete html page with escaped title")
val page = html_page("A&B", "body { color:red; }", "<main>Hi</main>")
expect(page).to_contain("<!DOCTYPE html>")
expect(page).to_contain("<title>A&amp;B</title>")
expect(page).to_contain("body { color:red; }")
expect(page).to_contain("<main>Hi</main>")
```

</details>

#### builds grid containers without reordering items

- builds grid containers without reordering items
   - Expected: html equals `<div style="display:grid; grid-template-columns:repeat(2, 1fr); gap:8px">\n  ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds grid containers without reordering items")
val html = html_grid(2, "8px", ["<span>A</span>", "<span>B</span>"])
expect(html).to_equal("<div style=\"display:grid; grid-template-columns:repeat(2, 1fr); gap:8px\">\n  <span>A</span>\n  <span>B</span>\n</div>\n")
```

</details>

#### builds cards with escaped titles and raw body content

- builds cards with escaped titles and raw body content


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds cards with escaped titles and raw body content")
val html = html_card("A < B", "<p>Body</p>")
expect(html).to_contain("<h3>A &lt; B</h3>")
expect(html).to_contain("<div class=\"card-body\"><p>Body</p></div>")
```

</details>

#### builds progress bars with clamped values

- builds progress bars with clamped values


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds progress bars with clamped values")
val html = html_progress_bar(140)
expect(html).to_contain("width:100%")
expect(html).to_contain("var(--green, #3fb950)")
```

</details>

#### builds tables with escaped headers and cells

- builds tables with escaped headers and cells


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds tables with escaped headers and cells")
val html = html_table(["Name"], [["A&B"], ["<tag>"]])
expect(html).to_contain("<th>Name</th>")
expect(html).to_contain("<td>A&amp;B</td>")
expect(html).to_contain("<td>&lt;tag&gt;</td>")
```

</details>

#### builds reset and dark theme css snippets

- builds reset and dark theme css snippets


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("builds reset and dark theme css snippets")
expect(css_reset()).to_contain("box-sizing: border-box")
expect(css_dark_theme()).to_contain("--bg: #0d1117")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/ui/html_builder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering html builder helpers.
- html builder helpers

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a4887ed6be10a25357a5d464e27445237c064fba9e8a00e4694a935cda23a281`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a4887ed6be10a25357a5d464e27445237c064fba9e8a00e4694a935cda23a281`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a4887ed6be10a25357a5d464e27445237c064fba9e8a00e4694a935cda23a281`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/ui/html_builder_spec.spl
mirror: doc/06_spec/01_unit/app/ui/html_builder_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/ui/html_builder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/ui/html_builder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/ui/html_builder_spec.spl:24:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes html special characters' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/html_builder_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a complete html page with escaped title' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/ui/html_builder_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds grid containers without reordering items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
