# html_render_spec

> Slide HTML render spec.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# html_render_spec

Slide HTML render spec.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/slides/html_render_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Slide HTML render spec.

Verifies that `render_slide_html` renders a slide as a styled HTML fragment
using the shared office style resolver's slide theme — the "render PPT like MS
PowerPoint" slice of the LibreOffice suite. Element roles are inferred from the
slide layout and element position (first element = title; on a title slide the
second = subtitle; otherwise = body), and each gets the resolver's Word-level
slide styling inlined.

All assertions are over the produced HTML string, so they run on the test
runner without the f64/i32 toolchain fragility.

## Scenarios

### slide HTML render: title slide

#### wraps the slide in a styled <section>

- wraps the slide in a styled <section>


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps the slide in a styled <section>")
val html = render_slide_html(title_slide("s1", "My Talk", "A subtitle"))
expect(html).to_start_with("<section class=\"slide\"")
expect(html).to_end_with("</section>")
```

</details>

#### styles the title as slide_title (bold, centered, 2.5em)

- styles the title as slide_title (bold, centered, 2.5em)


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("styles the title as slide_title (bold, centered, 2.5em)")
val html = render_slide_html(title_slide("s1", "My Talk", "A subtitle"))
expect(html).to_contain("class=\"slide_title\"")
expect(html).to_contain("font-size: 2.5em;")
expect(html).to_contain("text-align: center;")
expect(html).to_contain(">My Talk</div>")
```

</details>

#### styles the second element as slide_subtitle

- styles the second element as slide_subtitle


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("styles the second element as slide_subtitle")
val html = render_slide_html(title_slide("s1", "My Talk", "A subtitle"))
expect(html).to_contain("class=\"slide_subtitle\"")
expect(html).to_contain(">A subtitle</div>")
```

</details>

### slide HTML render: content slide
_A content slide styles its non-title elements as slide_body._

#### styles the body element as slide_body

- styles the body element as slide_body


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("styles the body element as slide_body")
val html = render_slide_html(content_slide("s2", "Agenda", "First point"))
expect(html).to_contain("class=\"slide_title\"")
expect(html).to_contain("class=\"slide_body\"")
expect(html).to_contain(">First point</div>")
```

</details>

#### escapes text content before writing HTML

- escapes text content before writing HTML


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes text content before writing HTML")
val html = render_slide_html(content_slide("s3", "A&B", "<script>bad</script>"))
expect(html).to_contain(">A&amp;B</div>")
expect(html).to_contain("&lt;script&gt;bad&lt;/script&gt;")
expect(html.contains("<script>")).to_be(false)
```

</details>

#### sanitizes invalid background colors

- sanitizes invalid background colors


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("sanitizes invalid background colors")
val slide = Slide(
    id: "s4",
    layout: SlideLayout.Blank,
    elements: [],
    notes: "",
    background: "url(javascript:bad)",
    transition: ""
)
val html = render_slide_html(slide)
expect(html).to_contain("background: #ffffff;")
```

</details>

#### positions slide elements with clamped boxes

- positions slide elements with clamped boxes


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("positions slide elements with clamped boxes")
val slide = Slide(
    id: "s5",
    layout: SlideLayout.Blank,
    elements: [SlideElement(
        id: "e1",
        kind: SlideElementKind.TextBox(content: "Box"),
        x: -10,
        y: 20,
        width: 300,
        height: -40
    )],
    notes: "",
    background: "#112233",
    transition: ""
)
val html = render_slide_html(slide)
expect(html).to_contain("position: relative; width: 960px; height: 540px;")
expect(html).to_contain("left: 0px; top: 20px; width: 300px; height: 0px;")
```

</details>

### slide HTML render: speaker notes

#### renders a presenter-notes block when notes are set

- renders a presenter-notes block when notes are set


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a presenter-notes block when notes are set")
val slide = set_slide_notes(content_slide("s6", "Agenda", "First point"), "Remember to smile")
val html = render_slide_html(slide)
expect(html).to_contain("</section>")
expect(html).to_contain("class=\"slide-notes\"")
expect(html).to_contain("Remember to smile")
expect(html.contains("<style")).to_be(false)
```

</details>

#### omits the presenter-notes block when notes are empty

- omits the presenter-notes block when notes are empty


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits the presenter-notes block when notes are empty")
val html = render_slide_html(content_slide("s7", "Agenda", "First point"))
expect(html.contains("slide-notes")).to_be(false)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `cc2ff0a458f6eacc188bd50fb5812ecc3fcc13d97a8e90f59cbcf2bacebae11f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cc2ff0a458f6eacc188bd50fb5812ecc3fcc13d97a8e90f59cbcf2bacebae11f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cc2ff0a458f6eacc188bd50fb5812ecc3fcc13d97a8e90f59cbcf2bacebae11f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/office/slides/html_render_spec.spl
mirror: doc/06_spec/01_unit/app/office/slides/html_render_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/office/slides/html_render_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/office/slides/html_render_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/office/slides/html_render_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps the slide in a styled <section>' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/slides/html_render_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'styles the title as slide_title (bold, centered, 2.5em)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/office/slides/html_render_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'styles the second element as slide_subtitle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
