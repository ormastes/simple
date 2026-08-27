# Html Window Specification

> Tests covering shared HTML window content.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Window Specification

## Scenarios

### shared HTML window content

#### wraps body HTML with reusable base CSS

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- wraps body HTML with reusable base CSS


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("wraps body HTML with reusable base CSS")
val html = html_window_content("Demo", html_pre_block("hello"), ".extra{color:red}")

expect(html).to_contain("simple-app-window")
expect(html).to_contain("simple-app-title")
expect(html).to_contain("simple-titlebar-label")
expect(html).to_contain("simple-app-pre")
expect(html).to_contain(".extra{color:red}")
```

</details>

#### bumps the titlebar widget to a 44px touch target on touch devices

- bumps the titlebar widget to a 44px touch target on touch devices


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bumps the titlebar widget to a 44px touch target on touch devices")
val html = html_window_content("Demo", html_pre_block("hello"), "")

# Touch-target rule must key on hover:none (the Android emulator and many
# touch devices report pointer:fine), and reach the 44px/48px minimums.
expect(html).to_contain("@media (hover:none),(pointer:coarse)")
expect(html).to_contain("min-height:44px;min-width:44px")
expect(html).to_contain(".simple-app-title{min-height:48px;}")
# Desktop default stays compact.
expect(html).to_contain("min-height:24px")
```

</details>

#### renders title bar widgets with reusable CSS hooks

- renders title bar widgets with reusable CSS hooks


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("renders title bar widgets with reusable CSS hooks")
val widget = html_titlebar_button("refresh", "Refresh") + html_titlebar_text_input("filter", "ready")
val html = html_window_content_with_titlebar_widgets("Demo", html_pre_block("hello"), widget, ".simple-titlebar-widget{color:lime}")

expect(widget).to_contain("data-simple-titlebar-widget=\"button\"")
expect(widget).to_contain("data-simple-titlebar-widget=\"input\"")
expect(widget).to_contain("data-action=\"refresh\"")
expect(widget).to_contain("data-target-id=\"filter\"")
expect(widget).to_contain("type=\"text\"")
expect(html).to_contain("simple-titlebar-widgets")
expect(html).to_contain("data-action=\"refresh\"")
expect(html).to_contain(".simple-titlebar-input{width:116px;min-width:96px;font-weight:500;cursor:text;}")
expect(html).to_contain(".simple-titlebar-widget{color:lime}")
```

</details>

#### builds picture markup from embedded data URIs

- builds picture markup from embedded data URIs
   - Expected: uri equals `data:image/png;base64,abcd`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds picture markup from embedded data URIs")
val uri = html_embedded_image_data_uri("image/png", "abcd")
val pic = html_picture(uri, "Logo")

expect(uri).to_equal("data:image/png;base64,abcd")
expect(pic).to_contain("<picture")
expect(pic).to_contain("src=\"data:image/png;base64,abcd\"")
expect(pic).to_contain("alt=\"Logo\"")
```

</details>

#### escapes text, titles, and picture attributes

- escapes text, titles, and picture attributes


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("escapes text, titles, and picture attributes")
val html = html_window_content("A < B", html_pre_block("<script>alert(1)</script>"), "")
val pic = html_picture("x\" onerror=\"bad", "A & B")

expect(html).to_contain("A &lt; B")
expect(html).to_contain("&lt;script&gt;alert(1)&lt;/script&gt;")
expect(pic).to_contain("src=\"x&quot; onerror=&quot;bad\"")
expect(pic).to_contain("alt=\"A &amp; B\"")
expect(html_titlebar_button("x\" onclick=\"bad", "A < B")).to_contain("data-action=\"x&quot; onclick=&quot;bad\"")
expect(html_titlebar_button("ok", "A < B")).to_contain("A &lt; B")
expect(html_titlebar_text_input("x\" autofocus bad", "A < B")).to_contain("data-target-id=\"x&quot; autofocus bad\"")
expect(html_titlebar_text_input("ok", "A < B")).to_contain("value=\"A &lt; B\"")
```

</details>

#### exposes CSS blocks for backend-neutral base rendering

- exposes CSS blocks for backend-neutral base rendering
   - Expected: block equals `<style>.demo{color:red}</style>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exposes CSS blocks for backend-neutral base rendering")
val block = html_css_block(".demo{color:red}")

expect(block).to_equal("<style>.demo{color:red}</style>")
```

</details>

#### builds WindowInfo using shared HTML content

- builds WindowInfo using shared HTML content
   - Expected: info.id equals `files`
   - Expected: info.title equals `Files`
   - Expected: info.x equals `1`
   - Expected: info.width equals `300`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds WindowInfo using shared HTML content")
val info = html_window_info("files", "Files", html_picture("file.png", "File"), "", 1, 2, 300, 200)

expect(info.id).to_equal("files")
expect(info.title).to_equal("Files")
expect(info.html).to_contain("simple-picture")
expect(info.x).to_equal(1)
expect(info.width).to_equal(300)
```

</details>

#### builds WindowInfo with title bar widgets

- builds WindowInfo with title bar widgets
   - Expected: info.id equals `terminal`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("builds WindowInfo with title bar widgets")
val info = html_window_info_with_titlebar_widgets("terminal", "Terminal", html_pre_block("ready"), html_titlebar_button("run", "Run"), "", 4, 5, 320, 240)

expect(info.id).to_equal("terminal")
expect(info.html).to_contain("simple-titlebar-widget")
expect(info.html).to_contain("data-action=\"run\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/html_window_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering shared HTML window content.
- shared HTML window content

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `ae03e81dbc827e257ee71ff32df1661d7e4e50ed145b00219465e4cc2006ae57`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ae03e81dbc827e257ee71ff32df1661d7e4e50ed145b00219465e4cc2006ae57`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ae03e81dbc827e257ee71ff32df1661d7e4e50ed145b00219465e4cc2006ae57`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/common/ui/html_window_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/html_window_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/html_window_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/html_window_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/html_window_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/ui/html_window_spec.spl:19:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'wraps body HTML with reusable base CSS' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/html_window_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bumps the titlebar widget to a 44px touch target on touch devices' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/html_window_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders title bar widgets with reusable CSS hooks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
