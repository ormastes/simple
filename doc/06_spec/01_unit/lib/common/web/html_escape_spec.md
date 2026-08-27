# Html Escape Specification

> Tests covering canonical html_escape, html_escape wrapper parity across all former duplicates.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Html Escape Specification

## Scenarios

### canonical html_escape

#### escapes all 5 special characters, amp first

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- escapes all 5 special characters, amp first
   - Expected: html_escape("& < > \" '") equals `&amp; &lt; &gt; &quot; &#39;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes all 5 special characters, amp first")
expect(html_escape("& < > \" '")).to_equal("&amp; &lt; &gt; &quot; &#39;")
```

</details>

#### does not double-escape when amp is escaped first

- does not double-escape when amp is escaped first
   - Expected: html_escape("&amp;") equals `&amp;amp;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not double-escape when amp is escaped first")
expect(html_escape("&amp;")).to_equal("&amp;amp;")
```

</details>

#### html_attr_escape matches html_escape (double-quoted attrs)

- html_attr_escape matches html_escape (double-quoted attrs)
   - Expected: html_attr_escape("a\"b'c") equals `html_escape("a"b'c")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("html_attr_escape matches html_escape (double-quoted attrs)")
expect(html_attr_escape("a\"b'c")).to_equal(html_escape("a\"b'c"))
```

</details>

#### html_escape_core matches html_escape (same underlying implementation)

- html_escape_core matches html_escape (same underlying implementation)
   - Expected: html_escape_core("a\"b'c") equals `html_escape("a"b'c")`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("html_escape_core matches html_escape (same underlying implementation)")
expect(html_escape_core("a\"b'c")).to_equal(html_escape("a\"b'c"))
```

</details>

#### passes through text with no special characters

- passes through text with no special characters
   - Expected: html_escape("hello world") equals `hello world`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes through text with no special characters")
expect(html_escape("hello world")).to_equal("hello world")
```

</details>

### html_escape wrapper parity across all former duplicates

#### app.ui.render.html.html_escape matches canonical

- app.ui.render.html.html_escape matches canonical
   - Expected: render_html_escape(sample) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("app.ui.render.html.html_escape matches canonical")
expect(render_html_escape(sample)).to_equal(expected)
```

</details>

#### common.ui.html_window.html_escape matches canonical

- common.ui.html_window.html_escape matches canonical
   - Expected: window_html_escape(sample) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("common.ui.html_window.html_escape matches canonical")
expect(window_html_escape(sample)).to_equal(expected)
```

</details>

#### common.ui.html_window.html_attr_escape matches canonical

- common.ui.html_window.html_attr_escape matches canonical
   - Expected: window_html_attr_escape(sample) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("common.ui.html_window.html_attr_escape matches canonical")
expect(window_html_attr_escape(sample)).to_equal(expected)
```

</details>

#### common.ui.mobile_html_gen.html_gen_escape_text matches canonical

- common.ui.mobile_html_gen.html_gen_escape_text matches canonical
   - Expected: html_gen_escape_text(sample) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("common.ui.mobile_html_gen.html_gen_escape_text matches canonical")
expect(html_gen_escape_text(sample)).to_equal(expected)
```

</details>

#### common.ui.mobile_html_gen.html_gen_escape_attr matches canonical

- common.ui.mobile_html_gen.html_gen_escape_attr matches canonical
   - Expected: html_gen_escape_attr(sample) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("common.ui.mobile_html_gen.html_gen_escape_attr matches canonical")
expect(html_gen_escape_attr(sample)).to_equal(expected)
```

</details>

#### gc_async_mut.web.browser_session_html.escape_html_text matches canonical

- gc_async_mut.web.browser_session_html.escape_html_text matches canonical
   - Expected: escape_html_text(sample) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("gc_async_mut.web.browser_session_html.escape_html_text matches canonical")
expect(escape_html_text(sample)).to_equal(expected)
```

</details>

#### every wrapper escapes a lone apostrophe (older copies missed this)

- every wrapper escapes a lone apostrophe (older copies missed this)
   - Expected: render_html_escape("'") equals `&#39;`
   - Expected: window_html_escape("'") equals `&#39;`
   - Expected: html_gen_escape_text("'") equals `&#39;`
   - Expected: escape_html_text("'") equals `&#39;`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("every wrapper escapes a lone apostrophe (older copies missed this)")
expect(render_html_escape("'")).to_equal("&#39;")
expect(window_html_escape("'")).to_equal("&#39;")
expect(html_gen_escape_text("'")).to_equal("&#39;")
expect(escape_html_text("'")).to_equal("&#39;")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/web/html_escape_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering canonical html_escape, html_escape wrapper parity across all former duplicates.
- canonical html_escape
- html_escape wrapper parity across all former duplicates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `0adbc50a0a0d931bc94c1ab1a872b310822aceda92c7e0fa426fc8ad3ae9c251`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0adbc50a0a0d931bc94c1ab1a872b310822aceda92c7e0fa426fc8ad3ae9c251`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0adbc50a0a0d931bc94c1ab1a872b310822aceda92c7e0fa426fc8ad3ae9c251`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/web/html_escape_spec.spl
mirror: doc/06_spec/01_unit/lib/common/web/html_escape_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/web/html_escape_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/web/html_escape_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/web/html_escape_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes all 5 special characters, amp first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/html_escape_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not double-escape when amp is escaped first' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/web/html_escape_spec.spl:36:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'html_attr_escape matches html_escape (double-quoted attrs)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
