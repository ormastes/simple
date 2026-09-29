# Mobile Html Gen Specification

> Tests covering mobile_html_gen — Simple generates HTML from a node model.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mobile Html Gen Specification

## Scenarios

### mobile_html_gen — Simple generates HTML from a node model

#### renders a leaf button to exact markup

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- renders a leaf button to exact markup
   - Expected: html equals `<button id="hello_button" data-action="go">Hello World</button>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a leaf button to exact markup")
val html = html_node_render(hello_button())
expect(html).to_equal("<button id=\"hello_button\" data-action=\"go\">Hello World</button>")
```

</details>

#### renders a void input with no closing tag

- renders a void input with no closing tag
   - Expected: html equals `<input id="hello_text" value="Generated UI">`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders a void input with no closing tag")
val html = html_node_render(hello_input())
expect(html).to_equal("<input id=\"hello_text\" value=\"Generated UI\">")
```

</details>

#### renders nested children in order

- renders nested children in order
   - Expected: html equals `<nav id="hello_taskbar"><button id="hello_taskbar_home">Home</button><button ... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders nested children in order")
val html = html_node_render(hello_nav())
expect(html).to_equal("<nav id=\"hello_taskbar\"><button id=\"hello_taskbar_home\">Home</button><button id=\"hello_taskbar_apps\">Apps</button></nav>")
```

</details>

#### escapes text content (no HTML injection)

- escapes text content (no HTML injection)
   - Expected: html equals `<span>&lt;script&gt;x&lt;/script&gt;&amp;y</span>`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes text content (no HTML injection)")
val node = html_leaf("span", [], "<script>x</script>&y")
val html = html_node_render(node)
expect(html).to_equal("<span>&lt;script&gt;x&lt;/script&gt;&amp;y</span>")
```

</details>

#### escapes attribute values

- escapes attribute values
   - Expected: html equals `<input value="a&quot;b&lt;c">`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("escapes attribute values")
val node = html_void("input", [attr("value", "a\"b<c")])
val html = html_node_render(node)
expect(html).to_equal("<input value=\"a&quot;b&lt;c\">")
```

</details>

#### wraps a full document with title + css + body

- wraps a full document with title + css + body
   - Expected: doc contains `<title>Hello</title>`
   - Expected: doc contains `<style>button{min-height:44px;}</style>`
   - Expected: doc contains `<button id="hello_button" data-action="go">Hello World</button>`
   - Expected: doc.starts_with("<!doctype html>") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("wraps a full document with title + css + body")
val body = html_node_render(hello_button())
val doc = html_gen_document("Hello", body, "button{min-height:44px;}")
expect(doc.contains("<title>Hello</title>")).to_equal(true)
expect(doc.contains("<style>button{min-height:44px;}</style>")).to_equal(true)
expect(doc.contains("<button id=\"hello_button\" data-action=\"go\">Hello World</button>")).to_equal(true)
expect(doc.starts_with("<!doctype html>")).to_equal(true)
```

</details>

#### generated body matches the hello reference structure (id markers)

- generated body matches the hello reference structure (id markers)
   - Expected: body contains `data-simple-wasm="hello"`
   - Expected: body contains `id="hello_taskbar"`
   - Expected: body contains `id="hello_button"`
   - Expected: body contains `id="hello_text"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("generated body matches the hello reference structure (id markers)")
val body = html_node_render(html_node("main", [attr("data-simple-wasm", "hello")], [
    hello_nav(), hello_button(), hello_input()
]))
# absolute oracle: the same id markers the hand-authored hello body exposes
expect(body.contains("data-simple-wasm=\"hello\"")).to_equal(true)
expect(body.contains("id=\"hello_taskbar\"")).to_equal(true)
expect(body.contains("id=\"hello_button\"")).to_equal(true)
expect(body.contains("id=\"hello_text\"")).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/ui/mobile_html_gen_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering mobile_html_gen — Simple generates HTML from a node model.
- mobile_html_gen — Simple generates HTML from a node model

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

- Canonical SPipe generation for source `ee227e2ffbb08c25d62d2a5d26f9178344bdcb82268d10c8f81506f5b126c988`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ee227e2ffbb08c25d62d2a5d26f9178344bdcb82268d10c8f81506f5b126c988`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ee227e2ffbb08c25d62d2a5d26f9178344bdcb82268d10c8f81506f5b126c988`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/ui/mobile_html_gen_spec.spl
mirror: doc/06_spec/01_unit/lib/common/ui/mobile_html_gen_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/ui/mobile_html_gen_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/ui/mobile_html_gen_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/ui/mobile_html_gen_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a leaf button to exact markup' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/mobile_html_gen_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders a void input with no closing tag' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/ui/mobile_html_gen_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'renders nested children in order' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
