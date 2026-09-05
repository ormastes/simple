# Mobile Html Gen Specification

> <details>

<!-- sdn-diagram:id=mobile_html_gen_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mobile_html_gen_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mobile_html_gen_spec -> std
mobile_html_gen_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mobile_html_gen_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mobile Html Gen Specification

## Scenarios

### mobile_html_gen — Simple generates HTML from a node model

#### renders a leaf button to exact markup

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_node_render(hello_button())
expect(html).to_equal("<button id=\"hello_button\" data-action=\"go\">Hello World</button>")
```

</details>

#### renders a void input with no closing tag

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_node_render(hello_input())
expect(html).to_equal("<input id=\"hello_text\" value=\"Generated UI\">")
```

</details>

#### renders nested children in order

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = html_node_render(hello_nav())
expect(html).to_equal("<nav id=\"hello_taskbar\"><button id=\"hello_taskbar_home\">Home</button><button id=\"hello_taskbar_apps\">Apps</button></nav>")
```

</details>

#### escapes text content (no HTML injection)

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = html_leaf("span", [], "<script>x</script>&y")
val html = html_node_render(node)
expect(html).to_equal("<span>&lt;script&gt;x&lt;/script&gt;&amp;y</span>")
```

</details>

#### escapes attribute values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val node = html_void("input", [attr("value", "a\"b<c")])
val html = html_node_render(node)
expect(html).to_equal("<input value=\"a&quot;b&lt;c\">")
```

</details>

#### wraps a full document with title + css + body

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = html_node_render(hello_button())
val doc = html_gen_document("Hello", body, "button{min-height:44px;}")
expect(doc.contains("<title>Hello</title>")).to_equal(true)
expect(doc.contains("<style>button{min-height:44px;}</style>")).to_equal(true)
expect(doc.contains("<button id=\"hello_button\" data-action=\"go\">Hello World</button>")).to_equal(true)
expect(doc.starts_with("<!doctype html>")).to_equal(true)
```

</details>

#### generated body matches the hello reference structure (id markers)

- hello nav
   - Expected: body contains `data-simple-wasm="hello"`
   - Expected: body contains `id="hello_taskbar"`
   - Expected: body contains `id="hello_button"`
   - Expected: body contains `id="hello_text"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
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
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
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
