# Browser Renderer Script Specification

> <details>

<!-- sdn-diagram:id=browser_renderer_script_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_renderer_script_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_renderer_script_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_renderer_script_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Renderer Script Specification

## Scenarios

### Browser renderer script collection

#### html_tree_builder_build_with_scripts collects script bodies

#### collects inline script body from HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head></head><body><script>val x = 1</script></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(1)
expect(result.script_types.len()).to_equal(1)
expect(result.script_types[0]).to_equal("")
```

</details>

#### collects inline script type metadata

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head></head><body><script type='text/simple'>val x = 1</script></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(1)
expect(result.script_types[0]).to_equal("text/simple")
```

</details>

#### collects multiple script bodies

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><script>val a = 1</script></head><body><script>val b = 2</script></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(2)
```

</details>

#### collects script src paths

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><script src='app.spl' type='text/simple'></script></head><body></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.src_paths.len()).to_equal(1)
expect(result.src_types.len()).to_equal(1)
expect(result.src_types[0]).to_equal("text/simple")
```

</details>

#### returns empty scripts for script-free HTML

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head></head><body><div>hello</div></body></html>"
val result = browser_renderer_parse_html_with_scripts(html)
expect(result.scripts.len()).to_equal(0)
expect(result.src_paths.len()).to_equal(0)
```

</details>

#### render_html_to_pixels_with_scripts integrates rendering and collection

#### renders HTML and reports collected script count

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #ff0000; }</style><script>val x = 1</script></head><body></body></html>"
val result = render_html_to_pixels_with_scripts(html, WIDTH, HEIGHT)
expect(result.scripts_collected).to_equal(1)
```

</details>

#### renders correctly with no scripts

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head><style>body { margin: 0; background-color: #00ff00; }</style></head><body></body></html>"
val result = render_html_to_pixels_with_scripts(html, WIDTH, HEIGHT)
expect(result.scripts_collected).to_equal(0)
expect(result.scripts_executed).to_equal(0)
```

</details>

#### captures console output from executed script

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head></head><body><script>print(\"hello from script\")</script></body></html>"
val result = render_html_to_pixels_with_scripts(html, WIDTH, HEIGHT)
expect(result.scripts_executed).to_equal(1)
expect(result.console_output.len()).to_equal(1)
expect(result.console_output[0]).to_contain("hello from script")
```

</details>

#### executes default script tags as JavaScript

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val html = "<html><head></head><body><script>const msg = \"hello from js\"\nprint(msg)</script></body></html>"
val result = render_html_to_pixels_with_scripts(html, WIDTH, HEIGHT)
expect(result.scripts_executed).to_equal(1)
expect(result.console_output.len()).to_equal(1)
expect(result.console_output[0]).to_contain("hello from js")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/browser_renderer_script_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser renderer script collection

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
