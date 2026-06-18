# Browser Session Stylesheet Source Bounds Spec

> HTML `<style>` / `<link rel=stylesheet>` extraction, CSS `@import` extraction, and recursive insertion all allocate arrays from input-derived counts. They must share one explicit cap so hostile documents cannot grow the stylesheet queue without bound before rendering or script execution.

<!-- sdn-diagram:id=browser_session_stylesheet_source_bounds_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=browser_session_stylesheet_source_bounds_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

browser_session_stylesheet_source_bounds_spec -> std
browser_session_stylesheet_source_bounds_spec -> common
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=browser_session_stylesheet_source_bounds_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Browser Session Stylesheet Source Bounds Spec

HTML `<style>` / `<link rel=stylesheet>` extraction, CSS `@import` extraction, and recursive insertion all allocate arrays from input-derived counts. They must share one explicit cap so hostile documents cannot grow the stylesheet queue without bound before rendering or script execution.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | .spipe/web_rendering_backend_animation_hardening/state.md |
| Design | doc/04_architecture/ui/simple_gui_stack.md |
| Research | N/A |
| Source | `test/01_unit/lib/common/web/browser_session_stylesheet_source_bounds_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

HTML `<style>` / `<link rel=stylesheet>` extraction, CSS `@import` extraction,
and recursive insertion all allocate arrays from input-derived counts. They
must share one explicit cap so hostile documents cannot grow the stylesheet
queue without bound before rendering or script execution.

## Requirements

**Requirements:** N/A

## Plan

**Plan:** .spipe/web_rendering_backend_animation_hardening/state.md

## Design

**Design:** doc/04_architecture/ui/simple_gui_stack.md

## Research

**Research:** N/A

## Syntax

The spec uses `std.spec` and direct stylesheet source count assertions.

## Scenarios

### BrowserSessionStylesheetSourceBounds

#### caps extracted stylesheets, css imports, and inserted pending sources

<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val cap = browser_session_debug_max_stylesheet_sources()
val html = str_repeat("<style>.x { color: red; }</style>", cap + 8)
val sources = extract_stylesheet_sources(html)
expect(sources.len()).to_equal(cap)

val css = str_repeat("@import url('theme.css');\n", cap + 8)
val imports = extract_css_import_sources("https://example.com/app/main.css", css)
expect(imports.len()).to_equal(cap)

val existing = [BrowserStylesheetSource.external("first.css")]
val combined = insert_stylesheet_sources(existing, 1, imports)
expect(combined.len()).to_equal(cap)
expect(combined[0].source).to_equal("first.css")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [.spipe/web_rendering_backend_animation_hardening/state.md](.spipe/web_rendering_backend_animation_hardening/state.md)
- **Design:** [doc/04_architecture/ui/simple_gui_stack.md](doc/04_architecture/ui/simple_gui_stack.md)


</details>
