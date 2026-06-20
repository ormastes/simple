# Plugins Specification

> _Each cataloged Office app is registered as a distinct plugin entry._

<!-- sdn-diagram:id=plugins_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=plugins_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

plugins_spec -> std
plugins_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=plugins_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Plugins Specification

## Scenarios

### office plugins: suite plugins on shared substrates
_Each cataloged Office app is registered as a distinct plugin entry._

#### registers each cataloged office app

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(office_plugin_names().len()).to_equal(11)
```

</details>

#### names the document, design, data, math, and utility plugins

<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = office_plugin_names()
expect(names).to_contain("office-markdown")
expect(names).to_contain("office-writer")
expect(names).to_contain("office-calc")
expect(names).to_contain("office-impress")
expect(names).to_contain("office-draw")
expect(names).to_contain("office-designer")
expect(names).to_contain("office-base")
expect(names).to_contain("office-math")
expect(names).to_contain("office-mail")
expect(names).to_contain("office-planner")
expect(names).to_contain("office-counter")
```

</details>

### office plugins: manifest round-trips and validates

#### round-trips through the registry manifest format

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# plugin_count is the number of entries parsed back out of the manifest;
# equalling the 11 input entries proves the manifest round-trips.
val probe = office_plugin_manifest_probe()
expect(probe.plugin_count).to_equal(11)
```

</details>

#### is a well-formed manifest (validation returns no error)

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val err = office_plugin_validate(office_plugin_entries())
expect(err).to_equal("")
```

</details>

#### the serialized manifest names each plugin

<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val probe = office_plugin_manifest_probe()
val manifest = probe.manifest_text
expect(manifest).to_contain("office-writer")
expect(manifest).to_contain("office-draw")
expect(manifest).to_contain("office-designer")
expect(manifest).to_contain("office-mail")
expect(manifest).to_contain("office-planner")
expect(manifest).to_contain("render-writer-markdown-html")
expect(manifest).to_contain("writer-markdown-summary")
expect(manifest).to_contain("render-sdd-html-with-selection")
expect(manifest).to_contain("render-ui-html")
expect(manifest).to_contain("render-ui-html-with-selection")
expect(manifest).to_contain("ui-css-edit")
expect(manifest).to_contain("mail-summary")
expect(manifest).to_contain("planner-summary")
```

</details>

#### rejects empty plugin libraries

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val malformed = plugin_entry_new("office-word", "", "0.1.0", ["render_document_html"])
expect(office_plugin_validate([malformed])).to_equal("manifest error: entry 'office-word' has empty library")
```

</details>

#### rejects empty and duplicate function names

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val empty_function = plugin_entry_new("office-word", "app.office.word.html_render", "0.1.0", [""])
val word = plugin_entry_new("office-word", "app.office.word.html_render", "0.1.0", ["render_document_html"])
val ppt = plugin_entry_new("office-ppt", "app.office.slides.html_render", "0.1.0", ["render_document_html"])
expect(office_plugin_validate([empty_function])).to_equal("manifest error: entry 'office-word' has empty function")
expect(office_plugin_validate([word, ppt])).to_equal("manifest error: duplicate function 'render_document_html'")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/plugins_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- office plugins: suite plugins on shared substrates
- office plugins: manifest round-trips and validates

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
