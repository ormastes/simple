# Libreoffice Specification

> _The suite and its six applications carry their LibreOffice names._

<!-- sdn-diagram:id=libreoffice_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=libreoffice_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

libreoffice_spec -> std
libreoffice_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=libreoffice_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Libreoffice Specification

## Scenarios

### LibreOffice branding: suite and application names
_The suite and its six applications carry their LibreOffice names._

#### names the suite LibreOffice

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libreoffice_suite_name()).to_equal("LibreOffice")
```

</details>

#### maps word/excel/ppt to Writer/Calc/Impress

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libreoffice_app_name("word")).to_equal("Writer")
expect(libreoffice_app_name("excel")).to_equal("Calc")
expect(libreoffice_app_name("ppt")).to_equal("Impress")
```

</details>

#### maps draw/db/math to Draw/Base/Math

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libreoffice_app_name("draw")).to_equal("Draw")
expect(libreoffice_app_name("db")).to_equal("Base")
expect(libreoffice_app_name("math")).to_equal("Math")
```

</details>

#### fails closed for unknown components and accepts counter routes

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(is_office_component("word")).to_be(true)
expect(is_office_component("sheets")).to_be(true)
expect(is_office_component("counter")).to_be(true)
expect(libreoffice_app_name_checked("counter")).to_equal("Counter")
expect(libreoffice_app_name_checked("unknown")).to_equal("error: unknown LibreOffice component: unknown")
val route = lookup_office_component("counter")
expect(route.valid).to_be(true)
expect(route.status).to_equal("component")
expect(route.component).to_equal("counter")
```

</details>

#### resolves launcher actions including counter actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val sheets = office_component_for_action("open_sheets")
expect(sheets.is_some()).to_be(true)
expect(sheets.unwrap()).to_equal("sheets")
val counter = office_component_for_action("open_counter")
expect(counter.is_some()).to_be(true)
expect(counter.unwrap()).to_equal("counter")
```

</details>

#### lists all six LibreOffice applications

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(libreoffice_apps().len()).to_equal(6)
```

</details>

### LibreOffice branding: implemented status
_All six LibreOffice apps now render/compute through the suite._

#### reports all six LibreOffice applications as implemented

<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val names = libreoffice_implemented_apps()
expect(names.len()).to_equal(6)
expect(names).to_contain("Writer")
expect(names).to_contain("Calc")
expect(names).to_contain("Impress")
expect(names).to_contain("Draw")
expect(names).to_contain("Base")
expect(names).to_contain("Math")
```

</details>

#### emits a LibreOffice-branded plugin entry per application

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val entries = libreoffice_plugin_entries()
expect(entries.len()).to_equal(6)
val first = entries[0]
expect(first.name).to_equal("libreoffice-writer")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/office/libreoffice_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- LibreOffice branding: suite and application names
- LibreOffice branding: implemented status

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
