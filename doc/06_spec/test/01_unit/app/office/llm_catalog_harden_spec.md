# llm_catalog_harden_spec

> Verifies that the LLM-facing Office catalog rejects malformed app/action rows before agents use the metadata as an automation surface. The catalog is the small boundary between advertised Office capabilities and agent-dispatchable actions for Markdown, Writer, Calc, Impress, Draw, Designer, Base, Math, and Counter.

<!-- sdn-diagram:id=llm_catalog_harden_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=llm_catalog_harden_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

llm_catalog_harden_spec -> std
llm_catalog_harden_spec -> app
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=llm_catalog_harden_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llm_catalog_harden_spec

Verifies that the LLM-facing Office catalog rejects malformed app/action rows before agents use the metadata as an automation surface. The catalog is the small boundary between advertised Office capabilities and agent-dispatchable actions for Markdown, Writer, Calc, Impress, Draw, Designer, Base, Math, and Counter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/sys_test/ide_office_plugin_suite.md |
| Design | doc/07_guide/app/ide_office_plugin_suite.md |
| Research | N/A |
| Source | `test/01_unit/app/office/llm_catalog_harden_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Verifies that the LLM-facing Office catalog rejects malformed app/action rows
before agents use the metadata as an automation surface. The catalog is the
small boundary between advertised Office capabilities and agent-dispatchable
actions for Markdown, Writer, Calc, Impress, Draw, Designer, Base, Math, and
Counter.

## Examples

`office_llm_catalog_validate(office_llm_feature_catalog())` returns an empty
string for the shipped catalog. Duplicate app names, empty evidence keys, empty
feature lists, and duplicate action names return deterministic error text.

**Requirements:** N/A
**Plan:** doc/03_plan/sys_test/ide_office_plugin_suite.md
**Design:** doc/07_guide/app/ide_office_plugin_suite.md
**Research:** N/A

## Scenarios

### Office LLM catalog validation

#### accepts the shipped Office catalog

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(office_llm_catalog_is_valid()).to_be(true)
expect(office_llm_catalog_validate(office_llm_feature_catalog())).to_equal("")
```

</details>

#### rejects duplicate app names

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(office_llm_catalog_validate([_row("Markdown", ["render-md"]), _row("Markdown", ["render-md-2"])])).to_equal("catalog error: duplicate app 'Markdown'")
```

</details>

#### rejects empty evidence keys

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val malformed = OfficeLlmFeature(app_name: "Markdown", component: "markdown", owner_module: "app.office.md_wysiwyg", features: ["html-render"], actions: ["render-md"], evidence_key: "")
expect(office_llm_catalog_validate([malformed])).to_equal("catalog error: app 'Markdown' has empty evidence key")
```

</details>

#### rejects empty feature lists

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val malformed = OfficeLlmFeature(app_name: "Markdown", component: "markdown", owner_module: "app.office.md_wysiwyg", features: [], actions: ["render-md"], evidence_key: "md_wysiwyg_spec")
expect(office_llm_catalog_validate([malformed])).to_equal("catalog error: app 'Markdown' has no features")
```

</details>

#### rejects duplicate actions across apps

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(office_llm_catalog_validate([_row("Markdown", ["render-md"]), _row("Writer", ["render-md"])])).to_equal("catalog error: duplicate action 'render-md'")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/ide_office_plugin_suite.md](doc/03_plan/sys_test/ide_office_plugin_suite.md)
- **Design:** [doc/07_guide/app/ide_office_plugin_suite.md](doc/07_guide/app/ide_office_plugin_suite.md)


</details>
