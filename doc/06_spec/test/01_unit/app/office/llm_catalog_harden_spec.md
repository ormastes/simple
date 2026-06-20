# llm_catalog_harden_spec

> Verifies that the LLM-facing Office catalog rejects malformed app/action rows before agents use the metadata as an automation surface. The catalog is the small boundary between advertised Office capabilities and agent-dispatchable actions for Markdown, Writer, Calc, Impress, Draw, Designer, Base, Math, Mail, Planner, and Counter.

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
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# llm_catalog_harden_spec

Verifies that the LLM-facing Office catalog rejects malformed app/action rows before agents use the metadata as an automation surface. The catalog is the small boundary between advertised Office capabilities and agent-dispatchable actions for Markdown, Writer, Calc, Impress, Draw, Designer, Base, Math, Mail, Planner, and Counter.

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
actions for Markdown, Writer, Calc, Impress, Draw, Designer, Base, Math, Mail,
Planner, and Counter.

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

#### documents an input schema for every shipped action

- missing push
   - Expected: missing.join(",") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var missing: [text] = []
for row in office_llm_feature_catalog():
    for action in row.actions:
        if office_llm_action_input_schema(action) == "":
            missing.push(action)
expect(missing.join(",")).to_equal("")
```

</details>

#### documents compact schemas for high-risk edit actions

<details>
<summary>Executable SSpec</summary>

Runnable source: 39 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(office_llm_action_input_schema("ui-layout-edit")).to_contain("node_id|expected_x|expected_y")
expect(office_llm_action_input_schema("render-ui-html-with-selection")).to_contain("select|node_id")
expect(office_llm_action_input_schema("sdd-document-summary")).to_equal("sdd_source")
expect(office_llm_action_input_schema("render-sdd-html-with-selection")).to_contain("select|node_id|edge_index")
expect(office_llm_action_input_schema("sdd-style-extends-read")).to_equal("css|key\\nsdd_source")
expect(office_llm_action_input_schema("sdd-style-target-read")).to_equal("css|key\\nsdd_source")
expect(office_llm_action_input_schema("sdd-style-value-read")).to_equal("css|key\\nsdd_source")
expect(office_llm_action_input_schema("sdd-style-resolved-read")).to_equal("css|target\\nsdd_source")
expect(office_llm_action_input_schema("sdd-style-resolved-value-read")).to_equal("css|target|key\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-label-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-style-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-parent-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-child-bounds-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-child-count-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-geometry-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-shape-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-layer-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-order-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-node-role-read")).to_equal("node_id\\nsdd_source")
expect(office_llm_action_input_schema("sdd-edge-label-read")).to_equal("edge_index\\nsdd_source")
expect(office_llm_action_input_schema("sdd-edge-label-point-read")).to_equal("edge_index\\nsdd_source")
expect(office_llm_action_input_schema("sdd-edge-style-read")).to_equal("edge_index\\nsdd_source")
expect(office_llm_action_input_schema("sdd-edge-kind-read")).to_equal("edge_index\\nsdd_source")
expect(office_llm_action_input_schema("sdd-edge-route-read")).to_equal("edge_index\\nsdd_source")
expect(office_llm_action_input_schema("sdd-edge-path-read")).to_equal("edge_index\\nsdd_source")
expect(office_llm_action_input_schema("sdd-edge-segments-read")).to_equal("edge_index\\nsdd_source")
expect(office_llm_action_input_schema("sdd-edge-endpoints-read")).to_equal("edge_index\\nsdd_source")
expect(office_llm_action_input_schema("reroute-sdd-connector")).to_contain("edge_index|route|waypoints")
expect(office_llm_action_input_schema("db-edit")).to_contain("update-where|match_col")
expect(office_llm_action_input_schema("base-table-summary")).to_contain("columns")
expect(office_llm_action_input_schema("md-edit")).to_contain("line_no|expected_source|new_source")
expect(office_llm_action_input_schema("writer-markdown-stats")).to_equal("markdown_source")
expect(office_llm_action_input_schema("writer-markdown-search")).to_equal("query\\nmarkdown_source")
expect(office_llm_action_input_schema("writer-markdown-range")).to_equal("start|count\\nmarkdown_source")
expect(office_llm_action_input_schema("writer-markdown-replace")).to_equal("query|replacement\\nmarkdown_source")
expect(office_llm_action_input_schema("writer-markdown-insert")).to_equal("line|text\\nmarkdown_source")
expect(office_llm_action_input_schema("writer-markdown-delete")).to_equal("line\\nmarkdown_source")
expect(office_llm_action_input_schema("writer-markdown-outline")).to_equal("markdown_source")
expect(office_llm_action_input_schema("ppt-markdown-outline")).to_equal("markdown_source")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


## Related Documentation

- **Plan:** [doc/03_plan/sys_test/ide_office_plugin_suite.md](doc/03_plan/sys_test/ide_office_plugin_suite.md)
- **Design:** [doc/07_guide/app/ide_office_plugin_suite.md](doc/07_guide/app/ide_office_plugin_suite.md)


</details>
