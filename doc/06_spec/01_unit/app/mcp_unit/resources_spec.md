# Resources Specification

> <details>

<!-- sdn-diagram:id=resources_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=resources_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

resources_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=resources_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Resources Specification

## Scenarios

### Resources

#### defines MCP resource data types and manager cache state

<details>
<summary>Executable SPipe</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/mcp/resources.spl")

expect(src).to_contain("struct ResourceInfo:")
expect(src).to_contain("uri: text")
expect(src).to_contain("mime_type: Option<text>")
expect(src).to_contain("struct ResourceTemplate:")
expect(src).to_contain("uri_template: text")
expect(src).to_contain("struct ResourceContent:")
expect(src).to_contain("class ResourceManager:")
expect(src).to_contain("resources_cache: Option<[ResourceInfo]>")
expect(src).to_contain("static fn create(project_root: text) -> ResourceManager:")
```

</details>

#### defines resource listing and built-in resource families

<details>
<summary>Executable SPipe</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val src = rt_file_read_text("src/lib/nogc_async_mut/mcp/resources.spl")

expect(src).to_contain("fn list_resources() -> [ResourceInfo]:")
expect(src).to_contain("project:///info")
expect(src).to_contain("file:///*")
expect(src).to_contain("symbol:///*")
expect(src).to_contain("type:///*")
expect(src).to_contain("docs:///*")
expect(src).to_contain("tree:///*")
expect(src).to_contain("bugdb:///all")
expect(src).to_contain("featuredb:///all")
expect(src).to_contain("testdb:///runs")
expect(src).to_contain("debuglog:///tree")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/resources_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Resources

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
