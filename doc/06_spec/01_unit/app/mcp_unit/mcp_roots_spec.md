# Mcp Roots Specification

> <details>

<!-- sdn-diagram:id=mcp_roots_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_roots_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_roots_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_roots_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Roots Specification

## Scenarios

### MCP Roots Response

<details>
<summary>Advanced: builds roots list response</summary>

#### builds roots list response _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = jo2(jp("uri", js("file:///home/user/project")), jp("name", js("project")))
val result = jo1(jp("roots", "[" + root + "]"))
val response = make_result_response("1", result)
expect(response.contains("\"roots\"")).to_equal(true)
expect(response.contains("file:///home/user/project")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: includes root name</summary>

#### includes root name _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val root = jo2(jp("uri", js("file:///project")), jp("name", js("my-project")))
val name = extract_json_string(root, "name")
expect(name).to_equal("my-project")
```

</details>


</details>

<details>
<summary>Advanced: handles empty roots list</summary>

#### handles empty roots list _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val result = jo1(jp("roots", "[]"))
val response = make_result_response("1", result)
expect(response.contains("\"roots\":[]")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_roots_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Roots Response

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 3 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
