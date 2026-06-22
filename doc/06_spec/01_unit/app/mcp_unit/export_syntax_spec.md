# Export Syntax Specification

> <details>

<!-- sdn-diagram:id=export_syntax_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=export_syntax_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

export_syntax_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=export_syntax_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Export Syntax Specification

## Scenarios

### MCP module export syntax

<details>
<summary>Advanced: can import from mcp helpers</summary>

#### can import from mcp helpers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val response = make_result_response("1", jo1(jp("status", js("ok"))))
expect(response.contains("jsonrpc")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: can access protocol types from helpers</summary>

#### can access protocol types from helpers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val method_name = "initialize"
val req = jo1(jp("method", js(method_name)))
val extracted = extract_json_string(req, "method")
expect(extracted).to_equal("initialize")
```

</details>


</details>

<details>
<summary>Advanced: can build JSON objects</summary>

#### can build JSON objects _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj = jo2(jp("key1", js("value1")), jp("key2", js("value2")))
expect(obj.contains("key1")).to_equal(true)
expect(obj.contains("key2")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: can use LB and RB helpers</summary>

#### can use LB and RB helpers _(slow)_

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = LB() + jp("test", js("value")) + RB()
expect(json.contains("test")).to_equal(true)
```

</details>


</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/export_syntax_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP module export syntax

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 4 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
