# Mcp Completion Specification

> <details>

<!-- sdn-diagram:id=mcp_completion_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_completion_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_completion_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_completion_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Completion Specification

## Scenarios

### MCP Completion Request

#### when requesting prompt completions

#### accepts completion request with ref/prompt

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = jo2(jp("type", js("ref/prompt")), jp("name", js("code-review")))
val arg = jo2(jp("name", js("language")), jp("value", js("py")))
val params = jo2(jp("ref", ref), jp("argument", arg))
expect(params.contains("ref/prompt")).to_equal(true)
expect(params.contains("language")).to_equal(true)
```

</details>

#### handles ref/prompt reference type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = jo1(jp("type", js("ref/prompt")))
val ref_type = extract_json_string(ref, "type")
expect(ref_type).to_equal("ref/prompt")
```

</details>

#### builds completion params with argument value

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val arg = jo2(jp("name", js("language")), jp("value", js("py")))
val arg_value = extract_json_string(arg, "value")
expect(arg_value).to_equal("py")
```

</details>

#### when requesting resource completions

#### handles ref/resource reference type

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = jo2(jp("type", js("ref/resource")), jp("uri", js("file:///*")))
val ref_type = extract_json_string(ref, "type")
expect(ref_type).to_equal("ref/resource")
```

</details>

#### includes uri in resource ref

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val ref = jo2(jp("type", js("ref/resource")), jp("uri", js("bugdb:///*")))
expect(ref.contains("bugdb://")).to_equal(true)
```

</details>

### MCP Completion Response Format

#### when building completion response

#### includes values array

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val values = "[" + js("python") + "," + js("perl") + "]"
val completion = jo3(jp("values", values), jp("total", "2"), jp("hasMore", "false"))
val result = jo1(jp("completion", completion))
val response = make_result_response("1", result)
expect(response.contains("values")).to_equal(true)
expect(response.contains("python")).to_equal(true)
```

</details>

#### includes total count

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completion = jo3(jp("values", "[]"), jp("total", "5"), jp("hasMore", "false"))
val result = jo1(jp("completion", completion))
val response = make_result_response("1", result)
expect(response.contains("\"total\":5")).to_equal(true)
```

</details>

#### includes hasMore flag

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completion = jo3(jp("values", "[]"), jp("total", "150"), jp("hasMore", "true"))
val result = jo1(jp("completion", completion))
val response = make_result_response("1", result)
expect(response.contains("\"hasMore\":true")).to_equal(true)
```

</details>

#### values array has max 100 items

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val max_items = 100
val actual_items = 5
expect(actual_items <= max_items).to_equal(true)
```

</details>

#### when no completions available

#### returns empty values array

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completion = jo3(jp("values", "[]"), jp("total", "0"), jp("hasMore", "false"))
val result = jo1(jp("completion", completion))
val response = make_result_response("1", result)
expect(response.contains("\"values\":[]")).to_equal(true)
```

</details>

#### returns zero total

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completion = jo3(jp("values", "[]"), jp("total", "0"), jp("hasMore", "false"))
expect(completion.contains("\"total\":0")).to_equal(true)
```

</details>

#### returns hasMore as false

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val completion = jo3(jp("values", "[]"), jp("total", "0"), jp("hasMore", "false"))
expect(completion.contains("\"hasMore\":false")).to_equal(true)
```

</details>

### MCP Context-Aware Completions

#### when context arguments provided

#### accepts context parameter in params

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context_arg = jo1(jp("language", js("python")))
val arg = jo2(jp("name", js("style")), jp("value", js("d")))
val params = jo3(jp("ref", jo1(jp("type", js("ref/prompt")))), jp("argument", arg), jp("context", context_arg))
expect(params.contains("context")).to_equal(true)
expect(params.contains("python")).to_equal(true)
```

</details>

#### extracts context values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val context_arg = jo1(jp("language", js("python")))
val lang = extract_json_string(context_arg, "language")
expect(lang).to_equal("python")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_completion_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- MCP Completion Request
- MCP Completion Response Format
- MCP Context-Aware Completions

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
