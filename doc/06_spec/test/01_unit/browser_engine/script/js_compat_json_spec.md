# Js Compat Json Specification

> <details>

<!-- sdn-diagram:id=js_compat_json_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=js_compat_json_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

js_compat_json_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=js_compat_json_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Js Compat Json Specification

## Scenarios

### Browser script JS compatibility JSON

#### parses quoted JSON strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_json_parse("\"hello\"")).to_equal("hello")
expect(js_json_parse("\"a\\nb\"")).to_equal("a\nb")
```

</details>

#### canonicalizes object and array JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val parsed = js_json_parse(" { \"name\" : \"Ada\", \"scores\" : [1, true, null] } ")
expect(parsed).to_equal("{\"name\":\"Ada\",\"scores\":[1,true,null]}")
```

</details>

#### rejects trailing or malformed JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_json_parse("true; alert(1)")).to_equal("")
expect(js_json_parse("{\"a\":}")).to_equal("")
```

</details>

#### stringifies text with JSON escaping

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js_json_stringify("a\nb\t\"c\"")).to_equal("\"a\\nb\\t\\\"c\\\"\"")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/browser_engine/script/js_compat_json_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- Browser script JS compatibility JSON

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
