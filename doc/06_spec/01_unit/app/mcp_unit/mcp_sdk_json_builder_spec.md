# Mcp Sdk Json Builder Specification

> <details>

<!-- sdn-diagram:id=mcp_sdk_json_builder_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=mcp_sdk_json_builder_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

mcp_sdk_json_builder_spec -> app
mcp_sdk_json_builder_spec -> std
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=mcp_sdk_json_builder_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 26 | 26 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Sdk Json Builder Specification

## Scenarios

### jo1-jo5 output structure (main_lazy_json)

#### jo1 produces well-formed single-pair object

#### wraps pair in braces

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val pair = jp("k", js("v"))
val got = jo1(pair)
expect(got).to_equal(LB() + pair + RB())
```

</details>

#### round-trips string field via extract_json_string

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val built = jo1(jp("name", js("alice")))
val extracted = extract_json_string(built, "name")
expect(extracted).to_equal("alice")
```

</details>

#### jo2 places comma between pairs

#### produces correct structure

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val p1 = jp("a", js("1"))
val p2 = jp("b", js("2"))
val got = jo2(p1, p2)
expect(got).to_equal(LB() + p1 + "," + p2 + RB())
```

</details>

#### round-trips both fields

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val built = jo2(jp("x", js("foo")), jp("y", js("bar")))
expect(extract_json_string(built, "x")).to_equal("foo")
expect(extract_json_string(built, "y")).to_equal("bar")
```

</details>

#### jo3 round-trips three fields

#### all three fields extractable

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val built = jo3(jp("a", js("1")), jp("b", js("2")), jp("c", js("3")))
expect(extract_json_string(built, "a")).to_equal("1")
expect(extract_json_string(built, "b")).to_equal("2")
expect(extract_json_string(built, "c")).to_equal("3")
```

</details>

#### jo4 round-trips four fields

#### all four fields extractable

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val built = jo4(jp("w", js("1")), jp("x", js("2")), jp("y", js("3")), jp("z", js("4")))
expect(extract_json_string(built, "w")).to_equal("1")
expect(extract_json_string(built, "x")).to_equal("2")
expect(extract_json_string(built, "y")).to_equal("3")
expect(extract_json_string(built, "z")).to_equal("4")
```

</details>

### escape_json round-trips via js/extract_json_string

#### special characters survive encode-decode

#### encodes newline in escaped JSON form

<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# extract_json_string returns the raw JSON-escaped form (no unescape step);
# verify the encoded form is present and newlines are eliminated.
val raw = "line1\nline2"
val built = jo1(jp("body", js(raw)))
val got = extract_json_string(built, "body")
# The extracted value is the JSON-escaped content (backslash-n, not real newline)
expect(got.contains("\n")).to_equal(false)
```

</details>

#### encodes tab in escaped JSON form

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val raw = "col1\tcol2"
val built = jo1(jp("tsv", js(raw)))
val got = extract_json_string(built, "tsv")
expect(got.contains("\t")).to_equal(false)
```

</details>

#### escape_json removes raw newlines

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("a\nb")
expect(escaped.contains("\n")).to_equal(false)
```

</details>

#### escape_json removes raw tabs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("a\tb")
expect(escaped.contains("\t")).to_equal(false)
```

</details>

#### escape_json preserves plain strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val escaped = escape_json("hello world")
expect(escaped).to_equal("hello world")
```

</details>

### first_n_chars uses native substring

#### boundary cases

#### returns first n chars

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_n_chars("hello", 3)).to_equal("hel")
```

</details>

#### returns whole string when n >= len

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_n_chars("abc", 10)).to_equal("abc")
```

</details>

#### returns empty string for n=0

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_n_chars("hello", 0)).to_equal("")
```

</details>

#### handles single-char string

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(first_n_chars("x", 1)).to_equal("x")
```

</details>

### _char_at guards invalid indexes

#### returns empty text for negative index

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_char_at("abc", -1)).to_equal("")
```

</details>

#### returns empty text for past-end index

<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(_char_at("abc", 3)).to_equal("")
```

</details>

### make_tool_result and make_tool_error JSON structure

#### make_tool_result output shape

#### contains content key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_tool_result("1", "hello world")
expect(r.contains("content")).to_equal(true)
```

</details>

#### contains structuredContent key

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_tool_result("1", "hello world")
expect(r.contains("structuredContent")).to_equal(true)
```

</details>

#### is well-formed JSON object

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_tool_result("2", "data")
expect(r.starts_with(LB())).to_equal(true)
expect(r.ends_with(RB())).to_equal(true)
```

</details>

#### make_tool_error output shape

#### contains isError

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_tool_error("1", -1, "boom")
expect(r.contains("isError")).to_equal(true)
```

</details>

#### isError value is true

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_tool_error("1", -1, "boom")
expect(r.contains("true")).to_equal(true)
```

</details>

#### contains the error message text

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = make_tool_error("1", -1, "something went wrong")
expect(r.contains("something went wrong")).to_equal(true)
```

</details>

### JSON-RPC builders (mcp_sdk.core.jsonrpc, rewritten)

#### jsonrpc_request builds the exact envelope

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = jsonrpc_request("7", "tools/list", "42")
val interior = "\"jsonrpc\":\"2.0\",\"id\":7,\"method\":\"tools/list\",\"params\":42"
expect(r.contains(interior)).to_equal(true)
expect(r.len()).to_equal(interior.len() + 2)
```

</details>

#### jsonrpc_notification builds the exact envelope

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = jsonrpc_notification("initialized", "1")
val interior = "\"jsonrpc\":\"2.0\",\"method\":\"initialized\",\"params\":1"
expect(r.contains(interior)).to_equal(true)
expect(r.len()).to_equal(interior.len() + 2)
```

</details>

#### jsonrpc_error_with_data nests the error object exactly

<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val r = jsonrpc_error_with_data("3", -32600, "bad request", "9")
val head_interior = "\"jsonrpc\":\"2.0\",\"id\":3,\"error\":"
val err_interior = "\"code\":-32600,\"message\":\"bad request\",\"data\":9"
expect(r.contains(head_interior)).to_equal(true)
expect(r.contains(err_interior)).to_equal(true)
expect(r.len()).to_equal(head_interior.len() + err_interior.len() + 4)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/mcp_unit/mcp_sdk_json_builder_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering:
- jo1-jo5 output structure (main_lazy_json)
- escape_json round-trips via js/extract_json_string
- first_n_chars uses native substring
- _char_at guards invalid indexes
- make_tool_result and make_tool_error JSON structure
- JSON-RPC builders (mcp_sdk.core.jsonrpc, rewritten)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 26 |
| Active scenarios | 26 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
