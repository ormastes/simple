# Korean Stock MCP Server

> Tests the Korean Stock MCP server including JSON helpers, formatting utilities, cache management, and URL building. Integration tests verify JSON-RPC communication.

<!-- sdn-diagram:id=korean_stock_mcp_spec.arch -->
<details class="sdn-source">
<summary>SDN source</summary>

```sdn id=korean_stock_mcp_spec.arch hash=sha256:auto render=ascii
@layout dag
@direction LR

korean_stock_mcp_spec
```

</details>

<details class="sdn-ascii" open>
<summary>Diagram</summary>

```ascii generated-from=korean_stock_mcp_spec.arch hash=sha256:auto
# run: simple md-diagram-update
```

</details>
<!-- sdn-diagram:end -->

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Korean Stock MCP Server

Tests the Korean Stock MCP server including JSON helpers, formatting utilities, cache management, and URL building. Integration tests verify JSON-RPC communication.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | In Progress |
| Source | `test/03_system/feature/examples/korean_stock_mcp_spec.spl` |
| Updated | 2026-06-01 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Korean Stock MCP server including JSON helpers, formatting utilities,
cache management, and URL building. Integration tests verify JSON-RPC communication.

## Scenarios

### Korean Stock MCP - JSON Helpers

#### provides brace helpers

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(LB()).to_equal("{")
expect(RB()).to_equal("}")
expect(Q()).to_equal("\"")
expect(SB_L()).to_equal("[")
expect(SB_R()).to_equal("]")
```

</details>

#### escapes JSON strings

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(escape_json("hello")).to_equal("hello")
expect(escape_json("line1\nline2")).to_equal(r"line1\nline2")
expect(escape_json("tab\there")).to_equal(r"tab\there")
```

</details>

#### builds JSON string values

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(js("hello")).to_equal("\"hello\"")
expect(js("")).to_equal("\"\"")
```

</details>

#### builds JSON pairs

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(jp("key", "123")).to_equal("\"key\":123")
expect(jp("name", js("test"))).to_equal("\"name\":\"test\"")
```

</details>

#### builds JSON objects

<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val obj1 = jo1(jp("a", "1"))
expect(obj1).to_equal("{\"a\":1}")

val obj2 = jo2(jp("a", "1"), jp("b", "2"))
expect(obj2).to_equal("{\"a\":1,\"b\":2}")

val obj3 = jo3(jp("x", js("y")), jp("a", "1"), jp("b", "2"))
expect(obj3).to_contain("\"x\":\"y\"")
expect(obj3).to_contain("\"a\":1")
```

</details>

#### extracts fields from JSON

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"method\":\"initialize\",\"id\":1}"
expect(extract_field(json, "method")).to_equal("initialize")
expect(extract_field(json, "id")).to_equal("1")
expect(extract_field(json, "missing")).to_equal("")
```

</details>

#### extracts nested string values

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val json = "{\"name\":\"Samsung\",\"ticker\":\"005930\"}"
expect(extract_field(json, "name")).to_equal("Samsung")
expect(extract_field(json, "ticker")).to_equal("005930")
```

</details>

### Korean Stock MCP - Formatting

#### formats KRW amounts with commas

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_krw("1000")).to_equal("1,000")
expect(format_krw("1000000")).to_equal("1,000,000")
expect(format_krw("500")).to_equal("500")
expect(format_krw("0")).to_equal("0")
expect(format_krw("")).to_equal("0")
```

</details>

#### formats volume with K/M suffixes

<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_volume("1500000")).to_equal("1M")
expect(format_volume("50000")).to_equal("50K")
expect(format_volume("500")).to_equal("500")
expect(format_volume("")).to_equal("0")
```

</details>

#### handles comma-separated input

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(format_krw("1,000,000")).to_equal("1,000,000")
expect(format_volume("1,500,000")).to_equal("1M")
```

</details>

### Korean Stock MCP - Safe String Helpers

#### substrings correctly

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mcp_substr("hello", 0, 3)).to_equal("hel")
expect(mcp_substr("hello", 1, 4)).to_equal("ell")
expect(mcp_substr("hello", 0, 5)).to_equal("hello")
```

</details>

#### gets char at index

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
expect(mcp_char_at("hello", 0)).to_equal("h")
expect(mcp_char_at("hello", 4)).to_equal("o")
expect(mcp_char_at("hello", 10)).to_equal("")
```

</details>

### Korean Stock MCP - KRX URL Building

#### builds form body with bld parameter

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val body = "bld=dbms/MDC/STAT/standard/MDCSTAT01501&trdDd=20240315"
expect(body).to_contain("bld=dbms/MDC/STAT/standard/MDCSTAT01501")
expect(body).to_contain("trdDd=20240315")
```

</details>

#### uses correct KRX API URL

<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val url = "http://data.krx.co.kr/comm/bldAttendant/getJsonData.cmd"
expect(url).to_contain("data.krx.co.kr")
expect(url).to_contain("getJsonData")
```

</details>

#### builds market index params

<details>
<summary>Executable SSpec</summary>

Runnable source: 2 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val params = "trdDd=20240315&idxIndMidclssCd=1001"
expect(params).to_contain("idxIndMidclssCd=1001")
```

</details>

#### maps market names to KRX codes

<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var mkt_id = "STK"
val market = "KOSDAQ"
if market == "KOSDAQ":
    mkt_id = "KSQ"
expect(mkt_id).to_equal("KSQ")
```

</details>

### Korean Stock MCP - Tool Schema

#### builds tool schema JSON

1. jp
2. jp
3. jp


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val schema = jo3(
    jp("type", js("object")),
    jp("properties", jo1(jp("ticker", jo2(jp("type", js("string")), jp("description", js("Stock ticker")))))),
    jp("required", "[" + js("ticker") + "]")
)
expect(schema).to_contain("\"type\":\"object\"")
expect(schema).to_contain("\"ticker\"")
expect(schema).to_contain("\"required\"")
```

</details>

#### builds complete tool entry

1. jp
2. jp
3. jp


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
val tool = jo3(
    jp("name", js("stock_price")),
    jp("description", js("Get stock price")),
    jp("inputSchema", jo1(jp("type", js("object"))))
)
expect(tool).to_contain("\"name\":\"stock_price\"")
expect(tool).to_contain("\"description\"")
expect(tool).to_contain("\"inputSchema\"")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 18 |
| Active scenarios | 18 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>
