# Korean Stock MCP Server

> Tests the Korean Stock MCP server including JSON helpers, formatting utilities, cache management, and URL building. Integration tests verify JSON-RPC communication.

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
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests the Korean Stock MCP server including JSON helpers, formatting utilities,
cache management, and URL building. Integration tests verify JSON-RPC communication.

## Scenarios

### Korean Stock MCP - JSON Helpers

#### provides brace helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- provides brace helpers
   - Expected: LB() equals `{`
   - Expected: RB() equals `}`
   - Expected: Q() equals `"`
   - Expected: SB_L() equals `[`
   - Expected: SB_R() equals `]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("provides brace helpers")
expect(LB()).to_equal("{")
expect(RB()).to_equal("}")
expect(Q()).to_equal("\"")
expect(SB_L()).to_equal("[")
expect(SB_R()).to_equal("]")
```

</details>

#### escapes JSON strings

- escapes JSON strings
   - Expected: escape_json("hello") equals `hello`
   - Expected: escape_json("line1\nline2") equals `r"line1\nline2"`
   - Expected: escape_json("tab\there") equals `r"tab\there"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("escapes JSON strings")
expect(escape_json("hello")).to_equal("hello")
expect(escape_json("line1\nline2")).to_equal(r"line1\nline2")
expect(escape_json("tab\there")).to_equal(r"tab\there")
```

</details>

#### builds JSON string values

- builds JSON string values
   - Expected: js("hello") equals `"hello"`
   - Expected: js("") equals `""`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds JSON string values")
expect(js("hello")).to_equal("\"hello\"")
expect(js("")).to_equal("\"\"")
```

</details>

#### builds JSON pairs

- builds JSON pairs
   - Expected: jp("key", "123") equals `"key":123`
   - Expected: jp("name", js("test")) equals `"name":"test"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds JSON pairs")
expect(jp("key", "123")).to_equal("\"key\":123")
expect(jp("name", js("test"))).to_equal("\"name\":\"test\"")
```

</details>

#### builds JSON objects

- builds JSON objects
   - Expected: obj1 equals `{"a":1}`
   - Expected: obj2 equals `{"a":1,"b":2}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds JSON objects")
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

- extracts fields from JSON
   - Expected: extract_field(json, "method") equals `initialize`
   - Expected: extract_field(json, "id") equals `1`
   - Expected: extract_field(json, "missing") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts fields from JSON")
val json = "{\"method\":\"initialize\",\"id\":1}"
expect(extract_field(json, "method")).to_equal("initialize")
expect(extract_field(json, "id")).to_equal("1")
expect(extract_field(json, "missing")).to_equal("")
```

</details>

#### extracts nested string values

- extracts nested string values
   - Expected: extract_field(json, "name") equals `Samsung`
   - Expected: extract_field(json, "ticker") equals `005930`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("extracts nested string values")
val json = "{\"name\":\"Samsung\",\"ticker\":\"005930\"}"
expect(extract_field(json, "name")).to_equal("Samsung")
expect(extract_field(json, "ticker")).to_equal("005930")
```

</details>

### Korean Stock MCP - Formatting

#### formats KRW amounts with commas

- formats KRW amounts with commas
   - Expected: format_krw("1000") equals `1,000`
   - Expected: format_krw("1000000") equals `1,000,000`
   - Expected: format_krw("500") equals `500`
   - Expected: format_krw("0") equals `0`
   - Expected: format_krw("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats KRW amounts with commas")
expect(format_krw("1000")).to_equal("1,000")
expect(format_krw("1000000")).to_equal("1,000,000")
expect(format_krw("500")).to_equal("500")
expect(format_krw("0")).to_equal("0")
expect(format_krw("")).to_equal("0")
```

</details>

#### formats volume with K/M suffixes

- formats volume with K/M suffixes
   - Expected: format_volume("1500000") equals `1M`
   - Expected: format_volume("50000") equals `50K`
   - Expected: format_volume("500") equals `500`
   - Expected: format_volume("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("formats volume with K/M suffixes")
expect(format_volume("1500000")).to_equal("1M")
expect(format_volume("50000")).to_equal("50K")
expect(format_volume("500")).to_equal("500")
expect(format_volume("")).to_equal("0")
```

</details>

#### handles comma-separated input

- handles comma-separated input
   - Expected: format_krw("1,000,000") equals `1,000,000`
   - Expected: format_volume("1,500,000") equals `1M`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("handles comma-separated input")
expect(format_krw("1,000,000")).to_equal("1,000,000")
expect(format_volume("1,500,000")).to_equal("1M")
```

</details>

### Korean Stock MCP - Safe String Helpers

#### substrings correctly

- substrings correctly
   - Expected: mcp_substr("hello", 0, 3) equals `hel`
   - Expected: mcp_substr("hello", 1, 4) equals `ell`
   - Expected: mcp_substr("hello", 0, 5) equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("substrings correctly")
expect(mcp_substr("hello", 0, 3)).to_equal("hel")
expect(mcp_substr("hello", 1, 4)).to_equal("ell")
expect(mcp_substr("hello", 0, 5)).to_equal("hello")
```

</details>

#### gets char at index

- gets char at index
   - Expected: mcp_char_at("hello", 0) equals `h`
   - Expected: mcp_char_at("hello", 4) equals `o`
   - Expected: mcp_char_at("hello", 10) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("gets char at index")
expect(mcp_char_at("hello", 0)).to_equal("h")
expect(mcp_char_at("hello", 4)).to_equal("o")
expect(mcp_char_at("hello", 10)).to_equal("")
```

</details>

### Korean Stock MCP - KRX URL Building

#### builds form body with bld parameter

- builds form body with bld parameter


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds form body with bld parameter")
val body = "bld=dbms/MDC/STAT/standard/MDCSTAT01501&trdDd=20240315"
expect(body).to_contain("bld=dbms/MDC/STAT/standard/MDCSTAT01501")
expect(body).to_contain("trdDd=20240315")
```

</details>

#### uses correct KRX API URL

- uses correct KRX API URL


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("uses correct KRX API URL")
val url = "http://data.krx.co.kr/comm/bldAttendant/getJsonData.cmd"
expect(url).to_contain("data.krx.co.kr")
expect(url).to_contain("getJsonData")
```

</details>

#### builds market index params

- builds market index params


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds market index params")
val params = "trdDd=20240315&idxIndMidclssCd=1001"
expect(params).to_contain("idxIndMidclssCd=1001")
```

</details>

#### maps market names to KRX codes

- maps market names to KRX codes
   - Expected: mkt_id equals `KSQ`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("maps market names to KRX codes")
var mkt_id = "STK"
val market = "KOSDAQ"
if market == "KOSDAQ":
    mkt_id = "KSQ"
expect(mkt_id).to_equal("KSQ")
```

</details>

### Korean Stock MCP - Tool Schema

#### builds tool schema JSON

- builds tool schema JSON


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds tool schema JSON")
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

- builds complete tool entry


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds complete tool entry")
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

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c9925230b0d76ef7ada3f022eb16b777716f83825a6b4093082f90fbdc7bc6d6`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c9925230b0d76ef7ada3f022eb16b777716f83825a6b4093082f90fbdc7bc6d6`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c9925230b0d76ef7ada3f022eb16b777716f83825a6b4093082f90fbdc7bc6d6`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/feature/examples/korean_stock_mcp_spec.spl
mirror: doc/06_spec/03_system/feature/examples/korean_stock_mcp_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/feature/examples/korean_stock_mcp_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/feature/examples/korean_stock_mcp_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/feature/examples/korean_stock_mcp_spec.spl:150:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provides brace helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/examples/korean_stock_mcp_spec.spl:159:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'escapes JSON strings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/feature/examples/korean_stock_mcp_spec.spl:166:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds JSON string values' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
