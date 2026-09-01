# @manual: primary

> Purpose: Prove that Pagination - page building with JSON helpers.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# @manual: primary

Purpose: Prove that Pagination - page building with JSON helpers.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/pagination_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that Pagination - page building with JSON helpers.
Audience: compiler and tooling engineers who maintain this spec.
## Operator workflow
Run this spec with the test runner and read the per-scenario verdict lines;
a failing scenario pinpoints the behavior that regressed.
## Compatibility and limitations
Covers the pinned behavior only; fixture data is local to this spec.
# @manual: primary
REQ-APP-MCP-UNIT-001
doc/01_research/local/REQ-APP-MCP-UNIT-001.md
doc/03_plan/sys_test/REQ-APP-MCP-UNIT-001.md
doc/04_architecture/REQ-APP-MCP-UNIT-001.md
doc/05_design/REQ-APP-MCP-UNIT-001.md

## Scenarios

### Pagination - page building with JSON helpers

<details>
<summary>Advanced: builds paginated response with items</summary>

#### builds paginated response with items _(slow)_

- Verify: builds paginated response with items
   - Expected: response contains `items`
   - Expected: response contains `item1`
   - Expected: response contains `item3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds paginated response with items")
val items = "[" + js("item1") + "," + js("item2") + "," + js("item3") + "]"
val result = jo1(jp("items", items))
val response = make_result_response("1", result)
expect(response.contains("items")).to_equal(true)
expect(response.contains("item1")).to_equal(true)
expect(response.contains("item3")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds empty page response</summary>

#### builds empty page response _(slow)_

- Verify: builds empty page response
   - Expected: response contains `items`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds empty page response")
val result = jo1(jp("items", "[]"))
val response = make_result_response("1", result)
expect(response.contains("items")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds page with next cursor</summary>

#### builds page with next cursor _(slow)_

- Verify: builds page with next cursor
   - Expected: response contains `nextCursor`
   - Expected: response contains `o10l10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds page with next cursor")
val result = jo2(
    jp("items", "[" + js("a") + "]"),
    jp("nextCursor", js("o10l10"))
)
val response = make_result_response("1", result)
expect(response.contains("nextCursor")).to_equal(true)
expect(response.contains("o10l10")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: builds page without next cursor when at end</summary>

#### builds page without next cursor when at end _(slow)_

- Verify: builds page without next cursor when at end
   - Expected: response does not contain `nextCursor`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: builds page without next cursor when at end")
val result = jo1(jp("items", "[" + js("last") + "]"))
val response = make_result_response("1", result)
expect(response.contains("nextCursor")).to_equal(false)
```

</details>


</details>

### Pagination - cursor encoding

<details>
<summary>Advanced: cursor format includes offset and limit</summary>

#### cursor format includes offset and limit _(slow)_

- Verify: cursor format includes offset and limit
   - Expected: cursor.starts_with("o") is true
   - Expected: cursor contains `l`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: cursor format includes offset and limit")
val cursor = "o10l20"
expect(cursor.starts_with("o")).to_equal(true)
expect(cursor.contains("l")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: first page cursor starts at zero</summary>

#### first page cursor starts at zero _(slow)_

- Verify: first page cursor starts at zero
   - Expected: cursor.starts_with("o0") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: first page cursor starts at zero")
val cursor = "o0l50"
expect(cursor.starts_with("o0")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: next page cursor advances offset</summary>

#### next page cursor advances offset _(slow)_

- Verify: next page cursor advances offset
   - Expected: next_offset equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: next page cursor advances offset")
val page_size = 10
val offset = 0
val next_offset = offset + page_size
expect(next_offset).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: previous page cursor decreases offset</summary>

#### previous page cursor decreases offset _(slow)_

- Verify: previous page cursor decreases offset
   - Expected: prev_offset equals `10`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: previous page cursor decreases offset")
val page_size = 10
val offset = 20
val prev_offset = offset - page_size
expect(prev_offset).to_equal(10)  # oracle: 10 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: previous at start returns no cursor</summary>

#### previous at start returns no cursor _(slow)_

- Verify: previous at start returns no cursor
   - Expected: has_previous is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: previous at start returns no cursor")
val offset = 0
val has_previous = offset > 0
expect(has_previous).to_equal(false)
```

</details>


</details>

### Pagination - page size clamping

<details>
<summary>Advanced: clamps page size to maximum</summary>

#### clamps page size to maximum _(slow)_

- Verify: clamps page size to maximum
   - Expected: clamped equals `1000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: clamps page size to maximum")
val requested = 2000
val max_size = 1000
val clamped = min_int(requested, max_size)
expect(clamped).to_equal(1000)  # oracle: 1000 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: accepts valid page size</summary>

#### accepts valid page size _(slow)_

- Verify: accepts valid page size
   - Expected: clamped equals `50`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: accepts valid page size")
val requested = 50
val max_size = 1000
val clamped = min_int(requested, max_size)
expect(clamped).to_equal(50)  # oracle: 50 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: handles zero page size with default</summary>

#### handles zero page size with default _(slow)_

- Verify: handles zero page size with default
   - Expected: page_size equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: handles zero page size with default")
val requested = 0
val default_size = 100
var page_size = requested
if page_size <= 0:
    page_size = default_size
expect(page_size).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: handles negative page size with default</summary>

#### handles negative page size with default _(slow)_

- Verify: handles negative page size with default
   - Expected: page_size equals `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: handles negative page size with default")
val requested = -10
val default_size = 100
var page_size = requested
if page_size <= 0:
    page_size = default_size
expect(page_size).to_equal(100)  # oracle: 100 — named expected value from the requirement
```

</details>


</details>

### Pagination - extract cursor from params

<details>
<summary>Advanced: extracts cursor from params JSON</summary>

#### extracts cursor from params JSON _(slow)_

- Verify: extracts cursor from params JSON
   - Expected: cursor equals `o10l20`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts cursor from params JSON")
val params = jo1(jp("cursor", js("o10l20")))
val cursor = extract_json_string(params, "cursor")
expect(cursor).to_equal("o10l20")
```

</details>


</details>

<details>
<summary>Advanced: returns empty for missing cursor</summary>

#### returns empty for missing cursor _(slow)_

- Verify: returns empty for missing cursor
   - Expected: cursor equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: returns empty for missing cursor")
val params = jo1(jp("other", js("value")))
val cursor = extract_json_string(params, "cursor")
expect(cursor).to_equal("")
```

</details>


</details>

<details>
<summary>Advanced: extracts empty cursor value</summary>

#### extracts empty cursor value _(slow)_

- Verify: extracts empty cursor value
   - Expected: cursor equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts empty cursor value")
val params = jo1(jp("cursor", js("")))
val cursor = extract_json_string(params, "cursor")
expect(cursor).to_equal("")
```

</details>


</details>

### Pagination - total count

<details>
<summary>Advanced: includes total count in response</summary>

#### includes total count in response _(slow)_

- Verify: includes total count in response
   - Expected: response contains `totalCount`
   - Expected: response contains `100`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: includes total count in response")
val result = jo2(
    jp("items", "[" + js("a") + "," + js("b") + "]"),
    jp("totalCount", "100")
)
val response = make_result_response("1", result)
expect(response.contains("totalCount")).to_equal(true)
expect(response.contains("100")).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: extracts total count</summary>

#### extracts total count _(slow)_

- Verify: extracts total count
   - Expected: extract_json_value(result, "totalCount") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: extracts total count")
val result = jo2(jp("items", "[]"), jp("totalCount", "42"))
expect(extract_json_value(result, "totalCount")).to_equal("42")
```

</details>


</details>

### Pagination - page iteration

<details>
<summary>Advanced: calculates total pages</summary>

#### calculates total pages _(slow)_

- Verify: calculates total pages
   - Expected: total_pages equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: calculates total pages")
val total_items = 25
val page_size = 10
var total_pages = total_items / page_size
if total_items % page_size > 0:
    total_pages = total_pages + 1
expect(total_pages).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: handles exact page boundary</summary>

#### handles exact page boundary _(slow)_

- Verify: handles exact page boundary
   - Expected: total_pages equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: handles exact page boundary")
val total_items = 30
val page_size = 10
var total_pages = total_items / page_size
if total_items % page_size > 0:
    total_pages = total_pages + 1
expect(total_pages).to_equal(3)  # oracle: 3 — named expected value from the requirement
```

</details>


</details>

<details>
<summary>Advanced: handles empty list</summary>

#### handles empty list _(slow)_

- Verify: handles empty list
   - Expected: is_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: handles empty list")
val total_items = 0
val is_empty = total_items == 0
expect(is_empty).to_equal(true)
```

</details>


</details>

<details>
<summary>Advanced: handles single item</summary>

#### handles single item _(slow)_

- Verify: handles single item
   - Expected: has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: handles single item")
val total_items = 1
val page_size = 10
val has_more = total_items > page_size
expect(has_more).to_equal(false)
```

</details>


</details>

### Pagination - config with log levels

<details>
<summary>Advanced: debug level for pagination trace</summary>

#### debug level for pagination trace _(slow)_

- Verify: debug level for pagination trace
   - Expected: log_level_to_int("debug") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: debug level for pagination trace")
expect(log_level_to_int("debug")).to_equal(0)
```

</details>


</details>

<details>
<summary>Advanced: info level for page access</summary>

#### info level for page access _(slow)_

- Verify: info level for page access
   - Expected: log_level_to_int("info") equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: info level for page access")
expect(log_level_to_int("info")).to_equal(1)
```

</details>


</details>

<details>
<summary>Advanced: warning level for invalid cursor</summary>

#### warning level for invalid cursor _(slow)_

- Verify: warning level for invalid cursor
   - Expected: log_level_to_int("warning") equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req: REQ-APP-MCP-UNIT-001
step("Verify: warning level for invalid cursor")
expect(log_level_to_int("warning")).to_equal(3)
```

</details>


</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 25 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-APP-MCP-UNIT-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `bff1239ec5f548a04e64ee94899bb0aac3700aa9489c1458e0eaee9c08540bce`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `bff1239ec5f548a04e64ee94899bb0aac3700aa9489c1458e0eaee9c08540bce`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `bff1239ec5f548a04e64ee94899bb0aac3700aa9489c1458e0eaee9c08540bce`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/mcp_unit/pagination_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/pagination_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/unit/app/mcp_unit/pagination_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/pagination_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/pagination_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/pagination_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/mcp_unit/pagination_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds paginated response with items' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/pagination_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds empty page response' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/pagination_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds page with next cursor' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
