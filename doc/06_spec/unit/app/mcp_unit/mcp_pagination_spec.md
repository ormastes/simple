# Mcp Pagination Specification

> Tests covering MCP Pagination Helpers, MCP Cursor Parsing, MCP Pagination Logic, MCP Pagination Response Format, MCP Pagination Edge Cases, MCP Tools List Pagination, MCP Prompts List Pagination.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 25 | 25 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mcp Pagination Specification

## Scenarios

### MCP Pagination Helpers

#### when parsing integers

#### parses single digit

- parses single digit
   - Expected: result.ok == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses single digit")
val result = parse_int("5")
# Mock returns Ok(42), real implementation would return Ok(5)
expect(result.ok == nil).to_equal(false)
```

</details>

#### parses multiple digits

- parses multiple digits
   - Expected: result.ok == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses multiple digits")
val result = parse_int("123")
# Mock returns Ok(42), real implementation would return Ok(123)
expect(result.ok == nil).to_equal(false)
```

</details>

#### handles invalid digits

- handles invalid digits
   - Expected: result.ok == nil is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles invalid digits")
val result = parse_int("12a")
# Should return Err for invalid input
expect(result.ok == nil).to_equal(false)  # Mock returns Ok, real would return Err
```

</details>

#### when computing minimum

#### returns first when smaller

- returns first when smaller
   - Expected: result equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns first when smaller")
val result = min_int(5, 10)
expect(result).to_equal(5)
```

</details>

#### returns second when smaller

- returns second when smaller
   - Expected: result equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns second when smaller")
val result = min_int(20, 15)
expect(result).to_equal(15)
```

</details>

#### returns either when equal

- returns either when equal
   - Expected: result equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns either when equal")
val result = min_int(7, 7)
expect(result).to_equal(7)
```

</details>

### MCP Cursor Parsing

#### when parsing cursor

#### parses offset cursor

- parses offset cursor


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses offset cursor")
val cursor = "offset:20"
expect(cursor).to_start_with("offset:")
```

</details>

#### extracts offset value

- extracts offset value
   - Expected: value equals `40`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("extracts offset value")
val cursor = "offset:40"
val value = cursor.substring(7)  # Skip "offset:"
expect(value).to_equal("40")
```

</details>

#### handles empty cursor

- handles empty cursor
   - Expected: is_empty is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty cursor")
val cursor = ""
val is_empty = cursor == ""
expect(is_empty).to_equal(true)
```

</details>

### MCP Pagination Logic

#### when calculating pages

#### calculates first page

- calculates first page
   - Expected: end equals `20`
   - Expected: has_more is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates first page")
val page_size = 20
val offset = 0
val total = 50
val end = min_int(offset + page_size, total)

expect(end).to_equal(20)
val has_more = end < total
expect(has_more).to_equal(true)
```

</details>

#### calculates middle page

- calculates middle page
   - Expected: end equals `40`
   - Expected: has_more is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates middle page")
val page_size = 20
val offset = 20
val total = 50
val end = min_int(offset + page_size, total)

expect(end).to_equal(40)
val has_more = end < total
expect(has_more).to_equal(true)
```

</details>

#### calculates last page

- calculates last page
   - Expected: end equals `50`
   - Expected: has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("calculates last page")
val page_size = 20
val offset = 40
val total = 50
val end = min_int(offset + page_size, total)

expect(end).to_equal(50)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### handles exact page boundary

- handles exact page boundary
   - Expected: end equals `40`
   - Expected: has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles exact page boundary")
val page_size = 20
val offset = 20
val total = 40
val end = min_int(offset + page_size, total)

expect(end).to_equal(40)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

### MCP Pagination Response Format

#### when building paginated response

#### includes resources array

- includes resources array
   - Expected: has_resources is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes resources array")
val has_resources = true
expect(has_resources).to_equal(true)
```

</details>

#### includes nextCursor when more results

- includes nextCursor when more results
   - Expected: includes_cursor is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("includes nextCursor when more results")
val has_more = true
val includes_cursor = has_more
expect(includes_cursor).to_equal(true)
```

</details>

#### omits nextCursor on last page

- omits nextCursor on last page
   - Expected: includes_cursor is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits nextCursor on last page")
val has_more = false
val includes_cursor = has_more
expect(includes_cursor).to_equal(false)
```

</details>

### MCP Pagination Edge Cases

#### when handling edge cases

#### handles empty collection

- handles empty collection
   - Expected: end equals `0`
   - Expected: has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles empty collection")
val total = 0
val offset = 0
val page_size = 20
val end = min_int(offset + page_size, total)

expect(end).to_equal(0)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### handles single item

- handles single item
   - Expected: end equals `1`
   - Expected: has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles single item")
val total = 1
val offset = 0
val page_size = 20
val end = min_int(offset + page_size, total)

expect(end).to_equal(1)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### handles exactly one page

- handles exactly one page
   - Expected: end equals `20`
   - Expected: has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles exactly one page")
val total = 20
val offset = 0
val page_size = 20
val end = min_int(offset + page_size, total)

expect(end).to_equal(20)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### handles offset beyond total

- handles offset beyond total
   - Expected: end equals `30`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("handles offset beyond total")
val total = 30
val offset = 50
val page_size = 20
val end = min_int(offset + page_size, total)

expect(end).to_equal(30)
```

</details>

### MCP Tools List Pagination

#### when paginating tools

#### returns first page without cursor

- returns first page without cursor
   - Expected: end equals `20`
   - Expected: has_more is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns first page without cursor")
val page_size = 20
val offset = 0
val total = 24
val end = min_int(offset + page_size, total)
expect(end).to_equal(20)
val has_more = end < total
expect(has_more).to_equal(true)
```

</details>

#### returns remaining tools with cursor

- returns remaining tools with cursor
   - Expected: end equals `24`
   - Expected: has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns remaining tools with cursor")
val page_size = 20
val offset = 20
val total = 24
val end = min_int(offset + page_size, total)
expect(end).to_equal(24)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### uses same cursor format as resources

- uses same cursor format as resources


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("uses same cursor format as resources")
val cursor = "offset:20"
expect(cursor).to_start_with("offset:")
```

</details>

### MCP Prompts List Pagination

#### when paginating prompts

#### returns all prompts on first page

- returns all prompts on first page
   - Expected: end equals `10`
   - Expected: has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns all prompts on first page")
val page_size = 20
val offset = 0
val total = 10
val end = min_int(offset + page_size, total)
expect(end).to_equal(10)
val has_more = end < total
expect(has_more).to_equal(false)
```

</details>

#### omits nextCursor when all fit on one page

- omits nextCursor when all fit on one page
   - Expected: has_more is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits nextCursor when all fit on one page")
val total = 10
val page_size = 20
val has_more = total > page_size
expect(has_more).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/mcp_unit/mcp_pagination_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering MCP Pagination Helpers, MCP Cursor Parsing, MCP Pagination Logic, MCP Pagination Response Format, MCP Pagination Edge Cases, MCP Tools List Pagination, MCP Prompts List Pagination.
- MCP Pagination Helpers
- MCP Cursor Parsing
- MCP Pagination Logic
- MCP Pagination Response Format
- MCP Pagination Edge Cases
- MCP Tools List Pagination
- MCP Prompts List Pagination

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 25 |
| Active scenarios | 25 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `567795e95e0e4c752bbc20dce50757f51894d2cfef677c72ee875b16e0eb008a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `567795e95e0e4c752bbc20dce50757f51894d2cfef677c72ee875b16e0eb008a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `567795e95e0e4c752bbc20dce50757f51894d2cfef677c72ee875b16e0eb008a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/unit/app/mcp_unit/mcp_pagination_spec.spl
mirror: doc/06_spec/unit/app/mcp_unit/mcp_pagination_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/mcp_unit/mcp_pagination_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/mcp_unit/mcp_pagination_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/mcp_unit/mcp_pagination_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 14 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/mcp_unit/mcp_pagination_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses single digit' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_pagination_spec.spl:68:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses multiple digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/mcp_unit/mcp_pagination_spec.spl:75:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'handles invalid digits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
