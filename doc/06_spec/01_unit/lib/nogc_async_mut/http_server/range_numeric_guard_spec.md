# Range Numeric Guard Specification

> Tests covering nogc async http server range numeric guard.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Range Numeric Guard Specification

## Scenarios

### nogc async http server range numeric guard

#### parses range bounds through a parser that can actually fail

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses range bounds through a parser that can actually fail


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses range bounds through a parser that can actually fail")
val source = rt_file_read_text("src/lib/nogc_async_mut/http_server/utilities.spl") ?? ""

expect(source).to_contain("val parsed_start = try_parse_int(start_str)")
expect(source).to_contain("val parsed_end = try_parse_int(end_str)")
```

</details>

#### fails closed on a malformed bound instead of coercing it

- fails closed on a malformed bound instead of coercing it


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails closed on a malformed bound instead of coercing it")
val source = rt_file_read_text("src/lib/nogc_async_mut/http_server/utilities.spl") ?? ""

expect(source).to_contain("if parsed_start == nil:")
expect(source).to_contain("if parsed_end == nil:")
```

</details>

#### never reintroduces the coercing to_int spellings

- never reintroduces the coercing to_int spellings
   - Expected: source does not contain `start = start_str.to_int()`
   - Expected: source does not contain `end = end_str.to_int()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("never reintroduces the coercing to_int spellings")
val source = rt_file_read_text("src/lib/nogc_async_mut/http_server/utilities.spl") ?? ""

expect(source.contains("start = start_str.to_int()")).to_equal(false)
expect(source.contains("end = end_str.to_int()")).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc async http server range numeric guard.
- nogc async http server range numeric guard

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4c62fb3e1fdbb2ce24d93b429c51babba8064bcab4d9d90629e101625fd11c71`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4c62fb3e1fdbb2ce24d93b429c51babba8064bcab4d9d90629e101625fd11c71`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4c62fb3e1fdbb2ce24d93b429c51babba8064bcab4d9d90629e101625fd11c71`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **76/100**; effective score: **49/100**; blockers: **2**.

SSpec documentization score: 49/100
source: test/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.md (current)
findings: 7 blockers: 2
  narrative=100 structure=100 oracle=50
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=76; blocker cap makes effective=49
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.spl:1:1: blocker SSDOC-ORA-002 [oracle] (-50): scenario relies on source-text inspection as system evidence
  why: Source presence or self-created arithmetic does not demonstrate production behavior.
  improve: Observe runtime behavior or a stable generated artifact instead.
test/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses range bounds through a parser that can actually fail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'fails closed on a malformed bound instead of coercing it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/range_numeric_guard_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never reintroduces the coercing to_int spellings' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
