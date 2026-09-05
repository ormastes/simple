# H1 Response Parse Specification

> Tests covering Browser HTTP/1 response parsing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# H1 Response Parse Specification

## Scenarios

### Browser HTTP/1 response parsing

#### parses a status-only response with no body

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a status-only response with no body
   - Expected: response.status equals `200`
   - Expected: response.body.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a status-only response with no body")
match parse_http_response_bytes(rt_text_to_bytes(
    "HTTP/1.1 200 OK\r\n\r\n"
)):
    Ok(response):
        expect(response.status).to_equal(200)
        expect(response.body.len()).to_equal(0)
    Err(error):
        fail("status-only response unexpectedly rejected: {error}")
```

</details>

#### parses a Content-Length delimited body

- parses a Content-Length delimited body
   - Expected: response.status equals `200`
   - Expected: response.body.len() equals `2`
   - Expected: response.body equals `[72u8, 73u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a Content-Length delimited body")
match parse_http_response_bytes(rt_text_to_bytes(
    "HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nHI"
)):
    Ok(response):
        expect(response.status).to_equal(200)
        expect(response.body.len()).to_equal(2)
        expect(response.body).to_equal([72u8, 73u8])
    Err(error):
        fail("Content-Length response unexpectedly rejected: {error}")
```

</details>

#### decodes a single-chunk Transfer-Encoding: chunked body

- decodes a single-chunk Transfer-Encoding: chunked body
   - Expected: response.status equals `200`
   - Expected: response.body.len() equals `2`
   - Expected: response.body equals `[72u8, 73u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes a single-chunk Transfer-Encoding: chunked body")
# Regression case: the chunked decode path used a `var [u8]`
# accumulator reassigned via `+`, which died under the Rust seed
# interpreter with "semantic: cannot convert array to int". Fixed by
# switching to per-byte `.push()` in parse_chunked_body_bytes.
match parse_http_response_bytes(rt_text_to_bytes(
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nHI\r\n0\r\n\r\n"
)):
    Ok(response):
        expect(response.status).to_equal(200)
        expect(response.body.len()).to_equal(2)
        expect(response.body).to_equal([72u8, 73u8])
    Err(error):
        fail("chunked response unexpectedly rejected: {error}")
```

</details>

#### concatenates multiple data chunks in order

- concatenates multiple data chunks in order
   - Expected: response.status equals `200`
   - Expected: response.body.len() equals `5`
   - Expected: response.body equals `[72u8, 73u8, 33u8, 33u8, 33u8]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("concatenates multiple data chunks in order")
match parse_http_response_bytes(rt_text_to_bytes(
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nHI\r\n3\r\n!!!\r\n0\r\n\r\n"
)):
    Ok(response):
        expect(response.status).to_equal(200)
        expect(response.body.len()).to_equal(5)
        expect(response.body).to_equal([72u8, 73u8, 33u8, 33u8, 33u8])
    Err(error):
        fail("multi-chunk response unexpectedly rejected: {error}")
```

</details>

#### rejects a chunk whose declared size exceeds the available data

- rejects a chunk whose declared size exceeds the available data


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a chunk whose declared size exceeds the available data")
expect(parse_http_response_bytes(rt_text_to_bytes(
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nHI\r\n0\r\n\r\n"
)).is_err()).to_equal(true)
```

</details>

#### rejects a chunked body missing the terminal zero-length chunk

- rejects a chunked body missing the terminal zero-length chunk


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a chunked body missing the terminal zero-length chunk")
expect(parse_http_response_bytes(rt_text_to_bytes(
    "HTTP/1.1 200 OK\r\nTransfer-Encoding: chunked\r\n\r\n2\r\nHI\r\n"
)).is_err()).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering Browser HTTP/1 response parsing.
- Browser HTTP/1 response parsing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `670c50647d57239d0e3332ec41086d63c89abaf6369d7a1fa764962f035333b4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `670c50647d57239d0e3332ec41086d63c89abaf6369d7a1fa764962f035333b4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `670c50647d57239d0e3332ec41086d63c89abaf6369d7a1fa764962f035333b4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 8 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.spl:20:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a status-only response with no body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.spl:32:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a Content-Length delimited body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/gpu/browser_engine/h1_response_parse_spec.spl:45:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes a single-chunk Transfer-Encoding: chunked body' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
