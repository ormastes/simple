# chunked_body_boundary_spec

> Purpose: Prove that chunked_body_end — boundary-aware detector.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# chunked_body_boundary_spec

Purpose: Prove that chunked_body_end — boundary-aware detector.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_server/chunked_body_boundary_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that chunked_body_end — boundary-aware detector.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### chunked_body_end — boundary-aware detector

#### reports complete at full length for a simple terminated stream

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports complete at full length for a simple terminated stream
- Verify: reports complete at full length for a simple terminated stream
   - Expected: chunked_body_end("5\r\nhello\r\n0\r\n\r\n") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports complete at full length for a simple terminated stream")
step("Verify: reports complete at full length for a simple terminated stream")
# @req: REQ-LIB-HTTP-SERVER-001
expect(chunked_body_end("5\r\nhello\r\n0\r\n\r\n")).to_equal(15)
```

</details>

#### does not match 0-CRLF-CRLF inside chunk data

- does not match 0-CRLF-CRLF inside chunk data
- Verify: does not match 0-CRLF-CRLF inside chunk data
   - Expected: chunked_body_end(enc) equals `enc.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not match 0-CRLF-CRLF inside chunk data")
step("Verify: does not match 0-CRLF-CRLF inside chunk data")
# 9-byte chunk whose DATA contains the 5 bytes "0\r\n\r\n"
val enc = "9\r\nAB0\r\n\r\nCD\r\n0\r\n\r\n"
expect(chunked_body_end(enc)).to_equal(enc.len())
```

</details>

#### reports incomplete when the buffer ends mid-chunk on an embedded 0-CRLF-CRLF

- reports incomplete when the buffer ends mid-chunk on an embedded 0-CRLF-CRLF
- Verify: reports incomplete when the buffer ends mid-chunk on an embedded 0-CRLF-CRLF
   - Expected: chunked_body_end("9\r\nAB0\r\n\r\n") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports incomplete when the buffer ends mid-chunk on an embedded 0-CRLF-CRLF")
step("Verify: reports incomplete when the buffer ends mid-chunk on an embedded 0-CRLF-CRLF")
# A flat scan would falsely claim the body ended here
expect(chunked_body_end("9\r\nAB0\r\n\r\n")).to_equal(-1)
```

</details>

#### reports incomplete mid chunk-size line

- reports incomplete mid chunk-size line
- Verify: reports incomplete mid chunk-size line
   - Expected: chunked_body_end("5") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports incomplete mid chunk-size line")
step("Verify: reports incomplete mid chunk-size line")
expect(chunked_body_end("5")).to_equal(-1)
```

</details>

#### reports a framing error for a non-hex chunk-size line

- reports a framing error for a non-hex chunk-size line
- Verify: reports a framing error for a non-hex chunk-size line
   - Expected: chunked_body_end("XYZ\r\nhello\r\n0\r\n\r\n") equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports a framing error for a non-hex chunk-size line")
step("Verify: reports a framing error for a non-hex chunk-size line")
expect(chunked_body_end("XYZ\r\nhello\r\n0\r\n\r\n")).to_equal(-2)
```

</details>

#### strips chunk extensions before validating the size

- strips chunk extensions before validating the size
- Verify: strips chunk extensions before validating the size
   - Expected: chunked_body_end(enc) equals `enc.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("strips chunk extensions before validating the size")
step("Verify: strips chunk extensions before validating the size")
val enc = "5;name=value\r\nhello\r\n0\r\n\r\n"
expect(chunked_body_end(enc)).to_equal(enc.len())
```

</details>

### HttpRequestParser — chunked payload containing 0-CRLF-CRLF

#### receives the full body when a chunk payload embeds the terminator bytes

- receives the full body when a chunk payload embeds the terminator bytes
- Verify: receives the full body when a chunk payload embeds the terminator bytes
   - Expected: r.is_ok() is true
   - Expected: data.body equals `AB0\r\n\r\nCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("receives the full body when a chunk payload embeds the terminator bytes")
step("Verify: receives the full body when a chunk payload embeds the terminator bytes")
val parser = HttpRequestParser.new()
val req = "POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n" +
          "9\r\nAB0\r\n\r\nCD\r\n0\r\n\r\n"
val r = parser.feed(req)
expect(r.is_ok()).to_equal(true)
assert_true(parser.is_complete())
val data = parser.to_request("127.0.0.1")
expect(data.body).to_equal("AB0\r\n\r\nCD")
```

</details>

#### waits for more data when fed a partial buffer ending on embedded terminator bytes

- waits for more data when fed a partial buffer ending on embedded terminator bytes
- Verify: waits for more data when fed a partial buffer ending on embedded terminator bytes
   - Expected: r1.is_ok() is true
   - Expected: r2.is_ok() is true
   - Expected: data.body equals `AB0\r\n\r\nCD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("waits for more data when fed a partial buffer ending on embedded terminator bytes")
step("Verify: waits for more data when fed a partial buffer ending on embedded terminator bytes")
val parser = HttpRequestParser.new()
val head = "POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n" +
           "9\r\nAB0\r\n\r\n"
val r1 = parser.feed(head)
expect(r1.is_ok()).to_equal(true)
assert_false(parser.is_complete())
val r2 = parser.feed("CD\r\n0\r\n\r\n")
expect(r2.is_ok()).to_equal(true)
assert_true(parser.is_complete())
val data = parser.to_request("127.0.0.1")
expect(data.body).to_equal("AB0\r\n\r\nCD")
```

</details>

#### still detects the end of a genuinely terminated stream

- still detects the end of a genuinely terminated stream
- Verify: still detects the end of a genuinely terminated stream
   - Expected: r.is_ok() is true
   - Expected: data.body equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still detects the end of a genuinely terminated stream")
step("Verify: still detects the end of a genuinely terminated stream")
val parser = HttpRequestParser.new()
val req = "POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n" +
          "5\r\nhello\r\n0\r\n\r\n"
val r = parser.feed(req)
expect(r.is_ok()).to_equal(true)
assert_true(parser.is_complete())
val data = parser.to_request("127.0.0.1")
expect(data.body).to_equal("hello")
```

</details>

#### rejects an invalid chunk-size line as a framing error

- rejects an invalid chunk-size line as a framing error
- Verify: rejects an invalid chunk-size line as a framing error
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an invalid chunk-size line as a framing error")
step("Verify: rejects an invalid chunk-size line as a framing error")
val parser = HttpRequestParser.new()
val req = "POST / HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n" +
          "XYZ\r\nhello\r\n0\r\n\r\n"
val r = parser.feed(req)
expect(r.is_ok()).to_equal(false)
assert_true(parser.has_error())
```

</details>

### async proxy — chunked body completion boundary walk

#### does not report complete on terminator bytes inside chunk data

- does not report complete on terminator bytes inside chunk data
- Verify: does not report complete on terminator bytes inside chunk data


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not report complete on terminator bytes inside chunk data")
step("Verify: does not report complete on terminator bytes inside chunk data")
assert_false(async_proxy_chunked_body_complete("9\r\nAB0\r\n\r\n"))
```

</details>

#### reports complete once the real terminal chunk arrives

- reports complete once the real terminal chunk arrives
- Verify: reports complete once the real terminal chunk arrives


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports complete once the real terminal chunk arrives")
step("Verify: reports complete once the real terminal chunk arrives")
assert_true(async_proxy_chunked_body_complete("9\r\nAB0\r\n\r\nCD\r\n0\r\n\r\n"))
```

</details>

#### reports complete for a simple terminated stream

- reports complete for a simple terminated stream
- Verify: reports complete for a simple terminated stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports complete for a simple terminated stream")
step("Verify: reports complete for a simple terminated stream")
assert_true(async_proxy_chunked_body_complete("5\r\nhello\r\n0\r\n\r\n"))
```

</details>

#### reports incomplete for a truncated stream

- reports incomplete for a truncated stream
- Verify: reports incomplete for a truncated stream


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports incomplete for a truncated stream")
step("Verify: reports incomplete for a truncated stream")
assert_false(async_proxy_chunked_body_complete("5\r\nhel"))
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-HTTP-SERVER-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `1979f257d0fe3a31842f1dd0622ab51effacc0a4e75ae0188d452dd8923175c3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `1979f257d0fe3a31842f1dd0622ab51effacc0a4e75ae0188d452dd8923175c3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `1979f257d0fe3a31842f1dd0622ab51effacc0a4e75ae0188d452dd8923175c3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/http_server/chunked_body_boundary_spec.spl
mirror: doc/06_spec/01_unit/lib/http_server/chunked_body_boundary_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http_server/chunked_body_boundary_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http_server/chunked_body_boundary_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http_server/chunked_body_boundary_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/http_server/chunked_body_boundary_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports complete at full length for a simple terminated stream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/chunked_body_boundary_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not match 0-CRLF-CRLF inside chunk data' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/chunked_body_boundary_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports incomplete when the buffer ends mid-chunk on an embedded 0-CRLF-CRLF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
