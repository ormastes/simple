# chunked_size_overflow_spec

> Purpose: Prove that chunked_body_end — chunk-size overflow.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# chunked_size_overflow_spec

Purpose: Prove that chunked_body_end — chunk-size overflow.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http_server/chunked_size_overflow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that chunked_body_end — chunk-size overflow.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### chunked_body_end — chunk-size overflow

#### rejects a 2^64 chunk-size instead of wrapping it to a last-chunk

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects a 2^64 chunk-size instead of wrapping it to a last-chunk
- Verify: rejects a 2^64 chunk-size instead of wrapping it to a last-chunk
   - Expected: chunked_body_end("10000000000000000\r\nX\r\n\r\n") equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a 2^64 chunk-size instead of wrapping it to a last-chunk")
step("Verify: rejects a 2^64 chunk-size instead of wrapping it to a last-chunk")
# @req: REQ-LIB-HTTP-SERVER-001
# Pre-fix this returned 24: the size wrapped to 0, the body ended here,
# and "GET /admin ..." would have been read as a second request.
expect(chunked_body_end("10000000000000000\r\nX\r\n\r\n")).to_equal(-2)
```

</details>

#### rejects a 2^64+5 chunk-size instead of wrapping it to 5

- rejects a 2^64+5 chunk-size instead of wrapping it to 5
- Verify: rejects a 2^64+5 chunk-size instead of wrapping it to 5
   - Expected: chunked_body_end("10000000000000005\r\nABCDE\r\n0\r\n\r\n") equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a 2^64+5 chunk-size instead of wrapping it to 5")
step("Verify: rejects a 2^64+5 chunk-size instead of wrapping it to 5")
expect(chunked_body_end("10000000000000005\r\nABCDE\r\n0\r\n\r\n")).to_equal(-2)
```

</details>

#### rejects a 16-hex-digit chunk-size that exceeds i64

- rejects a 16-hex-digit chunk-size that exceeds i64
- Verify: rejects a 16-hex-digit chunk-size that exceeds i64
   - Expected: chunked_body_end("FFFFFFFFFFFFFFFF\r\nX\r\n0\r\n\r\n") equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a 16-hex-digit chunk-size that exceeds i64")
step("Verify: rejects a 16-hex-digit chunk-size that exceeds i64")
expect(chunked_body_end("FFFFFFFFFFFFFFFF\r\nX\r\n0\r\n\r\n")).to_equal(-2)
```

</details>

#### rejects an overflowing chunk-size carrying a chunk extension

- rejects an overflowing chunk-size carrying a chunk extension
- Verify: rejects an overflowing chunk-size carrying a chunk extension
   - Expected: chunked_body_end("10000000000000000;a=b\r\nX\r\n\r\n") equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an overflowing chunk-size carrying a chunk extension")
step("Verify: rejects an overflowing chunk-size carrying a chunk extension")
expect(chunked_body_end("10000000000000000;a=b\r\nX\r\n\r\n")).to_equal(-2)
```

</details>

### decode_chunked — chunk-size overflow

#### returns Err for an overflowing chunk-size

- returns Err for an overflowing chunk-size
- Verify: returns Err for an overflowing chunk-size


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Err for an overflowing chunk-size")
step("Verify: returns Err for an overflowing chunk-size")
match decode_chunked("10000000000000000\r\nX\r\n\r\n"):
    case Ok(_):
        assert_true(false)
    case Err(err):
        assert_false(err.is_empty())
```

</details>

### async proxy — chunk-size overflow

#### does not report a wrapped 2^64 chunk-size as a complete body

- does not report a wrapped 2^64 chunk-size as a complete body
- Verify: does not report a wrapped 2^64 chunk-size as a complete body


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not report a wrapped 2^64 chunk-size as a complete body")
step("Verify: does not report a wrapped 2^64 chunk-size as a complete body")
# Pre-fix this returned true.
assert_false(async_proxy_chunked_body_complete("10000000000000000\r\nGET /admin HTTP/1.1\r\n\r\n"))
```

</details>

#### still reports a genuinely terminated stream as complete

- still reports a genuinely terminated stream as complete
- Verify: still reports a genuinely terminated stream as complete


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still reports a genuinely terminated stream as complete")
step("Verify: still reports a genuinely terminated stream as complete")
assert_true(async_proxy_chunked_body_complete("5\r\nhello\r\n0\r\n\r\n"))
```

</details>

### HttpRequestParser — the smuggled request is rejected, not queued

#### answers a framing error instead of ending the message at the wrapped size

- answers a framing error instead of ending the message at the wrapped size
- Verify: answers a framing error instead of ending the message at the wrapped size
   - Expected: r.is_ok() is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("answers a framing error instead of ending the message at the wrapped size")
step("Verify: answers a framing error instead of ending the message at the wrapped size")
# The security property lives in the CALLER: chunked_body_end returning
# -2 must reach the new parser.spl branch and become a ParseError, not
# leave the parser sitting in Body state waiting for more data. Pre-fix
# the body ended at the wrapped 0-size chunk and "GET /admin ..." was
# read as a second, smuggled request on the same connection.
var p = HttpRequestParser.new()
val raw = "POST /a HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n10000000000000000\r\nGET /admin HTTP/1.1\r\nHost: x\r\n\r\n"
val r = p.feed(raw)
expect(r.is_ok()).to_equal(false)
assert_true(p.has_error())
assert_false(p.is_complete())
```

</details>

#### still completes a valid chunked request

- still completes a valid chunked request
- Verify: still completes a valid chunked request
   - Expected: r.is_ok() is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("still completes a valid chunked request")
step("Verify: still completes a valid chunked request")
var p = HttpRequestParser.new()
val raw = "POST /a HTTP/1.1\r\nHost: x\r\nTransfer-Encoding: chunked\r\n\r\n5\r\nhello\r\n0\r\n\r\n"
val r = p.feed(raw)
expect(r.is_ok()).to_equal(true)
assert_true(p.is_complete())
```

</details>

### negative controls — valid sizes are untouched

#### accepts a normal terminated stream

- accepts a normal terminated stream
- Verify: accepts a normal terminated stream
   - Expected: chunked_body_end("5\r\nhello\r\n0\r\n\r\n") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a normal terminated stream")
step("Verify: accepts a normal terminated stream")
expect(chunked_body_end("5\r\nhello\r\n0\r\n\r\n")).to_equal(15)
```

</details>

#### accepts a size padded with many leading zeros

- accepts a size padded with many leading zeros
- Verify: accepts a size padded with many leading zeros
   - Expected: chunked_body_end(buf) equals `buf.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a size padded with many leading zeros")
step("Verify: accepts a size padded with many leading zeros")
val buf = "0000000000000000005\r\nhello\r\n0\r\n\r\n"
expect(chunked_body_end(buf)).to_equal(buf.len())
```

</details>

#### accepts the widest non-overflowing size and waits for its data

- accepts the widest non-overflowing size and waits for its data
- Verify: accepts the widest non-overflowing size and waits for its data
   - Expected: chunked_body_end("FFFFFFFFFFFFFFF\r\nX\r\n") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts the widest non-overflowing size and waits for its data")
step("Verify: accepts the widest non-overflowing size and waits for its data")
expect(chunked_body_end("FFFFFFFFFFFFFFF\r\nX\r\n")).to_equal(-1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 12 |
| Active scenarios | 12 |
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

- Canonical SPipe generation for source `8a22c07c150c9680b28464a5d1a912f5c10accd4d42ae6fcc17dca85e9c68d69`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `8a22c07c150c9680b28464a5d1a912f5c10accd4d42ae6fcc17dca85e9c68d69`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `8a22c07c150c9680b28464a5d1a912f5c10accd4d42ae6fcc17dca85e9c68d69`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/http_server/chunked_size_overflow_spec.spl
mirror: doc/06_spec/01_unit/lib/http_server/chunked_size_overflow_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http_server/chunked_size_overflow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http_server/chunked_size_overflow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http_server/chunked_size_overflow_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/http_server/chunked_size_overflow_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a 2^64 chunk-size instead of wrapping it to a last-chunk' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/chunked_size_overflow_spec.spl:61:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a 2^64+5 chunk-size instead of wrapping it to 5' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http_server/chunked_size_overflow_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a 16-hex-digit chunk-size that exceeds i64' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
