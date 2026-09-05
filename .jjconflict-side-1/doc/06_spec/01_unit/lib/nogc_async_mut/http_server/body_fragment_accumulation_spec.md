# Bounded HTTP body accumulation under one-byte fragmentation

> The Content-Length body is accumulated as chunks and joined once on

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Bounded HTTP body accumulation under one-byte fragmentation

The Content-Length body is accumulated as chunks and joined once on

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

The Content-Length body is accumulated as chunks and joined once on
completion. Appending to the retained `body` on every feed rebuilt the whole
body each time, which is O(n^2) byte copying under adversarial one-byte
fragmentation.

These scenarios pin the OBSERVABLE contract that the chunk-accumulation
refactor must preserve: identical body bytes, identical `consumed`
accounting, and correct reuse across a keep-alive `reset()`.

## Scenarios

### HTTP body accumulation under fragmentation

#### reassembles a Content-Length body fed one byte at a time

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reassembles a Content-Length body fed one byte at a time
   - Expected: consumed equals `req.len()`
   - Expected: parser.to_request("t").body equals `body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassembles a Content-Length body fed one byte at a time")
val parser = HttpRequestParser.new()
val body = "abcdefghijklmnopqrstuvwxyz"
val req = "POST /u HTTP/1.1\r\nHost: h\r\nContent-Length: {body.len()}\r\n\r\n{body}"
val consumed = _feed_one_byte_at_a_time(parser, req)
expect(consumed).to_equal(req.len())
expect(parser.to_request("t").body).to_equal(body)
```

</details>

#### reassembles the same body delivered as one whole feed

- reassembles the same body delivered as one whole feed
   - Expected: n equals `req.len()`
   - Expected: false is true
   - Expected: parser.to_request("t").body equals `body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassembles the same body delivered as one whole feed")
val parser = HttpRequestParser.new()
val body = "abcdefghijklmnopqrstuvwxyz"
val req = "POST /u HTTP/1.1\r\nHost: h\r\nContent-Length: {body.len()}\r\n\r\n{body}"
val r = parser.feed(req)
match r:
    Ok(n):
        expect(n).to_equal(req.len())
    Err(_):
        expect(false).to_equal(true)
expect(parser.to_request("t").body).to_equal(body)
```

</details>

#### accumulates a fresh body after a keep-alive reset

- accumulates a fresh body after a keep-alive reset
   - Expected: parser.to_request("t").body equals `AAA`
   - Expected: parser.to_request("t").body equals `BB`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accumulates a fresh body after a keep-alive reset")
val parser = HttpRequestParser.new()
val first = "POST /a HTTP/1.1\r\nHost: h\r\nContent-Length: 3\r\n\r\nAAA"
val _ = parser.feed(first)
expect(parser.to_request("t").body).to_equal("AAA")
parser.reset()
val second = "POST /b HTTP/1.1\r\nHost: h\r\nContent-Length: 2\r\n\r\nBB"
val _2 = _feed_one_byte_at_a_time(parser, second)
expect(parser.to_request("t").body).to_equal("BB")
```

</details>

#### reassembles a body split into two uneven fragments

- reassembles a body split into two uneven fragments
   - Expected: parser.to_request("t").body equals `123456`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reassembles a body split into two uneven fragments")
val parser = HttpRequestParser.new()
val req = "POST /u HTTP/1.1\r\nHost: h\r\nContent-Length: 6\r\n\r\n123456"
val cut = req.len() - 4
val a = parser.feed(req.slice(0, cut))
val b = parser.feed(req.slice(cut, req.len()))
expect(parser.to_request("t").body).to_equal("123456")
```

</details>

### accumulation work grows linearly, not quadratically

#### copies O(n) bytes appending n one-byte chunks

- copies O(n) bytes appending n one-byte chunks
   - Expected: buf.len() equals `n`
   - Expected: copied equals `n`
   - Expected: copied < (n * (n + 1)) / 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copies O(n) bytes appending n one-byte chunks")
# Pre-fix `buf = buf + chunk` copied the whole retained prefix per
# chunk: sum(1..n) = n*(n+1)/2. Amortized append copies each byte once.
var buf: [u8] = []
var copied: i64 = 0
var i: i64 = 0
val n: i64 = 64
while i < n:
    copied = copied + io_append_chunk(buf, [7u8])
    i = i + 1
expect(buf.len()).to_equal(n)
expect(copied).to_equal(n)
# Quadratic behavior would be 2080 for n=64.
expect(copied < (n * (n + 1)) / 2).to_equal(true)
```

</details>

#### keeps append work linear as fragment count doubles

- keeps append work linear as fragment count doubles
   - Expected: big_work equals `small_work * 2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps append work linear as fragment count doubles")
var small: [u8] = []
var small_work: i64 = 0
var a: i64 = 0
while a < 32:
    small_work = small_work + io_append_chunk(small, [1u8])
    a = a + 1
var big: [u8] = []
var big_work: i64 = 0
var b: i64 = 0
while b < 64:
    big_work = big_work + io_append_chunk(big, [1u8])
    b = b + 1
# Linear: doubling fragments doubles work. Quadratic would quadruple it.
expect(big_work).to_equal(small_work * 2)
```

</details>

#### copies O(n) body bytes when the body is fed one byte at a time

- copies O(n) body bytes when the body is fed one byte at a time
   - Expected: parser.to_request("t").body equals `body`
   - Expected: parser.body_copy_work() equals `n * 2`
   - Expected: parser.body_copy_work() < (n * (n + 1)) / 2 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("copies O(n) body bytes when the body is fed one byte at a time")
val parser = HttpRequestParser.new()
val body = "0123456789012345678901234567890123456789"
val req = "POST /u HTTP/1.1\r\nHost: h\r\nContent-Length: {body.len()}\r\n\r\n{body}"
val _ = _feed_one_byte_at_a_time(parser, req)
expect(parser.to_request("t").body).to_equal(body)
# Each body byte is copied once into a chunk, then once by the final
# join: 2n. Pre-fix per-feed concat was n*(n+1)/2.
val n = body.len()
expect(parser.body_copy_work()).to_equal(n * 2)
expect(parser.body_copy_work() < (n * (n + 1)) / 2).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `3793ade9ef399292308e4cc0100c668054fd2b875e0de30cfcab52c295800c6f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3793ade9ef399292308e4cc0100c668054fd2b875e0de30cfcab52c295800c6f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3793ade9ef399292308e4cc0100c668054fd2b875e0de30cfcab52c295800c6f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reassembles a Content-Length body fed one byte at a time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reassembles the same body delivered as one whole feed' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/http_server/body_fragment_accumulation_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accumulates a fresh body after a keep-alive reset' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
