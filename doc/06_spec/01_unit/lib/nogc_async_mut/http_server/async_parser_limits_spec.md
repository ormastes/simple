# Async HTTP Parser — request limits enforced during parsing

> The async server's incremental parser must enforce the same request limits as the sync server (shared `std.common.net.http_core` policy), and it must do so DURING parsing — before buffer growth — so a hostile client cannot exhaust memory with an endless request line, oversized headers, or an oversized body.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 18 | 18 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Async HTTP Parser — request limits enforced during parsing

The async server's incremental parser must enforce the same request limits as the sync server (shared `std.common.net.http_core` policy), and it must do so DURING parsing — before buffer growth — so a hostile client cannot exhaust memory with an endless request line, oversized headers, or an oversized body.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Requirements | N/A |
| Plan | doc/03_plan/agent_tasks/simple_erp.md |
| Design | N/A |
| Research | doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md |
| Source | `test/01_unit/lib/nogc_async_mut/http_server/async_parser_limits_spec.spl` |
| Updated | 2026-08-14 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

The async server's incremental parser must enforce the same request limits as
the sync server (shared `std.common.net.http_core` policy), and it must do so
DURING parsing — before buffer growth — so a hostile client cannot exhaust
memory with an endless request line, oversized headers, or an oversized body.

Each limit is proven at the boundary (accepted) and boundary+1 (rejected),
using `HttpRequestParser.with_limits` so the fixtures stay small. The
"endless" cases additionally prove the parser cuts a client off while the
terminator has NOT yet arrived — the memory-exhaustion scenario an
after-the-fact check cannot catch.

## Limit matrix proven here

| Limit | Boundary case | Over-limit case | Streaming case |
|-------|---------------|-----------------|----------------|
| Request line | exact length accepted | +1 byte → 431 | endless line cut off |
| Header line | exact length accepted | +1 byte → 431 | endless header cut off |
| Header count | exact count accepted | +1 header → 431 | — |
| Body (Content-Length) | exact size accepted | declared +1 → 413 pre-buffer | rejected before body bytes |
| Body (chunked) | small body decoded | decoded over limit → 413 | raw accumulation cut off → 413 |

## Examples

```simple
var p = HttpRequestParser.with_limits(64, 100, 8192, 10485760)
val r = p.feed("GET /" + long_path + " HTTP/1.1\r\n")
# Err(ParseError("431 Request line too long: ...")) once the limit is crossed
```

## Troubleshooting

- `431` in `error_message` — a line/header limit fired during parsing.
- `413` — the declared or decoded body exceeds `max_body`; note the
  rejection happens BEFORE body bytes are buffered.
- `400` — duplicate/invalid Content-Length or Content-Length combined with
  chunked (smuggling ambiguity), decided by the shared core.

**Requirements:** N/A
**Plan:** doc/03_plan/agent_tasks/simple_erp.md
**Design:** N/A
**Research:** doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md

Lane: .spipe/simple_enterprise_suite (Wave A, AC-2).

## Scenarios

### async parser — request line limit

#### accepts a request line exactly at the limit

- Open a parser with a 64-byte request-line limit
- var p = HttpRequestParser with limits
   - Expected: line.len() equals `64`
- Feed the boundary-length request line


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Open a parser with a 64-byte request-line limit")
var p = HttpRequestParser.with_limits(64, 100, 8192, 10485760)
# "GET " + path + " HTTP/1.1" == 4 + 51 + 9 == exactly 64 bytes
val path = "/" + repeat_char("a", 50)
val line = "GET " + path + " HTTP/1.1"
expect(line.len()).to_equal(64)

step("Feed the boundary-length request line")
expect(feed_ok(p, line + "\r\n")).to_be(true)
expect(p.has_error()).to_be(false)
```

</details>

#### rejects a request line one byte over the limit with 431

- var p = HttpRequestParser with limits
   - Expected: line.len() equals `65`
- Feed the over-limit request line


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(64, 100, 8192, 10485760)
val path = "/" + repeat_char("a", 51)
val line = "GET " + path + " HTTP/1.1"
expect(line.len()).to_equal(65)

step("Feed the over-limit request line")
expect(feed_ok(p, line + "\r\n")).to_be(false)
expect(p.has_error()).to_be(true)
expect(p.error_message.starts_with("431")).to_be(true)
```

</details>

#### cuts off an endless request line before buffering it all

- Stream request-line bytes with no CRLF terminator
- var p = HttpRequestParser with limits


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
step("Stream request-line bytes with no CRLF terminator")
var p = HttpRequestParser.with_limits(64, 100, 8192, 10485760)
expect(feed_ok(p, repeat_char("a", 80))).to_be(false)
expect(p.error_message.starts_with("431")).to_be(true)
```

</details>

### async parser — header line limit

#### accepts a header line exactly at the limit

- var p = HttpRequestParser with limits
- Feed the request line, then a boundary-length header line
   - Expected: hline.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 100, 32, 10485760)
step("Feed the request line, then a boundary-length header line")
expect(feed_ok(p, "GET / HTTP/1.1\r\n")).to_be(true)
# "X-A: " (5) + 27 = exactly 32 bytes
val hline = "X-A: " + repeat_char("b", 27)
expect(hline.len()).to_equal(32)
expect(feed_ok(p, hline + "\r\n")).to_be(true)
expect(p.has_error()).to_be(false)
```

</details>

#### rejects a header line one byte over the limit with 431

- var p = HttpRequestParser with limits
   - Expected: hline.len() equals `33`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 100, 32, 10485760)
expect(feed_ok(p, "GET / HTTP/1.1\r\n")).to_be(true)
val hline = "X-A: " + repeat_char("b", 28)
expect(hline.len()).to_equal(33)
expect(feed_ok(p, hline + "\r\n")).to_be(false)
expect(p.error_message.starts_with("431")).to_be(true)
```

</details>

#### cuts off an endless header line before buffering it all

- var p = HttpRequestParser with limits
- Stream header bytes with no CRLF terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 100, 32, 10485760)
expect(feed_ok(p, "GET / HTTP/1.1\r\n")).to_be(true)
step("Stream header bytes with no CRLF terminator")
expect(feed_ok(p, repeat_char("c", 40))).to_be(false)
expect(p.error_message.starts_with("431")).to_be(true)
```

</details>

### async parser — header count limit

#### accepts exactly the maximum number of headers

- var p = HttpRequestParser with limits
- Feed a request with exactly 3 headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 3, 8192, 10485760)
step("Feed a request with exactly 3 headers")
expect(feed_ok(p, "GET / HTTP/1.1\r\nA: 1\r\nB: 2\r\nC: 3\r\n\r\n")).to_be(true)
expect(p.is_complete()).to_be(true)
```

</details>

#### rejects one header beyond the maximum with 431

- var p = HttpRequestParser with limits
- Feed a request with 4 headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 3, 8192, 10485760)
step("Feed a request with 4 headers")
expect(feed_ok(p, "GET / HTTP/1.1\r\nA: 1\r\nB: 2\r\nC: 3\r\nD: 4\r\n\r\n")).to_be(false)
expect(p.error_message.starts_with("431")).to_be(true)
```

</details>

### async parser — body size limit

#### accepts a Content-Length body exactly at the limit

- var p = HttpRequestParser with limits
- POST a body of exactly 16 bytes
   - Expected: req.body.len() equals `16`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 100, 8192, 16)
step("POST a body of exactly 16 bytes")
val body = repeat_char("d", 16)
expect(feed_ok(p, "POST / HTTP/1.1\r\nContent-Length: 16\r\n\r\n" + body)).to_be(true)
expect(p.is_complete()).to_be(true)
val req = p.to_request("127.0.0.1")
expect(req.body.len()).to_equal(16)
```

</details>

#### rejects a declared body one byte over the limit with 413

- var p = HttpRequestParser with limits
- Declare Content-Length 17 against a 16-byte limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 100, 8192, 16)
step("Declare Content-Length 17 against a 16-byte limit")
expect(feed_ok(p, "POST / HTTP/1.1\r\nContent-Length: 17\r\n\r\n")).to_be(false)
expect(p.error_message.starts_with("413")).to_be(true)
```

</details>

#### rejects the declared body BEFORE any body bytes arrive

- var p = HttpRequestParser with limits
- Send only the headers of an oversized POST
- Verify no body bytes were ever buffered
   - Expected: p.body.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 100, 8192, 16)
step("Send only the headers of an oversized POST")
val accepted = feed_ok(p, "POST / HTTP/1.1\r\nContent-Length: 9999\r\n\r\n")
expect(accepted).to_be(false)
step("Verify no body bytes were ever buffered")
expect(p.body.len()).to_equal(0)
```

</details>

### async parser — header policy parity with the shared core

#### rejects duplicate Content-Length with 400

- var p = HttpRequestParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.new()
expect(feed_ok(p, "POST / HTTP/1.1\r\nContent-Length: 4\r\nContent-Length: 4\r\n\r\n")).to_be(false)
expect(p.error_message.starts_with("400")).to_be(true)
```

</details>

#### rejects invalid Content-Length with 400

- var p = HttpRequestParser new


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.new()
expect(feed_ok(p, "POST / HTTP/1.1\r\nContent-Length: abc\r\n\r\n")).to_be(false)
expect(p.error_message.starts_with("400")).to_be(true)
```

</details>

#### rejects Content-Length combined with chunked as smuggling ambiguity

- var p = HttpRequestParser new
- Send BOTH Content-Length and Transfer-Encoding: chunked


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.new()
step("Send BOTH Content-Length and Transfer-Encoding: chunked")
expect(feed_ok(p, "POST / HTTP/1.1\r\nContent-Length: 4\r\nTransfer-Encoding: chunked\r\n\r\n")).to_be(false)
expect(p.error_message.starts_with("400")).to_be(true)
```

</details>

### async parser — chunked bodies stay bounded

#### decodes a small chunked body normally

- var p = HttpRequestParser new
- Send a well-formed 4-byte chunked body
   - Expected: req.body equals `Wiki`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.new()
step("Send a well-formed 4-byte chunked body")
expect(feed_ok(p, "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n4\r\nWiki\r\n0\r\n\r\n")).to_be(true)
expect(p.is_complete()).to_be(true)
val req = p.to_request("127.0.0.1")
expect(req.body).to_equal("Wiki")
```

</details>

#### cuts off unbounded chunked accumulation with 413

- var p = HttpRequestParser with limits
- Stream chunk bytes past the accumulation bound with no terminator


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 100, 8192, 16)
expect(feed_ok(p, "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n")).to_be(true)
step("Stream chunk bytes past the accumulation bound with no terminator")
# Raw accumulation bound is max_body + max_header_line (16 + 8192).
expect(feed_ok(p, repeat_char("e", 8300))).to_be(false)
expect(p.error_message.starts_with("413")).to_be(true)
```

</details>

#### rejects a decoded chunked body over the limit with 413

- var p = HttpRequestParser with limits
- Send a well-formed chunked body decoding to 5 bytes against a 4-byte limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.with_limits(8192, 100, 8192, 4)
expect(feed_ok(p, "POST / HTTP/1.1\r\nTransfer-Encoding: chunked\r\n\r\n")).to_be(true)
step("Send a well-formed chunked body decoding to 5 bytes against a 4-byte limit")
expect(feed_ok(p, "5\r\nWikis\r\n0\r\n\r\n")).to_be(false)
expect(p.error_message.starts_with("413")).to_be(true)
```

</details>

### async parser — well-formed requests still parse

#### parses a complete GET request end to end

- var p = HttpRequestParser new
- Feed a complete request in two fragments
- Verify the parsed request fields
   - Expected: req.method equals `GET`
   - Expected: req.path equals `/hello`
   - Expected: req.query equals `x=1`
   - Expected: req.headers.len() equals `1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
var p = HttpRequestParser.new()
step("Feed a complete request in two fragments")
expect(feed_ok(p, "GET /hello?x=1 HTTP/1.1\r\nHost: example.com\r\n")).to_be(true)
expect(feed_ok(p, "\r\n")).to_be(true)
step("Verify the parsed request fields")
expect(p.is_complete()).to_be(true)
val req = p.to_request("127.0.0.1")
expect(req.method).to_equal("GET")
expect(req.path).to_equal("/hello")
expect(req.query).to_equal("x=1")
expect(req.headers.len()).to_equal(1)
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


## Related Documentation

- **Plan:** `doc/03_plan/agent_tasks/simple_erp.md`
- **Research:** `doc/01_research/local/simple_enterprise_suite_assessment_2026-08-14.md`


</details>
