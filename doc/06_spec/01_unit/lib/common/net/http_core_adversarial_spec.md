# http_core — adversarial edge hardening (lane W17-B)

> Purpose: Prove that http_core — hex_chunk_size fails closed on hostile chunk sizes.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 32 | 32 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# http_core — adversarial edge hardening (lane W17-B)

Purpose: Prove that http_core — hex_chunk_size fails closed on hostile chunk sizes.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/net/http_core_adversarial_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Prove that http_core — hex_chunk_size fails closed on hostile chunk sizes.
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### http_core — hex_chunk_size fails closed on hostile chunk sizes

#### parses a valid lowercase hex chunk size

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a valid lowercase hex chunk size
- Verify: parses a valid lowercase hex chunk size
   - Expected: hex_chunk_size("ff") equals `255`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a valid lowercase hex chunk size")
step("Verify: parses a valid lowercase hex chunk size")
# @req: REQ-LIB-COMMON-001
expect(hex_chunk_size("ff")).to_equal(255)
```

</details>

#### parses a valid uppercase hex chunk size

- parses a valid uppercase hex chunk size
- Verify: parses a valid uppercase hex chunk size
   - Expected: hex_chunk_size("1A") equals `26`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a valid uppercase hex chunk size")
step("Verify: parses a valid uppercase hex chunk size")
expect(hex_chunk_size("1A")).to_equal(26)
```

</details>

#### rejects an empty chunk-size field

- rejects an empty chunk-size field
- Verify: rejects an empty chunk-size field
   - Expected: hex_chunk_size("") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an empty chunk-size field")
step("Verify: rejects an empty chunk-size field")
expect(hex_chunk_size("")).to_equal(-1)
```

</details>

#### rejects a non-hex character (smuggled garbage size)

- rejects a non-hex character (smuggled garbage size)
- Verify: rejects a non-hex character (smuggled garbage size)
   - Expected: hex_chunk_size("xz") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a non-hex character (smuggled garbage size)")
step("Verify: rejects a non-hex character (smuggled garbage size)")
expect(hex_chunk_size("xz")).to_equal(-1)
```

</details>

#### rejects a chunk size beyond the 2^27 sanity bound

- rejects a chunk size beyond the 2^27 sanity bound
- A single 256 MiB chunk (10000000 hex) is hostile
   - Expected: hex_chunk_size("10000000") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a chunk size beyond the 2^27 sanity bound")
step("A single 256 MiB chunk (10000000 hex) is hostile")
expect(hex_chunk_size("10000000")).to_equal(-1)
```

</details>

### http_core — decode_chunked_bounded rejects malformed framing

#### decodes a well-formed chunked body

- decodes a well-formed chunked body
- Verify: decodes a well-formed chunked body
   - Expected: r.0 equals ``
   - Expected: r.1 equals `hello`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("decodes a well-formed chunked body")
step("Verify: decodes a well-formed chunked body")
val r = decode_chunked_bounded("5\r\nhello\r\n0\r\n\r\n", 1024)
expect(r.0).to_equal("")
expect(r.1).to_equal("hello")
```

</details>

#### rejects a bad chunk-size line with 400

- rejects a bad chunk-size line with 400
- Verify: rejects a bad chunk-size line with 400


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a bad chunk-size line with 400")
step("Verify: rejects a bad chunk-size line with 400")
val r = decode_chunked_bounded("zz\r\nhello\r\n0\r\n\r\n", 1024)
expect(r.0.starts_with("400")).to_be(true)
```

</details>

#### rejects a truncated chunk (size larger than data) with 400

- rejects a truncated chunk (size larger than data) with 400
- Verify: rejects a truncated chunk (size larger than data) with 400


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a truncated chunk (size larger than data) with 400")
step("Verify: rejects a truncated chunk (size larger than data) with 400")
val r = decode_chunked_bounded("5\r\nhi\r\n0\r\n\r\n", 1024)
expect(r.0.starts_with("400")).to_be(true)
```

</details>

#### rejects a chunk missing its CRLF terminator with 400

- rejects a chunk missing its CRLF terminator with 400
- Data followed by non-CRLF bytes must not be silently accepted


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a chunk missing its CRLF terminator with 400")
step("Data followed by non-CRLF bytes must not be silently accepted")
val r = decode_chunked_bounded("5\r\nhelloXX0\r\n\r\n", 1024)
expect(r.0.starts_with("400")).to_be(true)
```

</details>

#### rejects a decoded body exceeding max_body with 413

- rejects a decoded body exceeding max_body with 413
- Decoded size, not the encoded size, is what bounds memory


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a decoded body exceeding max_body with 413")
step("Decoded size, not the encoded size, is what bounds memory")
val r = decode_chunked_bounded("5\r\nhello\r\n0\r\n\r\n", 3)
expect(r.0.starts_with("413")).to_be(true)
```

</details>

### http_core — chunked_body_end_scan distinguishes invalid from incomplete

#### returns a positive end offset for complete framing

- returns a positive end offset for complete framing
- Verify: returns a positive end offset for complete framing
   - Expected: end equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a positive end offset for complete framing")
step("Verify: returns a positive end offset for complete framing")
val end = chunked_body_end_scan("5\r\nhello\r\n0\r\n\r\n")
expect(end).to_equal(15)  # oracle: 15 — named expected value from the requirement
```

</details>

#### returns -2 (provably invalid) on a bad chunk-size field

- returns -2 (provably invalid) on a bad chunk-size field
- Verify: returns -2 (provably invalid) on a bad chunk-size field
   - Expected: chunked_body_end_scan("zz\r\nhello\r\n0\r\n\r\n") equals `-2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns -2 (provably invalid) on a bad chunk-size field")
step("Verify: returns -2 (provably invalid) on a bad chunk-size field")
expect(chunked_body_end_scan("zz\r\nhello\r\n0\r\n\r\n")).to_equal(-2)
```

</details>

#### returns -1 (need more bytes) when the chunk data is truncated

- returns -1 (need more bytes) when the chunk data is truncated
- A short read must ask for more, never mis-frame
   - Expected: chunked_body_end_scan("5\r\nhel") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns -1 (need more bytes) when the chunk data is truncated")
step("A short read must ask for more, never mis-frame")
expect(chunked_body_end_scan("5\r\nhel")).to_equal(-1)
```

</details>

#### does not mistake a 0-chunk marker embedded in chunk DATA for the end

- does not mistake a 0-chunk marker embedded in chunk DATA for the end
- '0\\r\\n\\r\\n' inside data must be consumed as data, not termination
   - Expected: end equals `buf.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not mistake a 0-chunk marker embedded in chunk DATA for the end")
step("'0\\r\\n\\r\\n' inside data must be consumed as data, not termination")
val payload = "0\r\n\r\n"
val buf = "5\r\n" + payload + "\r\n0\r\n\r\n"
val end = chunked_body_end_scan(buf)
expect(end).to_equal(buf.len())
```

</details>

### http_core — duplicate singleton security headers are a smuggling vector

#### accepts a single Host header

- accepts a single Host header
- Verify: accepts a single Host header
   - Expected: d.0 equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a single Host header")
step("Verify: accepts a single Host header")
val d = body_decision([("Host", "example.com")], 1024, false)
expect(d.0).to_equal("")
```

</details>

#### rejects a duplicate Host header with 400

- rejects a duplicate Host header with 400
- Two Host headers let a proxy and origin disagree on authority


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a duplicate Host header with 400")
step("Two Host headers let a proxy and origin disagree on authority")
val d = body_decision([("Host", "a.com"), ("Host", "a.com")], 1024, false)
expect(d.0.starts_with("400")).to_be(true)
```

</details>

#### rejects conflicting duplicate Host headers with 400

- rejects conflicting duplicate Host headers with 400
- Verify: rejects conflicting duplicate Host headers with 400


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects conflicting duplicate Host headers with 400")
step("Verify: rejects conflicting duplicate Host headers with 400")
val d = body_decision([("Host", "a.com"), ("Host", "evil.com")], 1024, false)
expect(d.0.starts_with("400")).to_be(true)
```

</details>

#### rejects duplicate X-Forwarded-Host (spoofed forwarding chain)

- rejects duplicate X-Forwarded-Host (spoofed forwarding chain)
- Verify: rejects duplicate X-Forwarded-Host (spoofed forwarding chain)


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects duplicate X-Forwarded-Host (spoofed forwarding chain)")
step("Verify: rejects duplicate X-Forwarded-Host (spoofed forwarding chain)")
val d = body_decision([("X-Forwarded-Host", "a"), ("X-Forwarded-Host", "b")], 1024, false)
expect(d.0.starts_with("400")).to_be(true)
```

</details>

#### rejects duplicate Authorization headers

- rejects duplicate Authorization headers
- Verify: rejects duplicate Authorization headers


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects duplicate Authorization headers")
step("Verify: rejects duplicate Authorization headers")
val d = body_decision([("Authorization", "Bearer x"), ("Authorization", "Bearer y")], 1024, false)
expect(d.0.starts_with("400")).to_be(true)
```

</details>

### http_core — request-limit checks fail closed with correct status

#### rejects an over-long request line with 414

- rejects an over-long request line with 414
- Verify: rejects an over-long request line with 414
   - Expected: http_parse_error_status(e) equals `414`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an over-long request line with 414")
step("Verify: rejects an over-long request line with 414")
val limits = http_limits_default()
val long_line = "GET /" + repeat_char("a", 9000) + " HTTP/1.1"
val err = check_request_line(long_line, limits)
expect(err.is_some()).to_be(true)
match err:
    Some(e):
        expect(http_parse_error_status(e)).to_equal(414)  # oracle: 414 — named expected value from the requirement
    nil:
        expect(false).to_be(true)
```

</details>

#### rejects a malformed request line (too few parts) with 400

- rejects a malformed request line (too few parts) with 400
- Verify: rejects a malformed request line (too few parts) with 400
   - Expected: http_parse_error_status(e) equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a malformed request line (too few parts) with 400")
step("Verify: rejects a malformed request line (too few parts) with 400")
val limits = http_limits_default()
val err = check_request_line("GET", limits)
expect(err.is_some()).to_be(true)
match err:
    Some(e):
        expect(http_parse_error_status(e)).to_equal(400)  # oracle: 400 — named expected value from the requirement
    nil:
        expect(false).to_be(true)
```

</details>

#### accepts a well-formed request line

- accepts a well-formed request line
- Verify: accepts a well-formed request line


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a well-formed request line")
step("Verify: accepts a well-formed request line")
val limits = http_limits_default()
expect(check_request_line("GET / HTTP/1.1", limits).is_none()).to_be(true)
```

</details>

#### rejects too many headers with 400

- rejects too many headers with 400
- Verify: rejects too many headers with 400
   - Expected: http_parse_error_status(e) equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects too many headers with 400")
step("Verify: rejects too many headers with 400")
val limits = http_limits_default()
val err = check_header_count(101, limits)
expect(err.is_some()).to_be(true)
match err:
    Some(e):
        expect(http_parse_error_status(e)).to_equal(400)  # oracle: 400 — named expected value from the requirement
    nil:
        expect(false).to_be(true)
```

</details>

#### rejects an over-long single header line with 400

- rejects an over-long single header line with 400
- Verify: rejects an over-long single header line with 400
   - Expected: http_parse_error_status(e) equals `400`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an over-long single header line with 400")
step("Verify: rejects an over-long single header line with 400")
val limits = http_limits_default()
val big_value = repeat_char("v", 9000)
val err = check_header_size("X-Big", big_value, limits)
expect(err.is_some()).to_be(true)
match err:
    Some(e):
        expect(http_parse_error_status(e)).to_equal(400)  # oracle: 400 — named expected value from the requirement
    nil:
        expect(false).to_be(true)
```

</details>

#### rejects an over-sized body with 413

- rejects an over-sized body with 413
- Verify: rejects an over-sized body with 413
   - Expected: http_parse_error_status(e) equals `413`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects an over-sized body with 413")
step("Verify: rejects an over-sized body with 413")
val limits = http_limits_default()
val err = check_body_size(20000000, limits)
expect(err.is_some()).to_be(true)
match err:
    Some(e):
        expect(http_parse_error_status(e)).to_equal(413)  # oracle: 413 — named expected value from the requirement
    nil:
        expect(false).to_be(true)
```

</details>

#### accepts a body within the limit

- accepts a body within the limit
- Verify: accepts a body within the limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts a body within the limit")
step("Verify: accepts a body within the limit")
val limits = http_limits_default()
expect(check_body_size(1024, limits).is_none()).to_be(true)
```

</details>

### http_core — path guard rejects backslash traversal variants

#### rejects backslash dot-dot traversal

- rejects backslash dot-dot traversal
- Verify: rejects backslash dot-dot traversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects backslash dot-dot traversal")
step("Verify: rejects backslash dot-dot traversal")
expect(path_is_safe("/static\\..\\secret")).to_be(false)
```

</details>

#### rejects encoded-backslash dot-dot traversal

- rejects encoded-backslash dot-dot traversal
- Verify: rejects encoded-backslash dot-dot traversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects encoded-backslash dot-dot traversal")
step("Verify: rejects encoded-backslash dot-dot traversal")
expect(path_is_safe("/static/..%5csecret")).to_be(false)
```

</details>

#### rejects a raw null byte in the path

- rejects a raw null byte in the path
- Verify: rejects a raw null byte in the path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects a raw null byte in the path")
step("Verify: rejects a raw null byte in the path")
expect(path_is_safe("/a\0b")).to_be(false)
```

</details>

#### is_safe_static_path rejects a relative (no leading slash) path

- is_safe_static_path rejects a relative (no leading slash) path
- Verify: is_safe_static_path rejects a relative (no leading slash) path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_safe_static_path rejects a relative (no leading slash) path")
step("Verify: is_safe_static_path rejects a relative (no leading slash) path")
expect(is_safe_static_path("static/file")).to_be(false)
```

</details>

#### is_safe_static_path rejects a dot-dot traversal

- is_safe_static_path rejects a dot-dot traversal
- Verify: is_safe_static_path rejects a dot-dot traversal


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_safe_static_path rejects a dot-dot traversal")
step("Verify: is_safe_static_path rejects a dot-dot traversal")
expect(is_safe_static_path("/static/../etc/passwd")).to_be(false)
```

</details>

#### is_safe_static_path accepts a normal absolute path

- is_safe_static_path accepts a normal absolute path
- Verify: is_safe_static_path accepts a normal absolute path


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("is_safe_static_path accepts a normal absolute path")
step("Verify: is_safe_static_path accepts a normal absolute path")
expect(is_safe_static_path("/static/app.js")).to_be(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 32 |
| Active scenarios | 32 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-LIB`
- `REQ-LIB-COMMON-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `f481715192b4c3fbe5730c1bc69325bd6b64cd22b776409143fb0e6d8f54d174`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f481715192b4c3fbe5730c1bc69325bd6b64cd22b776409143fb0e6d8f54d174`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f481715192b4c3fbe5730c1bc69325bd6b64cd22b776409143fb0e6d8f54d174`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/common/net/http_core_adversarial_spec.spl
mirror: doc/06_spec/01_unit/lib/common/net/http_core_adversarial_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/net/http_core_adversarial_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/net/http_core_adversarial_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/net/http_core_adversarial_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/net/http_core_adversarial_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a valid lowercase hex chunk size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/net/http_core_adversarial_spec.spl:73:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a valid uppercase hex chunk size' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/net/http_core_adversarial_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty chunk-size field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
