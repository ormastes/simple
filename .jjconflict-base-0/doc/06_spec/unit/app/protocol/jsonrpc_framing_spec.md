# JSON-RPC Content-Length Framing

> Every Simple language server that speaks over stdio -- the MCP server, the LSP

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JSON-RPC Content-Length Framing

Every Simple language server that speaks over stdio -- the MCP server, the LSP

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | In Progress |
| Source | `test/unit/app/protocol/jsonrpc_framing_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

Every Simple language server that speaks over stdio -- the MCP server, the LSP
bridges, the TRACE32 bridges, the DAP adapter -- wraps each JSON-RPC message in
an LSP-style `Content-Length:` header block. This specification fixes the
framing behaviour those servers share, so that an editor or agent host talking
to any of them sees the same wire behaviour.

The audience is anyone adding a new stdio server, or changing how an existing
one reads its input.

## Scope and Preconditions

This covers the pure framing primitives in `src/app/protocol/framing.spl`: the
header-line terminator strip, the decimal length parser, the Content-Length
header recogniser, and the outbound frame encoder. It does not cover the
per-server stdin read loops, which differ deliberately in their read primitive
and in whether they auto-detect bare JSON-lines input.

## Primary Workflow

A host writes `Content-Length: <n>`, a blank line, then `<n>` characters of JSON
body. The server reads header lines until the blank line, takes the declared
length from whichever line is the Content-Length header, and then reads exactly
that many characters. Replies are encoded the same way.

## Key Concepts

| Concept | Description |
|---------|-------------|
| Header block | Lines before the first blank line |
| Declared length | The number in the Content-Length header |
| Tolerant parse | A malformed header must never abort the server |

## Related Specifications

- `test/01_unit/app/mcp_unit/transport_tcp_spec.spl` -- the TCP transport variant

## Evidence and Provenance

Behaviour was read off the pre-merge implementations in `src/app/mcp/main.spl`
and `src/app/simple_lsp_mcp/json_helpers.spl`, which a byte-level diff showed to
be identical apart from function names. Divergent siblings are recorded in
`doc/08_tracking/bug/jsonrpc_framing_divergence_2026-08-11.md`.

## Recovery and Troubleshooting

A header the server cannot understand yields a zero or absent declared length;
the read loop then reports no message rather than reading a wrong number of
bytes off the stream. This is the deliberate failure mode: refuse the frame,
keep the stream position sane.

## Compatibility and Limitations

The declared length is counted in `text` characters, not UTF-8 bytes. For ASCII
JSON -- which is what these servers emit -- the two coincide. Non-ASCII bodies
are a known open gap and are not claimed here.

## Scenarios

### JSON-RPC Content-Length framing

#### reads the declared length from a well-formed header

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the declared length from a well-formed header
- a host sends a standard Content-Length header line
   - Expected: frame_content_length_of("Content-Length: 42\r\n") equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads the declared length from a well-formed header")
step("a host sends a standard Content-Length header line")
expect(frame_content_length_of("Content-Length: 42\r\n")).to_equal(42)
```

</details>

#### accepts a header line that arrived without its terminator

- accepts a header line that arrived without its terminator
- the reader hands over a line whose CRLF was already consumed
   - Expected: frame_content_length_of("Content-Length: 7") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a header line that arrived without its terminator")
step("the reader hands over a line whose CRLF was already consumed")
expect(frame_content_length_of("Content-Length: 7")).to_equal(7)
```

</details>

#### reports no length for a line that is not a Content-Length header

- reports no length for a line that is not a Content-Length header
- an unrelated header such as Content-Type arrives first
   - Expected: frame_content_length_of("Content-Type: application/json\r\n") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no length for a line that is not a Content-Length header")
step("an unrelated header such as Content-Type arrives first")
expect(frame_content_length_of("Content-Type: application/json\r\n")).to_equal(-1)
```

</details>

#### tolerates an extra vendor header without mistaking it for a length

- tolerates an extra vendor header without mistaking it for a length
- a vendor extension header appears in the block
   - Expected: frame_content_length_of("X-Simple-Trace: on\r\n") equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("tolerates an extra vendor header without mistaking it for a length")
step("a vendor extension header appears in the block")
expect(frame_content_length_of("X-Simple-Trace: on\r\n")).to_equal(-1)
```

</details>

#### treats a non-numeric length as zero rather than aborting

- treats a non-numeric length as zero rather than aborting
- a malformed header declares a word instead of a number
   - Expected: frame_content_length_of("Content-Length: abc\r\n") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("treats a non-numeric length as zero rather than aborting")
step("a malformed header declares a word instead of a number")
expect(frame_content_length_of("Content-Length: abc\r\n")).to_equal(0)
```

</details>

#### stops at the first non-digit in a partly numeric length

- stops at the first non-digit in a partly numeric length
- a length is corrupted mid-value
   - Expected: frame_content_length_of("Content-Length: 12x34\r\n") equals `12`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("stops at the first non-digit in a partly numeric length")
step("a length is corrupted mid-value")
expect(frame_content_length_of("Content-Length: 12x34\r\n")).to_equal(12)
```

</details>

#### reads an empty length as zero

- reads an empty length as zero
- the header names no value at all
   - Expected: frame_content_length_of("Content-Length:\r\n") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads an empty length as zero")
step("the header names no value at all")
expect(frame_content_length_of("Content-Length:\r\n")).to_equal(0)
```

</details>

#### accepts a length declared with no space after the colon

- accepts a length declared with no space after the colon
- a terse host omits the conventional space
   - Expected: frame_content_length_of("Content-Length:15\r\n") equals `15`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a length declared with no space after the colon")
step("a terse host omits the conventional space")
expect(frame_content_length_of("Content-Length:15\r\n")).to_equal(15)
```

</details>

#### removes a CRLF terminator without touching the rest of the line

- removes a CRLF terminator without touching the rest of the line
- a line ends in the protocol-standard CRLF
   - Expected: frame_strip_line_end("Content-Length: 3\r\n") equals `Content-Length: 3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a CRLF terminator without touching the rest of the line")
step("a line ends in the protocol-standard CRLF")
expect(frame_strip_line_end("Content-Length: 3\r\n")).to_equal("Content-Length: 3")
```

</details>

#### removes a lone LF terminator

- removes a lone LF terminator
- a Unix-style reader delivers only a newline
   - Expected: frame_strip_line_end("abc\n") equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a lone LF terminator")
step("a Unix-style reader delivers only a newline")
expect(frame_strip_line_end("abc\n")).to_equal("abc")
```

</details>

#### removes a lone CR terminator

- removes a lone CR terminator
- a split read delivers the CR without its LF
   - Expected: frame_strip_line_end("abc\r") equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes a lone CR terminator")
step("a split read delivers the CR without its LF")
expect(frame_strip_line_end("abc\r")).to_equal("abc")
```

</details>

#### leaves an unterminated line unchanged

- leaves an unterminated line unchanged
- the final line of a stream arrives with no terminator
   - Expected: frame_strip_line_end("abc") equals `abc`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves an unterminated line unchanged")
step("the final line of a stream arrives with no terminator")
expect(frame_strip_line_end("abc")).to_equal("abc")
```

</details>

#### removes only one terminator so a split read is not over-trimmed

- removes only one terminator so a split read is not over-trimmed
- a buffer boundary leaves two terminators stuck together
   - Expected: frame_strip_line_end("abc\n\n") equals `abc\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("removes only one terminator so a split read is not over-trimmed")
step("a buffer boundary leaves two terminators stuck together")
expect(frame_strip_line_end("abc\n\n")).to_equal("abc\n")
```

</details>

#### leaves an empty line empty

- leaves an empty line empty
- the blank line that closes the header block is stripped
   - Expected: frame_strip_line_end("") equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("leaves an empty line empty")
step("the blank line that closes the header block is stripped")
expect(frame_strip_line_end("")).to_equal("")
```

</details>

#### parses a bare decimal run

- parses a bare decimal run
- a length value is handed to the parser directly
   - Expected: frame_parse_decimal("2048") equals `2048`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a bare decimal run")
step("a length value is handed to the parser directly")
expect(frame_parse_decimal("2048")).to_equal(2048)
```

</details>

#### reads a leading zero without changing the value

- reads a leading zero without changing the value
- a host zero-pads the declared length
   - Expected: frame_parse_decimal("007") equals `7`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reads a leading zero without changing the value")
step("a host zero-pads the declared length")
expect(frame_parse_decimal("007")).to_equal(7)
```

</details>

#### yields zero for text with no leading digit

- yields zero for text with no leading digit
- the length field is entirely non-numeric
   - Expected: frame_parse_decimal("nope") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yields zero for text with no leading digit")
step("the length field is entirely non-numeric")
expect(frame_parse_decimal("nope")).to_equal(0)
```

</details>

#### yields zero for an empty length field

- yields zero for an empty length field
- the length field is empty
   - Expected: frame_parse_decimal("") equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yields zero for an empty length field")
step("the length field is empty")
expect(frame_parse_decimal("")).to_equal(0)
```

</details>

#### encodes a reply with a header, a blank line, and the body

- encodes a reply with a header, a blank line, and the body
- the server frames a JSON-RPC reply for the host
   - Expected: frame_encode("{}") equals `Content-Length: 2\r\n\r\n{}`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes a reply with a header, a blank line, and the body")
step("the server frames a JSON-RPC reply for the host")
expect(frame_encode("{}")).to_equal("Content-Length: 2\r\n\r\n{}")
```

</details>

#### declares a length that matches the body it encodes

- declares a length that matches the body it encodes
- the server frames a larger reply
   - Expected: frame_encode(body) equals `"Content-Length: " + str(body.len()) + "\r\n\r\n" + body`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declares a length that matches the body it encodes")
step("the server frames a larger reply")
val body = "{\"jsonrpc\":\"2.0\",\"id\":1}"
expect(frame_encode(body)).to_equal("Content-Length: " + str(body.len()) + "\r\n\r\n" + body)
```

</details>

#### encodes an empty body as a zero-length frame

- encodes an empty body as a zero-length frame
- the server has nothing to say but must still frame it
   - Expected: frame_encode("") equals `Content-Length: 0\r\n\r\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("encodes an empty body as a zero-length frame")
step("the server has nothing to say but must still frame it")
expect(frame_encode("")).to_equal("Content-Length: 0\r\n\r\n")
```

</details>

#### round-trips its own encoded header back to the declared length

- round-trips its own encoded header back to the declared length
- a frame the server emitted is parsed by the same primitives
   - Expected: frame_content_length_of(header) equals `body.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips its own encoded header back to the declared length")
step("a frame the server emitted is parsed by the same primitives")
val body = "{\"ok\":true}"
val header = frame_encode(body).split("\r\n")[0]
expect(frame_content_length_of(header)).to_equal(body.len())
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-JSONRPC-FRAMING-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `6738a44156f9e09bbb643d8193438085d04f94b2b85b98c0a7bf35ceac2c04cf`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6738a44156f9e09bbb643d8193438085d04f94b2b85b98c0a7bf35ceac2c04cf`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6738a44156f9e09bbb643d8193438085d04f94b2b85b98c0a7bf35ceac2c04cf`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/app/protocol/jsonrpc_framing_spec.spl
mirror: doc/06_spec/unit/app/protocol/jsonrpc_framing_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=90
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/unit/app/protocol/jsonrpc_framing_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
test/unit/app/protocol/jsonrpc_framing_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 12 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/protocol/jsonrpc_framing_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 1 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/app/protocol/jsonrpc_framing_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the declared length from a well-formed header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/protocol/jsonrpc_framing_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a header line that arrived without its terminator' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/protocol/jsonrpc_framing_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no length for a line that is not a Content-Length header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
