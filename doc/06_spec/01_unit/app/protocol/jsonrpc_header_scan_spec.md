# JSON-RPC header part: unknown fields are skipped, never payload

> LSP 3.17 and the MCP stdio transport both define the message header as a

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# JSON-RPC header part: unknown fields are skipped, never payload

LSP 3.17 and the MCP stdio transport both define the message header as a

## At a Glance

| Field | Value |
|-------|-------|
| Category | Infrastructure |
| Status | Regression guard |
| Source | `test/01_unit/app/protocol/jsonrpc_header_scan_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and Audience

LSP 3.17 and the MCP stdio transport both define the message header as a
sequence of header FIELDS terminated by a blank line. `Content-Type` is a
defined field, vendor extensions are permitted, and a reader is required to
skip any field it does not recognise.

Two of this repo's stdio servers disagreed with that, in opposite directions:

- `src/app/t32_lsp_mcp/protocol.spl` treated any unrecognised header line as
  bare JSON-lines input and returned it as the message body. A client sending
  `Content-Type: application/vscode-jsonrpc; charset=utf-8` — which real VS
  Code does — had its header handed to the JSON parser as if it were a request.
- `src/app/lsp_mcp/main.spl` had no header loop at all: it read one line, then
  blindly consumed two more. An extra header dropped the message, and any body
  containing a newline was truncated.

This spec fixes the shared policy those loops must implement, as
`frame_scan_headers`.

The audience is anyone writing or reviewing a stdio read loop.

## Scope and Preconditions

Pure functions in `src/app/protocol/framing.spl` only; the per-server read
primitives (`input()` vs `stdin_read_char()`) are out of scope and are why the
loops cannot literally share code.

See doc/08_tracking/bug/jsonrpc_framing_divergence_2026-08-11.md

## Scenarios

### JSON-RPC header part scanning

#### reads the declared length from a minimal header

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reads the declared length from a minimal header
- A host sends only Content-Length, then the blank line
   - Expected: declared equals `42`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reads the declared length from a minimal header")
step("A host sends only Content-Length, then the blank line")
val declared = frame_scan_headers(["Content-Length: 42\r\n", "\r\n"])
expect(declared).to_equal(42)
```

</details>

#### skips a Content-Type header instead of treating it as payload

- skips a Content-Type header instead of treating it as payload
- Real VS Code sends Content-Type after Content-Length
- The unknown field is skipped and the declared length survives
   - Expected: frame_scan_headers(lines) equals `17`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("skips a Content-Type header instead of treating it as payload")
step("Real VS Code sends Content-Type after Content-Length")
val lines = [
    "Content-Length: 17\r\n",
    "Content-Type: application/vscode-jsonrpc; charset=utf-8\r\n",
    "\r\n",
]

step("The unknown field is skipped and the declared length survives")
expect(frame_scan_headers(lines)).to_equal(17)
```

</details>

#### skips a header that arrives BEFORE Content-Length

- skips a header that arrives BEFORE Content-Length
- Field order is not fixed by the spec
   - Expected: frame_scan_headers(lines) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("skips a header that arrives BEFORE Content-Length")
step("Field order is not fixed by the spec")
val lines = [
    "Content-Type: application/vscode-jsonrpc\r\n",
    "X-Vendor-Trace: abc123\r\n",
    "Content-Length: 9\r\n",
    "\r\n",
]
expect(frame_scan_headers(lines)).to_equal(9)
```

</details>

#### reports -1 when no Content-Length field was present

- reports -1 when no Content-Length field was present
- A header block with only unknown fields declares no body
   - Expected: frame_scan_headers(["Content-Type: text/plain\r\n", "\r\n"]) equals `-1`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("reports -1 when no Content-Length field was present")
step("A header block with only unknown fields declares no body")
expect(frame_scan_headers(["Content-Type: text/plain\r\n", "\r\n"])).to_equal(-1)
```

</details>

#### stops at the blank line and never scans the body

- stops at the blank line and never scans the body
- A body line that happens to look like a header must not be read
- The declared length is the header's 5, not the body's 99999
   - Expected: frame_scan_headers(lines) equals `5`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("stops at the blank line and never scans the body")
step("A body line that happens to look like a header must not be read")
val lines = [
    "Content-Length: 5\r\n",
    "\r\n",
    "Content-Length: 99999\r\n",
]

step("The declared length is the header's 5, not the body's 99999")
expect(frame_scan_headers(lines)).to_equal(5)
```

</details>

#### accepts bare LF line endings as well as CRLF

- accepts bare LF line endings as well as CRLF
- Some hosts emit LF-only headers
   - Expected: frame_scan_headers(["Content-Length: 8\n", "\n"]) equals `8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("accepts bare LF line endings as well as CRLF")
step("Some hosts emit LF-only headers")
expect(frame_scan_headers(["Content-Length: 8\n", "\n"])).to_equal(8)
```

</details>

#### declares the body length in BYTES, not characters

- declares the body length in BYTES, not characters
- A non-ASCII body has more bytes than characters
- The encoder's declared length matches what a byte reader must consume
   - Expected: declared equals `body.len()`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("declares the body length in BYTES, not characters")
step("A non-ASCII body has more bytes than characters")
val body = "{\"m\":\"héllo\"}"

step("The encoder's declared length matches what a byte reader must consume")
val framed = frame_encode(body)
val declared = frame_content_length_of(framed.split("\r\n")[0])
expect(declared).to_equal(body.len())
expect(declared).to_be_greater_than(0)
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
- `REQ-JSONRPC-FRAMING-002`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `21b006738c973f5204a47658d8e3636559a7b361b91df5ce34166aed1a336a15`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `21b006738c973f5204a47658d8e3636559a7b361b91df5ce34166aed1a336a15`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `21b006738c973f5204a47658d8e3636559a7b361b91df5ce34166aed1a336a15`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/protocol/jsonrpc_header_scan_spec.spl
mirror: doc/06_spec/01_unit/app/protocol/jsonrpc_header_scan_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/protocol/jsonrpc_header_scan_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/protocol/jsonrpc_header_scan_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/protocol/jsonrpc_header_scan_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/protocol/jsonrpc_header_scan_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/protocol/jsonrpc_header_scan_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reads the declared length from a minimal header' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/protocol/jsonrpc_header_scan_spec.spl:63:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips a Content-Type header instead of treating it as payload' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/protocol/jsonrpc_header_scan_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'skips a header that arrives BEFORE Content-Length' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
