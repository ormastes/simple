# Text protocol evidence (E4)

> A client sends an HTTP-like request and a server replies. The text protocol

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Text protocol evidence (E4)

A client sends an HTTP-like request and a server replies. The text protocol

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/spec/evidence/text_protocol_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience

A client sends an HTTP-like request and a server replies. The text protocol
adapter turns that raw request/response transcript into typed evidence so the
existing fail-closed comparator can check it field by field, instead of a
reviewer eyeballing a pasted transcript. Audience: QA authors capturing
protocol traces and reviewers who must trust frame-level parsing and typed
projection without reading raw transcripts.

## Scenarios

### Text protocol format adapter

#### parses a request/response transcript and verifies it end to end

- parses a request/response transcript and verifies it end to end
   - Text capture: after_step
- Capture a LIST request and its response as a protocol trace
   - Text capture: after_step
- Convert the trace into canonical evidence
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: evidence.parse_ok is true
- Verify the transcript against a closed oracle
   - Text capture: after_step
   - Evidence: text output verified by 1 expected check
   - Expected: result.summary equals `7 check(s) passed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 25 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("parses a request/response transcript and verifies it end to end")
step("Capture a LIST request and its response as a protocol trace")
val trace = sample_trace()

step("Convert the trace into canonical evidence")
val evidence = trace_to_evidence(trace, "simple-list/1")
expect(evidence.parse_ok).to_equal(true)

step("Verify the transcript against a closed oracle")
val spec = oracle_spec(
    "simple-list/1",
    [
        check_exact("request.start_line", "LIST /projects HTTP/1.1"),
        check_exact("request.headers.accept", "text/plain"),
        check_full_pattern("request.headers.correlation-id", "hex:16"),
        check_exact("response.start_line", "HTTP/1.1 200 OK"),
        check_exact("response.status", "200"),
        check_full_pattern("response.headers.request-id", "hex:16"),
        check_ignore("response.headers.date", "server clock"),
        check_multiset("response.body.lines", ["alpha", "beta"])
    ]
)
val result = compare_evidence(evidence, spec)
expect(result.summary).to_equal("7 check(s) passed")
```

</details>

#### shows a directional transcript for the manual's narrative section

- shows a directional transcript for the manual's narrative section
- Project the trace as C -> S / S -> C lines
- Verify the first line of each frame is marked with its direction
   - Expected: lines[0] equals `C -> S  LIST /projects HTTP/1.1`
   - Expected: lines contains `S -> C  HTTP/1.1 200 OK`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("shows a directional transcript for the manual's narrative section")
step("Project the trace as C -> S / S -> C lines")
val lines = protocol_transcript_lines(sample_trace())

step("Verify the first line of each frame is marked with its direction")
expect(lines[0]).to_equal("C -> S  LIST /projects HTTP/1.1")
expect(lines.contains("S -> C  HTTP/1.1 200 OK")).to_equal(true)
```

</details>

#### keeps duplicate headers instead of overwriting them

- keeps duplicate headers instead of overwriting them
- Send a request with a header repeated twice
- Parse the frame and verify both occurrences survive
   - Expected: evidence.parse_ok is true
   - Expected: tag_values equals `["one", "two"]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("keeps duplicate headers instead of overwriting them")
step("Send a request with a header repeated twice")
val raw = "LIST /projects HTTP/1.1\r\nX-Tag: one\r\nX-Tag: two\r\n\r\n"

step("Parse the frame and verify both occurrences survive")
val evidence = parse_http_like_frame(raw, "request")
expect(evidence.parse_ok).to_equal(true)
var tag_values: [text] = []
for node in evidence.nodes:
    if node.path == "request.headers.x-tag":
        tag_values.push(node.value)
expect(tag_values).to_equal(["one", "two"])
```

</details>

#### retains the raw frame text even when comparison uses parsed nodes

- retains the raw frame text even when comparison uses parsed nodes
- Parse a simple response frame
- Verify each node's raw text matches its parsed value
   - Expected: evidence.nodes.len() > 0 is true
   - Expected: node.raw equals `node.value`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("retains the raw frame text even when comparison uses parsed nodes")
step("Parse a simple response frame")
val raw = "HTTP/1.1 204 No Content\r\n\r\n"
val evidence = parse_http_like_frame(raw, "response")

step("Verify each node's raw text matches its parsed value")
expect(evidence.nodes.len() > 0).to_equal(true)
for node in evidence.nodes:
    expect(node.raw).to_equal(node.value)
```

</details>

#### fails a frame missing the blank-line separator between headers and body

- fails a frame missing the blank-line separator between headers and body
- Send a frame whose headers never close with a blank line
- Verify the parser reports a parse error rather than a partial parse
   - Expected: evidence.parse_ok is false
   - Expected: evidence.nodes.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails a frame missing the blank-line separator between headers and body")
step("Send a frame whose headers never close with a blank line")
val raw = "LIST /projects HTTP/1.1\r\nAccept: text/plain\r\n"

step("Verify the parser reports a parse error rather than a partial parse")
val evidence = parse_http_like_frame(raw, "request")
expect(evidence.parse_ok).to_equal(false)
expect(evidence.nodes.len()).to_equal(0)
```

</details>

#### fails a header line with no colon

- fails a header line with no colon
- Send a frame with a malformed header line
- Verify the parser reports a parse error
   - Expected: evidence.parse_ok is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails a header line with no colon")
step("Send a frame with a malformed header line")
val raw = "LIST /projects HTTP/1.1\r\nAcceptTextPlain\r\n\r\n"

step("Verify the parser reports a parse error")
val evidence = parse_http_like_frame(raw, "request")
expect(evidence.parse_ok).to_equal(false)
```

</details>

#### fails the whole trace when either frame fails to parse

- fails the whole trace when either frame fails to parse
- Build a trace whose response frame is malformed
- Verify the trace-level evidence carries the parse failure
   - Expected: evidence.parse_ok is false
- Verify comparing malformed evidence fails closed, never a clean pass
   - Expected: result.status equals `EvidenceStatus.failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("fails the whole trace when either frame fails to parse")
step("Build a trace whose response frame is malformed")
val bad_trace = protocol_trace(
    "text",
    "conn-2",
    [
        protocol_frame(0, ProtocolDirection.client_to_server, "conn-2", "", sample_request(), "simple-list/1"),
        protocol_frame(1, ProtocolDirection.server_to_client, "conn-2", "", "HTTP/1.1 200 OK\r\nBroken\r\n", "simple-list/1")
    ]
)

step("Verify the trace-level evidence carries the parse failure")
val evidence = trace_to_evidence(bad_trace, "simple-list/1")
expect(evidence.parse_ok).to_equal(false)

step("Verify comparing malformed evidence fails closed, never a clean pass")
val spec = oracle_spec("simple-list/1", [check_exact("response.status", "200")])
val result = compare_evidence(evidence, spec)
expect(result.status).to_equal(EvidenceStatus.failed)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `b85c532299ceaea637592135344a773b360789093f09a5d2f699bf22ba9d246c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `b85c532299ceaea637592135344a773b360789093f09a5d2f699bf22ba9d246c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `b85c532299ceaea637592135344a773b360789093f09a5d2f699bf22ba9d246c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/common/spec/evidence/text_protocol_spec.spl
mirror: doc/06_spec/01_unit/lib/common/spec/evidence/text_protocol_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/spec/evidence/text_protocol_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/spec/evidence/text_protocol_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/spec/evidence/text_protocol_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/common/spec/evidence/text_protocol_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'shows a directional transcript for the manual's narrative section' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/text_protocol_spec.spl:101:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps duplicate headers instead of overwriting them' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/spec/evidence/text_protocol_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'retains the raw frame text even when comparison uses parsed nodes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
