# H2 Server Resource Policy Specification

> Tests covering HTTP/2 server resource policy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# H2 Server Resource Policy Specification

## Scenarios

### HTTP/2 server resource policy

#### accepts the production limits and rejects invalid limits

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts the production limits and rejects invalid limits
   - Expected: h2_server_policy_error(policy) equals ``
   - Expected: policy.max_frame_payload equals `H2_DEFAULT_MAX_FRAME_PAYLOAD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("accepts the production limits and rejects invalid limits")
val policy = H2ServerPolicy.production()
expect(h2_server_policy_error(policy)).to_equal("")
expect(policy.max_frame_payload).to_equal(H2_DEFAULT_MAX_FRAME_PAYLOAD)
var invalid = H2ServerPolicy.production()
invalid.max_streams = 0
expect(h2_server_policy_error(invalid)).to_contain("max_streams must be positive")
invalid = H2ServerPolicy.production()
invalid.max_frame_payload = 16777216
expect(h2_server_policy_error(invalid)).to_contain("max_frame_payload")
```

</details>

#### bounds frame accumulation without integer-wrap arithmetic

- bounds frame accumulation without integer-wrap arithmetic


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("bounds frame accumulation without integer-wrap arithmetic")
expect(h2_accumulation_fits(8, 8, 16)).to_be(true)
expect(h2_accumulation_fits(8, 9, 16)).to_be(false)
expect(h2_accumulation_fits(17, 0, 16)).to_be(false)
expect(h2_accumulation_fits(-1, 1, 16)).to_be(false)
expect(h2_accumulation_fits(1, -1, 16)).to_be(false)
```

</details>

#### rejects fixed-size control frames with dishonest framing

- rejects fixed-size control frames with dishonest framing
   - Expected: h2_frame_protocol_error(8, 0, 1, 4) equals ``
   - Expected: h2_window_update_error([0, 0, 0, 1]) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects fixed-size control frames with dishonest framing")
expect(h2_frame_protocol_error(0, 0, 0, 0)).to_contain("stream zero")
expect(h2_frame_protocol_error(1, 4, 0, 0)).to_contain("stream zero")
expect(h2_frame_protocol_error(4, 1, 0, 6)).to_contain("acknowledgement")
expect(h2_frame_protocol_error(4, 0, 1, 0)).to_contain("stream identifier")
expect(h2_frame_protocol_error(6, 0, 0, 7)).to_contain("eight-byte")
expect(h2_frame_protocol_error(3, 0, 0, 4)).to_contain("requires a stream")
expect(h2_frame_protocol_error(8, 0, 1, 4)).to_equal("")
expect(h2_window_update_error([0, 0, 0, 0])).to_contain("nonzero")
expect(h2_window_update_error([0, 0, 0, 1])).to_equal("")
```

</details>

#### splits response DATA at the configured frame boundary

- splits response DATA at the configured frame boundary
   - Expected: h2_data_frame_count(0, 16384) equals `0`
   - Expected: h2_data_frame_count(16384, 16384) equals `1`
   - Expected: h2_data_frame_count(16385, 16384) equals `2`
   - Expected: h2_data_frame_count(32768, 16384) equals `2`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("splits response DATA at the configured frame boundary")
expect(h2_data_frame_count(0, 16384)).to_equal(0)
expect(h2_data_frame_count(16384, 16384)).to_equal(1)
expect(h2_data_frame_count(16385, 16384)).to_equal(2)
expect(h2_data_frame_count(32768, 16384)).to_equal(2)
```

</details>

#### filters hostile response headers and reclaims reset streams

- filters hostile response headers and reclaims reset streams
   - Expected: retained.streams.len() equals `1`
   - Expected: retained.streams[0].stream_id equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("filters hostile response headers and reclaims reset streams")
expect(h2_response_header_is_safe("x-trace-id", "safe")).to_be(true)
expect(h2_response_header_is_safe("connection", "keep-alive")).to_be(false)
expect(h2_response_header_is_safe("x-injected", "ok\r\nbad: yes")).to_be(false)
val session = H2ServerSession(conn: h2_connection_new(),
    streams: [h2_stream_entry_new(1), h2_stream_entry_new(3)],
    last_stream_id: 3, router: Router.new(), error: "")
val retained = h2_session_remove_stream(session, 1)
expect(retained.streams.len()).to_equal(1)
expect(retained.streams[0].stream_id).to_equal(3)
```

</details>

#### extracts HPACK bytes from padded and priority HEADERS envelopes

- extracts HPACK bytes from padded and priority HEADERS envelopes
   - Expected: h2_header_payload_error([2, 10, 11, 0, 0], 8) equals ``
   - Expected: h2_header_payload_fragment([2, 10, 11, 0, 0], 8) equals `[10, 11]`
   - Expected: h2_header_payload_error([0, 0, 0, 0, 0, 20, 21], 32) equals ``
   - Expected: h2_header_payload_fragment([0, 0, 0, 0, 0, 20, 21], 32) equals `[20, 21]`
   - Expected: h2_header_payload_error([1, 0, 0, 0, 0, 0, 30, 0], 40) equals ``
   - Expected: h2_header_payload_fragment([1, 0, 0, 0, 0, 0, 30, 0], 40) equals `[30]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("extracts HPACK bytes from padded and priority HEADERS envelopes")
expect(h2_header_payload_error([2, 10, 11, 0, 0], 8)).to_equal("")
expect(h2_header_payload_fragment([2, 10, 11, 0, 0], 8)).to_equal([10, 11])
expect(h2_header_payload_error([0, 0, 0, 0, 0, 20, 21], 32)).to_equal("")
expect(h2_header_payload_fragment([0, 0, 0, 0, 0, 20, 21], 32)).to_equal([20, 21])
expect(h2_header_payload_error([1, 0, 0, 0, 0, 0, 30, 0], 40)).to_equal("")
expect(h2_header_payload_fragment([1, 0, 0, 0, 0, 0, 30, 0], 40)).to_equal([30])
```

</details>

#### rejects malformed HEADERS envelopes before HPACK decoding

- rejects malformed HEADERS envelopes before HPACK decoding


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("rejects malformed HEADERS envelopes before HPACK decoding")
expect(h2_header_payload_error([], 8)).to_contain("padding length")
expect(h2_header_payload_error([0, 1, 2, 3, 4], 32)).to_contain("five-byte")
expect(h2_header_payload_error([3, 10, 0], 8)).to_contain("exceeds")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/http/h2/h2_server_resource_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HTTP/2 server resource policy.
- HTTP/2 server resource policy

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

- Canonical SPipe generation for source `703b0c78913d7dc39617e4fbaa8790ac0dbf592a880e669c66976662191a3049`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `703b0c78913d7dc39617e4fbaa8790ac0dbf592a880e669c66976662191a3049`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `703b0c78913d7dc39617e4fbaa8790ac0dbf592a880e669c66976662191a3049`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/http/h2/h2_server_resource_policy_spec.spl
mirror: doc/06_spec/01_unit/lib/http/h2/h2_server_resource_policy_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/http/h2/h2_server_resource_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/http/h2/h2_server_resource_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/http/h2/h2_server_resource_policy_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 6 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/http/h2/h2_server_resource_policy_spec.spl:27:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts the production limits and rejects invalid limits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http/h2/h2_server_resource_policy_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'bounds frame accumulation without integer-wrap arithmetic' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/http/h2/h2_server_resource_policy_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects fixed-size control frames with dishonest framing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
