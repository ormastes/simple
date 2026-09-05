# Websocket Facade Specification

> Tests covering nogc_async_mut websocket facade.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 1 | 1 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Websocket Facade Specification

## Scenarios

### nogc_async_mut websocket facade

#### re-exports runtime-safe websocket helpers

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- re-exports runtime-safe websocket helpers
   - Expected: OPCODE_TEXT equals `1`
   - Expected: is_text_frame(OPCODE_TEXT) equals `1`
   - Expected: is_control_frame(OPCODE_CLOSE) equals `1`
   - Expected: opcode_name(OPCODE_CLOSE) equals `Close`
   - Expected: validate_frame_structure(1, OPCODE_TEXT, 5) equals `1`
   - Expected: get_header_size(125, 0) equals `2`
   - Expected: base64_encode_byte(0) equals `A`
   - Expected: base64_encode_byte(-1) equals `/`
   - Expected: base64_encode_triple(72, 105, 33) equals `SGkh`
   - Expected: sha1_rotate_left(1, -1) equals `2147483648`
   - Expected: ws_bytes_to_text(invalid_bytes).length() equals `5`
   - Expected: request contains `Upgrade: websocket`
   - Expected: parse_upgrade_response("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n") equals `1`
   - Expected: close_status_name(CLOSE_NORMAL) equals `Normal Closure`
   - Expected: is_valid_close_status(CLOSE_NORMAL) equals `1`
   - Expected: frame_info(1, OPCODE_TEXT, 0, 2) equals `Frame: FIN | Text | UNMASKED | Payload: 2 bytes`
   - Expected: text_payload_length("Hi") equals `2`
   - Expected: split_into_chunks([1, 2, 3], 0).length() equals `0`
   - Expected: mask_payload([1, 2], []).length() equals `0`
   - Expected: create_frame(1, OPCODE_TEXT, 1, [1, 2], []).length() equals `0`
   - Expected: extract_mask_key([1, 2], 2, 1).length() equals `0`
   - Expected: extract_payload([1, 2], -1, 2, []).length() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-exports runtime-safe websocket helpers")
expect(OPCODE_TEXT).to_equal(1)
expect(is_text_frame(OPCODE_TEXT)).to_equal(1)
expect(is_control_frame(OPCODE_CLOSE)).to_equal(1)
expect(opcode_name(OPCODE_CLOSE)).to_equal("Close")
expect(validate_frame_structure(1, OPCODE_TEXT, 5)).to_equal(1)
expect(get_header_size(125, 0)).to_equal(2)

expect(base64_encode_byte(0)).to_equal("A")
expect(base64_encode_byte(-1)).to_equal("/")
expect(base64_encode_triple(72, 105, 33)).to_equal("SGkh")
expect(sha1_rotate_left(1, -1)).to_equal(2147483648)
var invalid_bytes = word_to_bytes(0x41424344)
invalid_bytes.push(-1)
expect(ws_bytes_to_text(invalid_bytes).length()).to_equal(5)

val request = build_upgrade_request("example.test", "/chat", "abc")
expect(request.contains("Upgrade: websocket")).to_equal(true)
expect(parse_upgrade_response("HTTP/1.1 101 Switching Protocols\r\nUpgrade: websocket\r\nConnection: Upgrade\r\n\r\n")).to_equal(1)

expect(close_status_name(CLOSE_NORMAL)).to_equal("Normal Closure")
expect(is_valid_close_status(CLOSE_NORMAL)).to_equal(1)

expect(frame_info(1, OPCODE_TEXT, 0, 2)).to_equal("Frame: FIN | Text | UNMASKED | Payload: 2 bytes")
expect(text_payload_length("Hi")).to_equal(2)
expect(split_into_chunks([1, 2, 3], 0).length()).to_equal(0)
expect(mask_payload([1, 2], []).length()).to_equal(0)
expect(create_frame(1, OPCODE_TEXT, 1, [1, 2], []).length()).to_equal(0)
expect(extract_mask_key([1, 2], 2, 1).length()).to_equal(0)
expect(extract_payload([1, 2], -1, 2, []).length()).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/nogc_async_mut/websocket/websocket_facade_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering nogc_async_mut websocket facade.
- nogc_async_mut websocket facade

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 1 |
| Active scenarios | 1 |
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

- Canonical SPipe generation for source `ac82321389aa50e0ecb978ae8161d08c2fba3f6ed315ffb8e535d54fed1c63a3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `ac82321389aa50e0ecb978ae8161d08c2fba3f6ed315ffb8e535d54fed1c63a3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `ac82321389aa50e0ecb978ae8161d08c2fba3f6ed315ffb8e535d54fed1c63a3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/unit/lib/nogc_async_mut/websocket/websocket_facade_spec.spl
mirror: doc/06_spec/unit/lib/nogc_async_mut/websocket/websocket_facade_spec.md (current)
findings: 4 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=90 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/nogc_async_mut/websocket/websocket_facade_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/nogc_async_mut/websocket/websocket_facade_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/nogc_async_mut/websocket/websocket_facade_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 15 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/nogc_async_mut/websocket/websocket_facade_spec.spl:18:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 're-exports runtime-safe websocket helpers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
