# X25519mlkem768 Hrr Specification

> Tests covering TLS 1.3 X25519MLKEM768 HelloRetryRequest.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Hrr Specification

## Scenarios

### TLS 1.3 X25519MLKEM768 HelloRetryRequest

#### should REQ-005 constructs CH2 from an exact fresh hybrid share

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should REQ-005 constructs CH2 from an exact fresh hybrid share
- Create fresh X25519MLKEM768 state for ClientHello2
- Parse the emitted hybrid key share through the server parser
   - Expected: parsed.key_share_groups.len() equals `1`
   - Expected: parsed.x25519_mlkem768_key_share.len() equals `1216`
   - Expected: parsed.x25519_mlkem768_key_share[0] equals `fresh_share[0]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should REQ-005 constructs CH2 from an exact fresh hybrid share")
step("Create fresh X25519MLKEM768 state for ClientHello2")
val fresh_share = _hrr_octets(1216, 41)
val ch2 = match build_client_hello2_bytes_with_x25519_mlkem768(
        _hrr_octets(32, 7), fresh_share, "example.test", []):
    case Ok(value): value
    case Err(reason): fail(reason)
step("Parse the emitted hybrid key share through the server parser")
val parsed = process_client_hello(parse_handshake_header(ch2).body)
expect(parsed.key_share_groups.len()).to_equal(1)
expect(parsed.key_share_groups[0] == GROUP_X25519_MLKEM768).to_be(true)
expect(parsed.x25519_mlkem768_key_share.len()).to_equal(1216)
expect(parsed.x25519_mlkem768_key_share[0]).to_equal(fresh_share[0])
expect(parsed.x25519_mlkem768_key_share[1215]).to_equal(
    fresh_share[1215])
```

</details>

#### should REQ-004 rejects malformed hybrid CH2 material before encoding

- should REQ-004 rejects malformed hybrid CH2 material before encoding
- Reject a ClientHello2 hybrid share with the wrong length


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should REQ-004 rejects malformed hybrid CH2 material before encoding")
step("Reject a ClientHello2 hybrid share with the wrong length")
match build_client_hello2_bytes_with_x25519_mlkem768(
        _hrr_octets(32, 7), _hrr_octets(1215, 41),
        "example.test", []):
    case Ok(_): fail("malformed hybrid CH2 share was encoded")
    case Err(reason): expect(reason).to_contain("1216")
```

</details>

#### should REQ-005 rejects HRR selecting the hybrid share already sent in CH1

- should REQ-005 rejects HRR selecting the hybrid share already sent in CH1
- Receive an HRR that repeats the CH1 hybrid key-share group


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should REQ-005 rejects HRR selecting the hybrid share already sent in CH1")
step("Receive an HRR that repeats the CH1 hybrid key-share group")
val body = _hybrid_hrr_body()
val result = process_hrr_after_serverhello_with_x25519_mlkem768(
    _hybrid_hrr_handshake(body), body,
    _hrr_octets(32, 7), _hrr_octets(32, 17),
    _hrr_octets(32, 29), _hrr_octets(32, 33), [], [],
    "example.test", false, true, false, true, true)
match result:
    case HrrFlowResult.Ok(_):
        fail("same-group X25519MLKEM768 HRR was accepted")
    case HrrFlowResult.Reject(reason):
        expect(reason).to_contain("equals CH1 key_share group")
```

</details>

#### should REQ-004 rejects a hybrid HRR when CH1 did not support the group

- should REQ-004 rejects a hybrid HRR when CH1 did not support the group
- Reject an HRR group that ClientHello1 did not advertise


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should REQ-004 rejects a hybrid HRR when CH1 did not support the group")
step("Reject an HRR group that ClientHello1 did not advertise")
val body = _hybrid_hrr_body()
val result = process_hrr_after_serverhello_with_x25519_mlkem768(
    _hybrid_hrr_handshake(body), body,
    _hrr_octets(32, 7), _hrr_octets(32, 17),
    _hrr_octets(32, 29), _hrr_octets(32, 33), [],
    _hrr_octets(1216, 73), "example.test",
    false, true, false, false, false)
match result:
    case HrrFlowResult.Ok(_): fail("unoffered hybrid HRR was accepted")
    case HrrFlowResult.Reject(reason):
        expect(reason).to_contain("not in client supported_groups")
```

</details>

#### should REQ-005 accepts one hybrid HRR only with fresh 1216-byte state

- should REQ-005 accepts one hybrid HRR only with fresh 1216-byte state
- Accept one hybrid retry with a fresh exact-length key share
   - Expected: value.transcript_seed.len() equals `expected_seed_len`
   - Expected: parsed.x25519_mlkem768_key_share.len() equals `1216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("should REQ-005 accepts one hybrid HRR only with fresh 1216-byte state")
step("Accept one hybrid retry with a fresh exact-length key share")
val body = _hybrid_hrr_body()
val fresh_share = _hrr_octets(1216, 73)
val result = process_hrr_after_serverhello_with_x25519_mlkem768(
    _hybrid_hrr_handshake(body), body,
    _hrr_octets(32, 7), _hrr_octets(32, 17),
    _hrr_octets(32, 29), _hrr_octets(32, 33), [], fresh_share,
    "example.test", false, true, false, true, false)
match result:
    case HrrFlowResult.Reject(reason): fail(reason)
    case HrrFlowResult.Ok(value):
        expect(value.selected_group == GROUP_X25519_MLKEM768).to_be(true)
        val expected_seed_len = 36u64 + _hybrid_hrr_handshake(body).len()
        expect(value.transcript_seed.len()).to_equal(expected_seed_len)
        val parsed = process_client_hello(
            parse_handshake_header(value.client_hello2_bytes).body)
        expect(parsed.x25519_mlkem768_key_share.len()).to_equal(1216)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TLS 1.3 X25519MLKEM768 HelloRetryRequest.
- TLS 1.3 X25519MLKEM768 HelloRetryRequest

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
- `REQ-005`
- `REQ-004`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `2a9d21475f8de5bf7a3eadebfdf90fb2a33038ec0af8401b67f6a1578e201c10`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `2a9d21475f8de5bf7a3eadebfdf90fb2a33038ec0af8401b67f6a1578e201c10`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `2a9d21475f8de5bf7a3eadebfdf90fb2a33038ec0af8401b67f6a1578e201c10`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **82/100**; blockers: **0**.

SSpec documentization score: 82/100
source: test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl
mirror: doc/06_spec/01_unit/os/tls13/x25519mlkem768_hrr_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=75 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tls13/x25519mlkem768_hrr_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tls13/x25519mlkem768_hrr_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 3 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl:67:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-005 constructs CH2 from an exact fresh hybrid share' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should REQ-005 constructs CH2 from an exact fresh hybrid share' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl:85:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-004 rejects malformed hybrid CH2 material before encoding' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl:85:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should REQ-004 rejects malformed hybrid CH2 material before encoding' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-005 rejects HRR selecting the hybrid share already sent in CH1' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should REQ-005 rejects HRR selecting the hybrid share already sent in CH1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl:111:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-004 rejects a hybrid HRR when CH1 did not support the group' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/os/tls13/x25519mlkem768_hrr_spec.spl:127:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-005 accepts one hybrid HRR only with fresh 1216-byte state' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
