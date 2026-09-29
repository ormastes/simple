# X25519mlkem768 Acceleration Specification

> Tests covering TLS 1.3 X25519MLKEM768 negotiation contract.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# X25519mlkem768 Acceleration Specification

## Scenarios

### TLS 1.3 X25519MLKEM768 negotiation contract

#### should REQ-005 uses the draft-05 NamedGroup code point

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should REQ-005 uses the draft-05 NamedGroup code point
- Load the shared X25519MLKEM768 fixture
   - Expected: GROUP_X25519_MLKEM768.to_i64() equals `0x11EC`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-005 uses the draft-05 NamedGroup code point")
step("Load the shared X25519MLKEM768 fixture")
expect(GROUP_X25519_MLKEM768.to_i64()).to_equal(0x11EC)
```

</details>

#### should REQ-005 accepts the exact 1216-byte client key share

- should REQ-005 accepts the exact 1216-byte client key share
- Negotiate the TLS 1.3 hybrid group


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-005 accepts the exact 1216-byte client key share")
step("Negotiate the TLS 1.3 hybrid group")
match tls13_validate_x25519_mlkem768_client_share(
        GROUP_X25519_MLKEM768, _octets(1216)):
    case Ok(valid): expect(valid).to_be(true)
    case Err(error): fail(error.reason)
```

</details>

#### should REQ-006 accepts the exact 1120-byte server key share

- should REQ-006 accepts the exact 1120-byte server key share
- Negotiate the TLS 1.3 hybrid group


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-006 accepts the exact 1120-byte server key share")
step("Negotiate the TLS 1.3 hybrid group")
match tls13_validate_x25519_mlkem768_server_share(
        GROUP_X25519_MLKEM768, _octets(1120)):
    case Ok(valid): expect(valid).to_be(true)
    case Err(error): fail(error.reason)
```

</details>

#### should REQ-004 NFR-013 maps a malformed client share to illegal_parameter

- should REQ-004 NFR-013 maps a malformed client share to illegal_parameter
- Negotiate the TLS 1.3 hybrid group


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-004 NFR-013 maps a malformed client share to illegal_parameter")
step("Negotiate the TLS 1.3 hybrid group")
match tls13_validate_x25519_mlkem768_client_share(
        GROUP_X25519_MLKEM768, _octets(1215)):
    case Ok(_): fail("malformed client share was accepted")
    case Err(error):
        expect(error.alert == TlsHybridAlert.IllegalParameter).to_be(true)
        expect(error.reason).to_contain("1216")
```

</details>

#### should REQ-004 NFR-013 maps a malformed server share to illegal_parameter

- should REQ-004 NFR-013 maps a malformed server share to illegal_parameter
- Validate the exact hybrid ServerHello key-share length


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-004 NFR-013 maps a malformed server share to illegal_parameter")
step("Validate the exact hybrid ServerHello key-share length")
match tls13_validate_x25519_mlkem768_server_share(
        GROUP_X25519_MLKEM768, _octets(1119)):
    case Ok(_): fail("malformed server share was accepted")
    case Err(error):
        expect(error.alert == TlsHybridAlert.IllegalParameter).to_be(true)
        expect(error.reason).to_contain("1120")
```

</details>

#### should REQ-004 rejects unexpected groups on both share directions

- should REQ-004 rejects unexpected groups on both share directions
- Validate the negotiated group on client and server shares


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-004 rejects unexpected groups on both share directions")
step("Validate the negotiated group on client and server shares")
match tls13_validate_x25519_mlkem768_client_share(
        0x001Du16, _octets(1216)):
    case Ok(_): fail("unexpected client group was accepted")
    case Err(error): expect(error.reason).to_contain("unexpected")
match tls13_validate_x25519_mlkem768_server_share(
        0x001Du16, _octets(1120)):
    case Ok(_): fail("unexpected server group was accepted")
    case Err(error): expect(error.reason).to_contain("unexpected")
```

</details>

#### should REQ-004 rejects obsolete experimental group identifiers

- should REQ-004 rejects obsolete experimental group identifiers
- Negotiate the TLS 1.3 hybrid group


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-004 rejects obsolete experimental group identifiers")
step("Negotiate the TLS 1.3 hybrid group")
match tls13_validate_x25519_mlkem768_client_share(
        0x2D00u16, _octets(1216)):
    case Ok(_): fail("obsolete hybrid group was accepted")
    case Err(error): expect(error.reason).to_contain("unexpected")
match tls13_validate_x25519_mlkem768_server_share(
        0x2D01u16, _octets(1120)):
    case Ok(_): fail("obsolete ML-KEM draft group was accepted")
    case Err(error): expect(error.reason).to_contain("unexpected")
```

</details>

#### should REQ-005 REQ-006 REQ-014 advertises and parses a hybrid ClientHello

- should REQ-005 REQ-006 REQ-014 advertises and parses a hybrid ClientHello
- Load the shared X25519MLKEM768 fixture
- Negotiate the TLS 1.3 hybrid group
   - Expected: parsed.x25519_mlkem768_key_share.len() equals `1216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-005 REQ-006 REQ-014 advertises and parses a hybrid ClientHello")
step("Load the shared X25519MLKEM768 fixture")
val encoded = match build_client_hello_bytes_with_x25519_mlkem768(
        _byte_octets(32, 1), _byte_octets(1216, 33),
        _byte_octets(32, 65), [], "example.test"):
    case Ok(value): value
    case Err(reason): fail(reason)
step("Negotiate the TLS 1.3 hybrid group")
val parsed = process_client_hello(parse_handshake_header(encoded).body)
expect(parsed.named_groups[0] == GROUP_X25519_MLKEM768).to_be(true)
expect(parsed.key_share_groups[0] == GROUP_X25519_MLKEM768).to_be(true)
expect(parsed.x25519_mlkem768_key_share.len()).to_equal(1216)
```

</details>

#### keeps REQ-014 REQ-017 NFR-018 hybrid parsing above a common TCP MSS

- keeps REQ-014 REQ-017 NFR-018 hybrid parsing above a common TCP MSS
- Build a large hybrid-first ClientHello without disabling ML-KEM
- Parse the large complete handshake at the protocol boundary
   - Expected: parsed.named_groups[0] equals `GROUP_X25519_MLKEM768`
   - Expected: parsed.key_share_groups[0] equals `GROUP_X25519_MLKEM768`
   - Expected: parsed.x25519_mlkem768_key_share.len() equals `1216`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("keeps REQ-014 REQ-017 NFR-018 hybrid parsing above a common TCP MSS")
step("Build a large hybrid-first ClientHello without disabling ML-KEM")
val encoded = match build_client_hello_bytes_with_x25519_mlkem768(
        _byte_octets(32, 1), _byte_octets(1216, 33),
        _byte_octets(32, 65), [], _long_server_name()):
    case Ok(value): value
    case Err(reason): fail(reason)
expect(encoded.len().to_i64()).to_be_greater_than(1460)

step("Parse the large complete handshake at the protocol boundary")
val parsed = process_client_hello(parse_handshake_header(encoded).body)
expect(parsed.named_groups[0]).to_equal(GROUP_X25519_MLKEM768)
expect(parsed.key_share_groups[0]).to_equal(GROUP_X25519_MLKEM768)
expect(parsed.x25519_mlkem768_key_share.len()).to_equal(1216)
```

</details>

#### should REQ-003 REQ-006 completes client decapsulation from ServerHello

- should REQ-003 REQ-006 completes client decapsulation from ServerHello
- Run the scalar CPU reference exchange


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-003 REQ-006 completes client decapsulation from ServerHello")
step("Run the scalar CPU reference exchange")
val config = x25519_mlkem768_default_config()
val client = match x25519_mlkem768_keygen(
        config, _byte_octets(32, 1), _list_octets(32, 33),
        _list_octets(32, 65)):
    case Ok(value): value
    case Err(reason): fail(reason)
val server = match x25519_mlkem768_encapsulate(
        config, client.client_key_share, _byte_octets(32, 97),
        _list_octets(32, 129)):
    case Ok(value): value
    case Err(reason): fail(reason)
val recovered = match tls13_decapsulate_x25519_mlkem768_server_hello(
        _server_hello_hybrid(
            server.server_key_share, GROUP_X25519_MLKEM768),
        config, client.x25519_private_key, client.decapsulation_key):
    case Ok(value): value
    case Err(error): fail(error.reason)
expect(_lists_equal(
    recovered.shared_secret, server.shared_secret)).to_be(true)
```

</details>

#### should REQ-004 REQ-016 maps all-zero X25519 output to illegal_parameter

- should REQ-004 REQ-016 maps all-zero X25519 output to illegal_parameter
- Reject a prohibited all-zero classical contribution


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-004 REQ-016 maps all-zero X25519 output to illegal_parameter")
step("Reject a prohibited all-zero classical contribution")
val config = x25519_mlkem768_default_config()
val client = match x25519_mlkem768_keygen(
        config, _byte_octets(32, 1), _list_octets(32, 33),
        _list_octets(32, 65)):
    case Ok(value): value
    case Err(reason): fail(reason)
val server = match x25519_mlkem768_encapsulate(
        config, client.client_key_share, _byte_octets(32, 97),
        _list_octets(32, 129)):
    case Ok(value): value
    case Err(reason): fail(reason)
var prohibited_share = server.server_key_share
var i: i64 = 1088
while i < 1120:
    prohibited_share[i] = 0
    i = i + 1
match tls13_decapsulate_x25519_mlkem768_server_hello(
        _server_hello_hybrid(prohibited_share, GROUP_X25519_MLKEM768),
        config, client.x25519_private_key, client.decapsulation_key):
    case Ok(_): fail("all-zero peer X25519 share was accepted")
    case Err(error):
        expect(error.alert == TlsHybridAlert.IllegalParameter).to_be(true)
        expect(error.reason).to_contain("all-zero")
```

</details>

#### should REQ-004 NFR-013 maps validation and decapsulation failures to alerts

- should REQ-004 NFR-013 maps validation and decapsulation failures to alerts
- Map hybrid validation failures to TLS alerts


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should REQ-004 NFR-013 maps validation and decapsulation failures to alerts")
step("Map hybrid validation failures to TLS alerts")
val config = x25519_mlkem768_default_config()
match tls13_decapsulate_x25519_mlkem768_server_hello(
        _server_hello_hybrid(_octets(1120), 0x001Du16),
        config, _byte_octets(32, 1), _octets(2400)):
    case Ok(_): fail("unexpected ServerHello group was accepted")
    case Err(error):
        expect(error.alert == TlsHybridAlert.IllegalParameter).to_be(true)
match tls13_decapsulate_x25519_mlkem768_server_hello(
        _server_hello_hybrid(
            _octets(1120), GROUP_X25519_MLKEM768),
        config, _byte_octets(32, 1), []):
    case Ok(_): fail("invalid ML-KEM decapsulation key was accepted")
    case Err(error):
        expect(error.alert == TlsHybridAlert.InternalError).to_be(true)
        expect(error.reason).to_contain("decapsulation key")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TLS 1.3 X25519MLKEM768 negotiation contract.
- TLS 1.3 X25519MLKEM768 negotiation contract

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

- `REQ-SSPEC-SYSTEM`
- `REQ-005`
- `REQ-006`
- `REQ-004`
- `REQ-014`
- `REQ-017`
- `REQ-003`
- `REQ-016`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4b3dbf9a86c6f5699e228f7266e63520457b28b186acb1585fd200d5b8c2c3e2`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4b3dbf9a86c6f5699e228f7266e63520457b28b186acb1585fd200d5b8c2c3e2`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4b3dbf9a86c6f5699e228f7266e63520457b28b186acb1585fd200d5b8c2c3e2`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **84/100**; effective score: **84/100**; blockers: **0**.

SSpec documentization score: 84/100
source: test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl
mirror: doc/06_spec/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.md (current)
findings: 12 blockers: 0
  narrative=100 structure=70 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:80:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-005 uses the draft-05 NamedGroup code point' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:80:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should REQ-005 uses the draft-05 NamedGroup code point' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:86:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-005 accepts the exact 1216-byte client key share' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:86:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should REQ-005 accepts the exact 1216-byte client key share' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:95:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-006 accepts the exact 1120-byte server key share' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should REQ-006 accepts the exact 1120-byte server key share' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:104:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-004 NFR-013 maps a malformed client share to illegal_parameter' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:115:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-004 NFR-013 maps a malformed server share to illegal_parameter' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/tls/feature/x25519mlkem768_acceleration_spec.spl:126:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should REQ-004 rejects unexpected groups on both share directions' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
