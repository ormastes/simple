# TLS 1.3 Client Authentication Codec Specification

> Exercises the pure handshake helpers added for TLS 1.3 client authentication:

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# TLS 1.3 Client Authentication Codec Specification

Exercises the pure handshake helpers added for TLS 1.3 client authentication:

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/03_system/os/os_tls_client_auth_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Exercises the pure handshake helpers added for TLS 1.3 client authentication:
- CertificateRequest parsing
- client Certificate encoding
- client CertificateVerify encoding

tag: slow, system, tls

## Scenarios

### tls13 client auth handshake helpers

#### parses CertificateRequest signature_algorithms

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses CertificateRequest signature_algorithms
   - Expected: req.request_context.len() equals `0`
   - Expected: req.sig_algs.len() equals `1`
   - Expected: req.sig_algs[0] equals `0x0807`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("parses CertificateRequest signature_algorithms")
val body = [
    0x00u8,
    0x00, 0x08,
    0x00, 0x0d,
    0x00, 0x04,
    0x00, 0x02,
    0x08, 0x07
]
val req = parse_certificate_request(body)
expect(req.request_context.len()).to_equal(0)
expect(req.sig_algs.len()).to_equal(1)
expect(req.sig_algs[0]).to_equal(0x0807)
```

</details>

#### builds an empty client Certificate message

- builds an empty client Certificate message
   - Expected: parsed.msg_type equals `11`
   - Expected: parsed.body[0] equals `0x00`
   - Expected: parsed.body[1] equals `0x00`
   - Expected: parsed.body[2] equals `0x00`
   - Expected: parsed.body[3] equals `0x00`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds an empty client Certificate message")
val msg = build_certificate_bytes([], [])
val parsed = parse_handshake_header(msg)
expect(parsed.msg_type).to_equal(11)
expect(parsed.body[0]).to_equal(0x00)
expect(parsed.body[1]).to_equal(0x00)
expect(parsed.body[2]).to_equal(0x00)
expect(parsed.body[3]).to_equal(0x00)
```

</details>

#### builds a non-empty client CertificateVerify message

- builds a non-empty client CertificateVerify message
   - Expected: parsed.msg_type equals `15`
   - Expected: parsed.body[0] equals `0x08`
   - Expected: parsed.body[1] equals `0x07`
   - Expected: parsed.body[2] equals `0x00`
   - Expected: parsed.body[3] equals `0x04`
   - Expected: parsed.body[4] equals `0xAA`
   - Expected: parsed.body[7] equals `0xDD`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("builds a non-empty client CertificateVerify message")
val sig = [0xAAu8, 0xBB, 0xCC, 0xDD]
val msg = build_certificate_verify_bytes(0x0807, sig)
val parsed = parse_handshake_header(msg)
expect(parsed.msg_type).to_equal(15)
expect(parsed.body[0]).to_equal(0x08)
expect(parsed.body[1]).to_equal(0x07)
expect(parsed.body[2]).to_equal(0x00)
expect(parsed.body[3]).to_equal(0x04)
expect(parsed.body[4]).to_equal(0xAA)
expect(parsed.body[7]).to_equal(0xDD)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9535294fcf2bef461f6913366c6b1b0fd9b90c28e6a6c552963d6cf69e3f5e1e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9535294fcf2bef461f6913366c6b1b0fd9b90c28e6a6c552963d6cf69e3f5e1e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9535294fcf2bef461f6913366c6b1b0fd9b90c28e6a6c552963d6cf69e3f5e1e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/03_system/os/os_tls_client_auth_spec.spl
mirror: doc/06_spec/03_system/os/os_tls_client_auth_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/os/os_tls_client_auth_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/os/os_tls_client_auth_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/os/os_tls_client_auth_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/os/os_tls_client_auth_spec.spl:26:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses CertificateRequest signature_algorithms' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_tls_client_auth_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds an empty client Certificate message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/os/os_tls_client_auth_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'builds a non-empty client CertificateVerify message' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
