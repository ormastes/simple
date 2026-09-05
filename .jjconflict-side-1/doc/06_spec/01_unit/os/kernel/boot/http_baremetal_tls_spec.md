# Http Baremetal Tls Specification

> Tests covering http_tls record framing, http_tls_session_from_context.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Http Baremetal Tls Specification

## Scenarios

### http_tls record framing

#### round-trips a plaintext buffer through encrypt then decrypt

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a plaintext buffer through encrypt then decrypt
   - Expected: send.record.len() > 5u64 is true
   - Expected: recv.ok is true
   - Expected: recv.content_type equals `23`
   - Expected: recv.data.len().to_u64() equals `3u64`
   - Expected: recv.data[0u64] equals `0x48u8`
   - Expected: recv.data[1u64] equals `0x49u8`
   - Expected: recv.data[2u64] equals `0x21u8`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("round-trips a plaintext buffer through encrypt then decrypt")
val send = http_tls_encrypt_app_record(_loopback_session(), _plaintext())
expect(send.record.len() > 5u64).to_equal(true)
val recv = http_tls_decrypt_app_record(_loopback_session(), send.record)
expect(recv.ok).to_equal(true)
# Real content type is application_data (0x17 = 23).
expect(recv.content_type).to_equal(23)
expect(recv.data.len().to_u64()).to_equal(3u64)
expect(recv.data[0u64]).to_equal(0x48u8)
expect(recv.data[1u64]).to_equal(0x49u8)
expect(recv.data[2u64]).to_equal(0x21u8)
```

</details>

#### advances server_seq on encrypt (return-the-object)

- advances server_seq on encrypt (return-the-object)
   - Expected: send.session.server_seq equals `1u64`
   - Expected: send.session.client_seq equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("advances server_seq on encrypt (return-the-object)")
val send = http_tls_encrypt_app_record(_loopback_session(), _plaintext())
expect(send.session.server_seq).to_equal(1u64)
expect(send.session.client_seq).to_equal(0u64)
```

</details>

#### advances client_seq on a successful decrypt

- advances client_seq on a successful decrypt
   - Expected: recv.session.client_seq equals `1u64`
   - Expected: recv.session.server_seq equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("advances client_seq on a successful decrypt")
val send = http_tls_encrypt_app_record(_loopback_session(), _plaintext())
val recv = http_tls_decrypt_app_record(_loopback_session(), send.record)
expect(recv.session.client_seq).to_equal(1u64)
expect(recv.session.server_seq).to_equal(0u64)
```

</details>

#### fails closed and leaves the sequence unchanged on a tampered record

- fails closed and leaves the sequence unchanged on a tampered record
   - Expected: recv.ok is false
   - Expected: recv.error != "" is true
   - Expected: recv.session.client_seq equals `0u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("fails closed and leaves the sequence unchanged on a tampered record")
val send = http_tls_encrypt_app_record(_loopback_session(), _plaintext())
# Flip a byte inside the ciphertext body (past the 5-byte header) so the
# AEAD tag check fails.
var bad: [u8] = []
var i: u64 = 0
while i < send.record.len():
    if i == 6u64:
        bad.push(send.record[i] ^ 0xFFu8)
    else:
        bad.push(send.record[i])
    i = i + 1u64
val recv = http_tls_decrypt_app_record(_loopback_session(), bad)
expect(recv.ok).to_equal(false)
expect(recv.error != "").to_equal(true)
expect(recv.session.client_seq).to_equal(0u64)
```

</details>

#### does not desync when two records are decrypted with a threaded session

- does not desync when two records are decrypted with a threaded session
   - Expected: r0.ok is true
   - Expected: r1.ok is true
   - Expected: r1.session.client_seq equals `2u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("does not desync when two records are decrypted with a threaded session")
# Server encrypts record #0 then record #1; a client tracking client_seq
# must decrypt both in order using the advanced session.
var srv = _loopback_session()
val s0 = http_tls_encrypt_app_record(srv, _plaintext())
srv = s0.session
val s1 = http_tls_encrypt_app_record(srv, _plaintext())
var cli = _loopback_session()
val r0 = http_tls_decrypt_app_record(cli, s0.record)
expect(r0.ok).to_equal(true)
cli = r0.session
val r1 = http_tls_decrypt_app_record(cli, s1.record)
expect(r1.ok).to_equal(true)
expect(r1.session.client_seq).to_equal(2u64)
```

</details>

### http_tls_session_from_context

#### maps application keys and sequence counters from a server context

- maps application keys and sequence counters from a server context
   - Expected: session.cipher_suite equals `0x1303u16`
   - Expected: session.client_seq equals `0u64`
   - Expected: session.server_seq equals `0u64`
   - Expected: session.server_key.key.len().to_u64() equals `16u64`
   - Expected: session.client_key.iv.len().to_u64() equals `12u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("maps application keys and sequence counters from a server context")
val ctx = Tls13ServerContext(
    cipher_suite: 0x1303u16,
    named_group: 0x001Du16,
    server_random: [],
    server_keyshare_pub: [],
    client_app_key: _key16(),
    client_app_iv: _iv12(),
    server_app_key: _key16(),
    server_app_iv: _iv12(),
    client_seq: 0u64,
    server_seq: 0u64
)
val session = http_tls_session_from_context(ctx)
expect(session.cipher_suite).to_equal(0x1303u16)
expect(session.client_seq).to_equal(0u64)
expect(session.server_seq).to_equal(0u64)
expect(session.server_key.key.len().to_u64()).to_equal(16u64)
expect(session.client_key.iv.len().to_u64()).to_equal(12u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/kernel/boot/http_baremetal_tls_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering http_tls record framing, http_tls_session_from_context.
- http_tls record framing
- http_tls_session_from_context

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `089844ecd2720c8f70c25ab82dbbc9faa6a91ac2a0c994fca8e38582ab3ae90b`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `089844ecd2720c8f70c25ab82dbbc9faa6a91ac2a0c994fca8e38582ab3ae90b`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `089844ecd2720c8f70c25ab82dbbc9faa6a91ac2a0c994fca8e38582ab3ae90b`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/kernel/boot/http_baremetal_tls_spec.spl
mirror: doc/06_spec/01_unit/os/kernel/boot/http_baremetal_tls_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/kernel/boot/http_baremetal_tls_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/kernel/boot/http_baremetal_tls_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/kernel/boot/http_baremetal_tls_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/kernel/boot/http_baremetal_tls_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a plaintext buffer through encrypt then decrypt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/http_baremetal_tls_spec.spl:92:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advances server_seq on encrypt (return-the-object)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/kernel/boot/http_baremetal_tls_spec.spl:99:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advances client_seq on a successful decrypt' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
