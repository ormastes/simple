# P256 Ecdhe Handshake Secret Specification

> Tests covering P-256 ephemeral pubkeys are 65-byte uncompressed SEC1 points, P-256 ECDHE produces a symmetric 32-byte shared X, tls13_compute_handshake_secrets fed with P-256 shared X, tls13_traffic_keys over P-256-derived handshake-traffic secrets.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# P256 Ecdhe Handshake Secret Specification

## Scenarios

### P-256 ephemeral pubkeys are 65-byte uncompressed SEC1 points

#### client pub is 65 bytes

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- client pub is 65 bytes
   - Expected: pub_c.len().to_u64() equals `65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("client pub is 65 bytes")
# Inline build of client scalar 0x31..0x50 (32 bytes BE).
var sc: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc.push((0x31u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc)
expect(pub_c.len().to_u64()).to_equal(65u64)
```

</details>

#### server pub is 65 bytes

- server pub is 65 bytes
   - Expected: pub_s.len().to_u64() equals `65u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("server pub is 65 bytes")
# Inline build of server scalar 0x91..0xb0 (32 bytes BE).
var sc: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc)
expect(pub_s.len().to_u64()).to_equal(65u64)
```

</details>

### P-256 ECDHE produces a symmetric 32-byte shared X

#### client_priv * server_pub yields 32 bytes

- client_priv * server_pub yields 32 bytes
   - Expected: sh_c.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("client_priv * server_pub yields 32 bytes")
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
expect(sh_c.len().to_u64()).to_equal(32u64)
```

</details>

#### server_priv * client_pub yields 32 bytes

- server_priv * client_pub yields 32 bytes
   - Expected: sh_s.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("server_priv * client_pub yields 32 bytes")
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
expect(sh_s.len().to_u64()).to_equal(32u64)
```

</details>

#### client and server agree byte-for-byte on shared X

- client and server agree byte-for-byte on shared X
   - Expected: equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("client and server agree byte-for-byte on shared X")
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
# Byte-equal check (avoid fn-call helper for the same regression
# surface; inline the loop).
var equal: bool = sh_c.len() == sh_s.len()
var j: u64 = 0u64
while equal and j < sh_c.len():
    if sh_c[j] != sh_s[j]:
        equal = false
    j = j + 1u64
expect(equal).to_equal(true)
```

</details>

### tls13_compute_handshake_secrets fed with P-256 shared X

#### yields 32-byte handshake_secret + 32-byte hs traffic secrets

- yields 32-byte handshake_secret + 32-byte hs traffic secrets
   - Expected: secrets.handshake_secret.len().to_u64() equals `32u64`
   - Expected: secrets.client_hs_traffic.len().to_u64() equals `32u64`
   - Expected: secrets.server_hs_traffic.len().to_u64() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("yields 32-byte handshake_secret + 32-byte hs traffic secrets")
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
# Build a synthetic transcript inline.
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t = transcript_new()
t = transcript_add(t, seed)
val secrets = tls13_compute_handshake_secrets(sh_c, t)
expect(secrets.handshake_secret.len().to_u64()).to_equal(32u64)
expect(secrets.client_hs_traffic.len().to_u64()).to_equal(32u64)
expect(secrets.server_hs_traffic.len().to_u64()).to_equal(32u64)
```

</details>

#### client and server derive byte-identical handshake_secret

- client and server derive byte-identical handshake_secret
   - Expected: equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("client and server derive byte-identical handshake_secret")
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t1 = transcript_new()
t1 = transcript_add(t1, seed)
var t2 = transcript_new()
t2 = transcript_add(t2, seed)
val secrets_c = tls13_compute_handshake_secrets(sh_c, t1)
val secrets_s = tls13_compute_handshake_secrets(sh_s, t2)
var equal: bool = secrets_c.handshake_secret.len() == secrets_s.handshake_secret.len()
var j: u64 = 0u64
while equal and j < secrets_c.handshake_secret.len():
    if secrets_c.handshake_secret[j] != secrets_s.handshake_secret[j]:
        equal = false
    j = j + 1u64
expect(equal).to_equal(true)
```

</details>

#### client and server derive byte-identical client_hs_traffic

- client and server derive byte-identical client_hs_traffic
   - Expected: equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("client and server derive byte-identical client_hs_traffic")
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t1 = transcript_new()
t1 = transcript_add(t1, seed)
var t2 = transcript_new()
t2 = transcript_add(t2, seed)
val secrets_c = tls13_compute_handshake_secrets(sh_c, t1)
val secrets_s = tls13_compute_handshake_secrets(sh_s, t2)
var equal: bool = secrets_c.client_hs_traffic.len() == secrets_s.client_hs_traffic.len()
var j: u64 = 0u64
while equal and j < secrets_c.client_hs_traffic.len():
    if secrets_c.client_hs_traffic[j] != secrets_s.client_hs_traffic[j]:
        equal = false
    j = j + 1u64
expect(equal).to_equal(true)
```

</details>

#### client and server derive byte-identical server_hs_traffic

- client and server derive byte-identical server_hs_traffic
   - Expected: equal is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 31 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("client and server derive byte-identical server_hs_traffic")
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_c = p256_keypair_pub(sc_c)
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
val sh_s = p256_ecdh_shared_x(sc_s, pub_c)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t1 = transcript_new()
t1 = transcript_add(t1, seed)
var t2 = transcript_new()
t2 = transcript_add(t2, seed)
val secrets_c = tls13_compute_handshake_secrets(sh_c, t1)
val secrets_s = tls13_compute_handshake_secrets(sh_s, t2)
var equal: bool = secrets_c.server_hs_traffic.len() == secrets_s.server_hs_traffic.len()
var j: u64 = 0u64
while equal and j < secrets_c.server_hs_traffic.len():
    if secrets_c.server_hs_traffic[j] != secrets_s.server_hs_traffic[j]:
        equal = false
    j = j + 1u64
expect(equal).to_equal(true)
```

</details>

### tls13_traffic_keys over P-256-derived handshake-traffic secrets

#### client AES-128 key is 16 bytes and IV is 12 bytes

- client AES-128 key is 16 bytes and IV is 12 bytes
   - Expected: tk.key.len().to_u64() equals `16u64`
   - Expected: tk.iv.len().to_u64() equals `12u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("client AES-128 key is 16 bytes and IV is 12 bytes")
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t = transcript_new()
t = transcript_add(t, seed)
val secrets = tls13_compute_handshake_secrets(sh_c, t)
val tk = tls13_traffic_keys(secrets.client_hs_traffic)
expect(tk.key.len().to_u64()).to_equal(16u64)
expect(tk.iv.len().to_u64()).to_equal(12u64)
```

</details>

#### server AES-128 key is 16 bytes and IV is 12 bytes

- server AES-128 key is 16 bytes and IV is 12 bytes
   - Expected: tk.key.len().to_u64() equals `16u64`
   - Expected: tk.iv.len().to_u64() equals `12u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("server AES-128 key is 16 bytes and IV is 12 bytes")
var sc_c: [u8] = []
var sc_s: [u8] = []
var i: u64 = 0u64
while i < 32u64:
    sc_c.push((0x31u8 + i.to_u8()))
    sc_s.push((0x91u8 + i.to_u8()))
    i = i + 1u64
val pub_s = p256_keypair_pub(sc_s)
val sh_c = p256_ecdh_shared_x(sc_c, pub_s)
var seed: [u8] = []
var k: u64 = 0u64
while k < 64u64:
    seed.push((k.to_u8() ^ 0x5au8))
    k = k + 1u64
var t = transcript_new()
t = transcript_add(t, seed)
val secrets = tls13_compute_handshake_secrets(sh_c, t)
val tk = tls13_traffic_keys(secrets.server_hs_traffic)
expect(tk.key.len().to_u64()).to_equal(16u64)
expect(tk.iv.len().to_u64()).to_equal(12u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering P-256 ephemeral pubkeys are 65-byte uncompressed SEC1 points, P-256 ECDHE produces a symmetric 32-byte shared X, tls13_compute_handshake_secrets fed with P-256 shared X, tls13_traffic_keys over P-256-derived handshake-traffic secrets.
- P-256 ephemeral pubkeys are 65-byte uncompressed SEC1 points
- P-256 ECDHE produces a symmetric 32-byte shared X
- tls13_compute_handshake_secrets fed with P-256 shared X
- tls13_traffic_keys over P-256-derived handshake-traffic secrets

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
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

- Canonical SPipe generation for source `61c45e265691ecf7da98ff6fe26143c5770b2b620b098d702ddb6e2769bf3192`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61c45e265691ecf7da98ff6fe26143c5770b2b620b098d702ddb6e2769bf3192`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61c45e265691ecf7da98ff6fe26143c5770b2b620b098d702ddb6e2769bf3192`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl
mirror: doc/06_spec/unit/os/tls13/p256_ecdhe_handshake_secret_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/tls13/p256_ecdhe_handshake_secret_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/tls13/p256_ecdhe_handshake_secret_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'client pub is 65 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'server pub is 65 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/tls13/p256_ecdhe_handshake_secret_spec.spl:94:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'client_priv * server_pub yields 32 bytes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
