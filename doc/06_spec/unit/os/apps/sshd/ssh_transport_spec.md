# Ssh Transport Specification

> Tests covering SSH transport KEXINIT parsing, SSH transport algorithm negotiation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 15 | 15 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Ssh Transport Specification

## Scenarios

### SSH transport KEXINIT parsing

#### parses a valid SSH version string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- parses a valid SSH version string
   - Expected: version.is_ok() is true
   - Expected: version.unwrap() equals `SSH-2.0-SimpleOS_1.0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses a valid SSH version string")
val version = ssh_parse_version_string(ssh_build_version_string())
expect(version.is_ok()).to_equal(true)
expect(version.unwrap()).to_equal("SSH-2.0-SimpleOS_1.0")
```

</details>

#### returns Err for a version string without CRLF

- returns Err for a version string without CRLF
   - Expected: version.is_err() is true
   - Expected: version.err() equals `no CRLF terminator in version string`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for a version string without CRLF")
val version = ssh_parse_version_string(_hex_decode("5353482d322e302d53696d706c654f535f312e30"))
expect(version.is_err()).to_equal(true)
expect(version.err()).to_equal("no CRLF terminator in version string")
```

</details>

#### returns Err for a non-SSH-2.0 version prefix

- returns Err for a non-SSH-2.0 version prefix
   - Expected: version.is_err() is true
   - Expected: version.err() equals `unsupported SSH version: SSH-1.5-Legacy`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for a non-SSH-2.0 version prefix")
val version = ssh_parse_version_string(_hex_decode("5353482d312e352d4c65676163790d0a"))
expect(version.is_err()).to_equal(true)
expect(version.err()).to_equal("unsupported SSH version: SSH-1.5-Legacy")
```

</details>

#### parses the canonical transport KEXINIT payload

- parses the canonical transport KEXINIT payload
   - Expected: parsed.is_ok() is true
   - Expected: kex.kex_algorithms equals `curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com`
   - Expected: kex.server_host_key_algorithms equals `ssh-ed25519,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256`
   - Expected: kex.encryption_client_to_server equals `aes256-gcm@openssh.com`
   - Expected: kex.encryption_server_to_client equals `aes256-gcm@openssh.com`
   - Expected: kex.mac_client_to_server equals `hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none`
   - Expected: kex.mac_server_to_client equals `hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none`
   - Expected: kex.compression_client_to_server equals `none`
   - Expected: kex.compression_server_to_client equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses the canonical transport KEXINIT payload")
val payload = ssh_build_kexinit()
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_ok()).to_equal(true)
val kex = parsed.unwrap()
expect(kex.kex_algorithms).to_equal("curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com")
expect(kex.server_host_key_algorithms).to_equal("ssh-ed25519,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256")
expect(kex.encryption_client_to_server).to_equal("aes256-gcm@openssh.com")
expect(kex.encryption_server_to_client).to_equal("aes256-gcm@openssh.com")
expect(kex.mac_client_to_server).to_equal("hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none")
expect(kex.mac_server_to_client).to_equal("hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none")
expect(kex.compression_client_to_server).to_equal("none")
expect(kex.compression_server_to_client).to_equal("none")
```

</details>

#### parses repeated canonical KEXINIT payloads consistently

- parses repeated canonical KEXINIT payloads consistently
   - Expected: parsed.is_ok() is true
   - Expected: parsed.unwrap().server_host_key_algorithms equals `ssh-ed25519,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("parses repeated canonical KEXINIT payloads consistently")
val payload = ssh_build_kexinit()
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_ok()).to_equal(true)
expect(parsed.unwrap().server_host_key_algorithms).to_equal("ssh-ed25519,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256")
```

</details>

#### returns Err for a KEXINIT with the wrong message type

- returns Err for a KEXINIT with the wrong message type
   - Expected: parsed.is_err() is true
   - Expected: parsed.err() equals `not a KEXINIT message`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for a KEXINIT with the wrong message type")
var payload = ssh_build_kexinit()
payload[0] = 21
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err()).to_equal("not a KEXINIT message")
```

</details>

#### returns Err for a truncated KEXINIT name-list

- returns Err for a truncated KEXINIT name-list
   - Expected: parsed.is_err() is true
   - Expected: parsed.err() equals `KEXINIT: bad comp_s2c`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for a truncated KEXINIT name-list")
val payload = ssh_build_kexinit()
var truncated: [u8] = []
var i: u64 = 0
while i + 8 < payload.len():
    truncated.push(payload[i])
    i = i + 1
val parsed = ssh_parse_kexinit(truncated)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err()).to_equal("KEXINIT: bad comp_s2c")
```

</details>

#### returns Err for a KEXINIT with trailing bytes after reserved

- returns Err for a KEXINIT with trailing bytes after reserved
   - Expected: parsed.is_err() is true
   - Expected: parsed.err() equals `KEXINIT: trailing bytes after reserved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for a KEXINIT with trailing bytes after reserved")
var payload = ssh_build_kexinit()
payload.push(0xAA)
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err()).to_equal("KEXINIT: trailing bytes after reserved")
```

</details>

#### returns Err for a KEXINIT with a truncated reserved field

- returns Err for a KEXINIT with a truncated reserved field
   - Expected: parsed.is_err() is true
   - Expected: parsed.err() equals `KEXINIT: truncated reserved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for a KEXINIT with a truncated reserved field")
var payload = ssh_build_kexinit()
payload.pop()
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err()).to_equal("KEXINIT: truncated reserved")
```

</details>

#### returns Err for a KEXINIT with a non-zero reserved field

- returns Err for a KEXINIT with a non-zero reserved field
   - Expected: parsed.is_err() is true
   - Expected: parsed.err() equals `KEXINIT: non-zero reserved`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err for a KEXINIT with a non-zero reserved field")
var payload = ssh_build_kexinit()
val reserved_offset = payload.len() - 4
payload[reserved_offset + 3] = 1
val parsed = ssh_parse_kexinit(payload)
expect(parsed.is_err()).to_equal(true)
expect(parsed.err()).to_equal("KEXINIT: non-zero reserved")
```

</details>

### SSH transport algorithm negotiation

#### honors client preference order for host key algorithms

- honors client preference order for host key algorithms
   - Expected: negotiated.is_ok() is true
   - Expected: algos.host_key equals `ecdsa-sha2-nistp256`
   - Expected: algos.kex equals `curve25519-sha256`
   - Expected: algos.cipher_c2s equals `aes128-gcm@openssh.com`
   - Expected: algos.cipher_s2c equals `aes128-gcm@openssh.com`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("honors client preference order for host key algorithms")
val client = _kex_init(
    "curve25519-sha256",
    "ecdsa-sha2-nistp256,ssh-ed25519,rsa-sha2-256",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519,ecdsa-sha2-nistp256",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_ok()).to_equal(true)
val algos = negotiated.unwrap()
expect(algos.host_key).to_equal("ecdsa-sha2-nistp256")
expect(algos.kex).to_equal("curve25519-sha256")
expect(algos.cipher_c2s).to_equal("aes128-gcm@openssh.com")
expect(algos.cipher_s2c).to_equal("aes128-gcm@openssh.com")
```

</details>

#### falls back to ssh-ed25519 when stronger client preferences are unavailable

- falls back to ssh-ed25519 when stronger client preferences are unavailable
   - Expected: negotiated.is_ok() is true
   - Expected: negotiated.unwrap().host_key equals `ssh-ed25519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls back to ssh-ed25519 when stronger client preferences are unavailable")
val client = _kex_init(
    "curve25519-sha256",
    "rsa-sha2-512,ecdsa-sha2-nistp256,ssh-ed25519",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_ok()).to_equal(true)
expect(negotiated.unwrap().host_key).to_equal("ssh-ed25519")
```

</details>

#### accepts OpenSSH MAC lists when AES-GCM is negotiated

- accepts OpenSSH MAC lists when AES-GCM is negotiated
   - Expected: negotiated.is_ok() is true
   - Expected: algos.cipher_c2s equals `aes128-gcm@openssh.com`
   - Expected: algos.cipher_s2c equals `aes128-gcm@openssh.com`
   - Expected: algos.mac_c2s equals `none`
   - Expected: algos.mac_s2c equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts OpenSSH MAC lists when AES-GCM is negotiated")
val client = _kex_init(
    "curve25519-sha256",
    "ssh-ed25519,rsa-sha2-256",
    "chacha20-poly1305@openssh.com,aes128-gcm@openssh.com",
    "chacha20-poly1305@openssh.com,aes128-gcm@openssh.com",
    "umac-64-etm@openssh.com,umac-128-etm@openssh.com,hmac-sha2-256",
    "umac-64-etm@openssh.com,umac-128-etm@openssh.com,hmac-sha2-256",
    "none,zlib@openssh.com",
    "none,zlib@openssh.com"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none",
    "hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_ok()).to_equal(true)
val algos = negotiated.unwrap()
expect(algos.cipher_c2s).to_equal("aes128-gcm@openssh.com")
expect(algos.cipher_s2c).to_equal("aes128-gcm@openssh.com")
expect(algos.mac_c2s).to_equal("none")
expect(algos.mac_s2c).to_equal("none")
```

</details>

#### prefers aes256-gcm when both peers advertise it

- prefers aes256-gcm when both peers advertise it
   - Expected: negotiated.is_ok() is true
   - Expected: algos.cipher_c2s equals `aes256-gcm@openssh.com`
   - Expected: algos.cipher_s2c equals `aes256-gcm@openssh.com`
   - Expected: algos.mac_c2s equals `none`
   - Expected: algos.mac_s2c equals `none`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers aes256-gcm when both peers advertise it")
val client = _kex_init(
    "curve25519-sha256",
    "ssh-ed25519",
    "aes256-gcm@openssh.com,aes128-gcm@openssh.com,aes256-ctr",
    "aes256-gcm@openssh.com,aes128-gcm@openssh.com,aes256-ctr",
    "none",
    "none",
    "none",
    "none"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519",
    "aes256-gcm@openssh.com,aes128-gcm@openssh.com,aes256-ctr",
    "aes256-gcm@openssh.com,aes128-gcm@openssh.com,aes256-ctr",
    "hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none",
    "hmac-sha2-512-etm@openssh.com,hmac-sha2-256-etm@openssh.com,none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_ok()).to_equal(true)
val algos = negotiated.unwrap()
expect(algos.cipher_c2s).to_equal("aes256-gcm@openssh.com")
expect(algos.cipher_s2c).to_equal("aes256-gcm@openssh.com")
expect(algos.mac_c2s).to_equal("none")
expect(algos.mac_s2c).to_equal("none")
```

</details>

#### returns Err when the client and server share no host key algorithm

- returns Err when the client and server share no host key algorithm
   - Expected: negotiated.is_err() is true
   - Expected: negotiated.err() equals `no matching host key algorithm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns Err when the client and server share no host key algorithm")
val client = _kex_init(
    "curve25519-sha256",
    "rsa-sha2-256,rsa-sha2-512",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)
val server = _kex_init(
    "curve25519-sha256,ext-info-s,kex-strict-s-v00@openssh.com",
    "ssh-ed25519",
    "aes128-gcm@openssh.com",
    "aes128-gcm@openssh.com",
    "none",
    "none",
    "none",
    "none"
)

val negotiated = ssh_negotiate_algorithms(client, server)
expect(negotiated.is_err()).to_equal(true)
expect(negotiated.err()).to_equal("no matching host key algorithm")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/unit/os/apps/sshd/ssh_transport_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSH transport KEXINIT parsing, SSH transport algorithm negotiation.
- SSH transport KEXINIT parsing
- SSH transport algorithm negotiation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 15 |
| Active scenarios | 15 |
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

- Canonical SPipe generation for source `59cf636344b000540c79ee58c3be5424f10f64a2c9f0aec449cc6e0f87816731`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `59cf636344b000540c79ee58c3be5424f10f64a2c9f0aec449cc6e0f87816731`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `59cf636344b000540c79ee58c3be5424f10f64a2c9f0aec449cc6e0f87816731`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/os/apps/sshd/ssh_transport_spec.spl
mirror: doc/06_spec/unit/os/apps/sshd/ssh_transport_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/os/apps/sshd/ssh_transport_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/os/apps/sshd/ssh_transport_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/os/apps/sshd/ssh_transport_spec.spl:40:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'parses a valid SSH version string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/sshd/ssh_transport_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Err for a version string without CRLF' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/os/apps/sshd/ssh_transport_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns Err for a non-SSH-2.0 version prefix' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
