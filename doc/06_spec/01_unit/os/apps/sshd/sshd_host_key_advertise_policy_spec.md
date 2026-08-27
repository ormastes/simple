# Sshd Host Key Advertise Policy Specification

> Tests covering SSHD host key advertisement follows config, SSHD host key policy fails closed, SSHD startup itself is gated by the host key policy, SSHD never negotiates a disabled host key algorithm, SSHD certificate-aware host key list follows config.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 22 | 22 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sshd Host Key Advertise Policy Specification

## Scenarios

### SSHD host key advertisement follows config

#### advertises ssh-ed25519 when the config enables it

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- advertises ssh-ed25519 when the config enables it
   - Expected: host_key_set_advertised_algorithms(keys) equals `ssh-ed25519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advertises ssh-ed25519 when the config enables it")
val keys = sshd_build_host_keys_for_session_for_test(true, _seed32(), nil, nil, nil)
expect(host_key_set_advertised_algorithms(keys)).to_equal("ssh-ed25519")
```

</details>

#### never advertises ssh-ed25519 when the config disables it

- never advertises ssh-ed25519 when the config disables it
   - Expected: host_key_set_advertised_algorithms(keys) equals ``
   - Expected: host_key_set_advertised_algorithms(keys) does not contain `ssh-ed25519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never advertises ssh-ed25519 when the config disables it")
val keys = sshd_build_host_keys_for_session_for_test(false, _seed32(), nil, nil, nil)
# Absolute oracle: the disabled algorithm must be absent from the list.
expect(host_key_set_advertised_algorithms(keys)).to_equal("")
expect(host_key_set_advertised_algorithms(keys).contains("ssh-ed25519")).to_equal(false)
```

</details>

#### advertises only the remaining enabled algorithm when ed25519 is disabled

- advertises only the remaining enabled algorithm when ed25519 is disabled
   - Expected: algos equals `rsa-sha2-256,rsa-sha2-512`
   - Expected: algos does not contain `ssh-ed25519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advertises only the remaining enabled algorithm when ed25519 is disabled")
val keys = sshd_build_host_keys_for_session_for_test(false, _seed32(), [0x30u8, 0x82u8], nil, nil)
val algos = host_key_set_advertised_algorithms(keys)
expect(algos).to_equal("rsa-sha2-256,rsa-sha2-512")
expect(algos.contains("ssh-ed25519")).to_equal(false)
```

</details>

#### advertises ecdsa alone when only ecdsa is configured

- advertises ecdsa alone when only ecdsa is configured
   - Expected: algos equals `ecdsa-sha2-nistp256`
   - Expected: algos does not contain `ssh-ed25519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("advertises ecdsa alone when only ecdsa is configured")
val keys = sshd_build_host_keys_for_session_for_test(false, _seed32(), nil, nil, [0x30u8, 0x77u8])
val algos = host_key_set_advertised_algorithms(keys)
expect(algos).to_equal("ecdsa-sha2-nistp256")
expect(algos.contains("ssh-ed25519")).to_equal(false)
```

</details>

### SSHD host key policy fails closed

#### reports no algorithm available when every host key is disabled

- reports no algorithm available when every host key is disabled
   - Expected: host_key_set_has_any_algorithm(keys) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no algorithm available when every host key is disabled")
val keys = sshd_build_host_keys_for_session_for_test(false, _seed32(), nil, nil, nil)
expect(host_key_set_has_any_algorithm(keys)).to_equal(false)
```

</details>

#### reports an algorithm available when ed25519 is enabled

- reports an algorithm available when ed25519 is enabled
   - Expected: host_key_set_has_any_algorithm(keys) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports an algorithm available when ed25519 is enabled")
val keys = sshd_build_host_keys_for_session_for_test(true, _seed32(), nil, nil, nil)
expect(host_key_set_has_any_algorithm(keys)).to_equal(true)
```

</details>

#### refuses to serve when the config leaves no host key algorithm enabled

- refuses to serve when the config leaves no host key algorithm enabled
   - Expected: sshd_host_key_policy_satisfiable_for_test(false, _seed32(), nil, nil, nil) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to serve when the config leaves no host key algorithm enabled")
expect(sshd_host_key_policy_satisfiable_for_test(false, _seed32(), nil, nil, nil)).to_equal(false)
```

</details>

#### serves when at least one host key algorithm remains enabled

- serves when at least one host key algorithm remains enabled
   - Expected: sshd_host_key_policy_satisfiable_for_test(true, _seed32(), nil, nil, nil) is true
   - Expected: sshd_host_key_policy_satisfiable_for_test(false, _seed32(), [0x30u8], nil, nil) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serves when at least one host key algorithm remains enabled")
expect(sshd_host_key_policy_satisfiable_for_test(true, _seed32(), nil, nil, nil)).to_equal(true)
expect(sshd_host_key_policy_satisfiable_for_test(false, _seed32(), [0x30u8], nil, nil)).to_equal(true)
```

</details>

#### serves on a certificate alone when the raw key is disabled

- serves on a certificate alone when the raw key is disabled
   - Expected: sshd_host_key_policy_satisfiable_for_test(false, _seed32(), nil, nil, [0x00u8, 0x01u8]) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("serves on a certificate alone when the raw key is disabled")
expect(sshd_host_key_policy_satisfiable_for_test(false, _seed32(), nil, nil, [0x00u8, 0x01u8])).to_equal(true)
```

</details>

### SSHD startup itself is gated by the host key policy

#### refuses to start when no host key algorithm is enabled

- refuses to start when no host key algorithm is enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to start when no host key algorithm is enabled")
# Absolute oracle: start() must hand back the refusal Err, and must do
# so BEFORE binding a listener. Reaching the bind is itself the failure
# signal here — rt_boot_tcp_bind is a baremetal-only extern, so an
# unguarded start() dies on it rather than returning this text.
expect(sshd_start_verdict_for_test(false, _seed32(), nil, nil, nil))
    .to_equal("sshd: no host key algorithm enabled")
```

</details>

#### still refuses when ed25519 is disabled and no other key or cert is set

- still refuses when ed25519 is disabled and no other key or cert is set


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("still refuses when ed25519 is disabled and no other key or cert is set")
expect(sshd_start_verdict_for_test(false, _seed32(), nil, nil, nil).contains("no host key algorithm"))
    .to_equal(true)
```

</details>

#### does not refuse a daemon that still has ed25519 enabled

- does not refuse a daemon that still has ed25519 enabled


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not refuse a daemon that still has ed25519 enabled")
# Success half of the gate, evaluated on a real SshDaemon. start()
# cannot be run to completion on a host interpreter once the gate
# passes (it proceeds into the baremetal rt_boot_tcp_bind), so this
# asserts the very verdict start() branches on.
expect(sshd_daemon_host_key_policy_satisfiable_for_test(true, _seed32(), nil, nil, nil))
    .to_equal(true)
```

</details>

#### does not refuse a daemon carrying only a host certificate

- does not refuse a daemon carrying only a host certificate


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does not refuse a daemon carrying only a host certificate")
expect(sshd_daemon_host_key_policy_satisfiable_for_test(false, _seed32(), nil, nil, [0x00u8, 0x01u8]))
    .to_equal(true)
```

</details>

#### refuses a daemon whose only configured key is one this lane never advertises

- refuses a daemon whose only configured key is one this lane never advertises


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses a daemon whose only configured key is one this lane never advertises")
# Divergence pinned deliberately, and it is the fail-closed direction:
# build_host_keys_for_session() hardcodes rsa_pkcs8/ecdsa to nil because
# the live lane stays on the Ed25519/X25519 surface. So an RSA-only or
# ECDSA-only configuration leaves NOTHING advertisable and start() must
# refuse — even though the pure-policy hook above, which trusts the
# passed-in key material, reports such a config satisfiable.
expect(sshd_daemon_host_key_policy_satisfiable_for_test(false, _seed32(), [0x30u8], nil, nil))
    .to_equal(false)
expect(sshd_daemon_host_key_policy_satisfiable_for_test(false, _seed32(), nil, [0x30u8], nil))
    .to_equal(false)
expect(sshd_start_verdict_for_test(false, _seed32(), [0x30u8], nil, nil))
    .to_equal("sshd: no host key algorithm enabled")
```

</details>

### SSHD never negotiates a disabled host key algorithm

#### negotiates ssh-ed25519 when the config enables it

- negotiates ssh-ed25519 when the config enables it
   - Expected: negotiated.is_ok() is true
   - Expected: negotiated.unwrap().host_key equals `ssh-ed25519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negotiates ssh-ed25519 when the config enables it")
# Positive control: the same client proposal succeeds when enabled, so a
# failure below is attributable to the gate and not to the harness.
val negotiated = ssh_negotiate_algorithms(
    _client_kexinit("ssh-ed25519"),
    _server_kexinit(true, nil)
)
expect(negotiated.is_ok()).to_equal(true)
expect(negotiated.unwrap().host_key).to_equal("ssh-ed25519")
```

</details>

#### refuses the exchange when the client offers only the disabled algorithm

- refuses the exchange when the client offers only the disabled algorithm
   - Expected: negotiated.is_ok() is false
   - Expected: negotiated.unwrap_err() equals `no matching host key algorithm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses the exchange when the client offers only the disabled algorithm")
# Security oracle: a disabled algorithm must be unreachable, not merely
# unadvertised — negotiation fails closed rather than selecting it.
val negotiated = ssh_negotiate_algorithms(
    _client_kexinit("ssh-ed25519"),
    _server_kexinit(false, [0x30u8, 0x82u8])
)
expect(negotiated.is_ok()).to_equal(false)
expect(negotiated.unwrap_err()).to_equal("no matching host key algorithm")
```

</details>

#### falls through to an enabled algorithm instead of the disabled one

- falls through to an enabled algorithm instead of the disabled one
   - Expected: negotiated.is_ok() is true
   - Expected: negotiated.unwrap().host_key equals `rsa-sha2-256`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("falls through to an enabled algorithm instead of the disabled one")
# The client prefers ssh-ed25519; the daemon must skip it and land on RSA
# rather than honouring client preference for a switched-off key.
val negotiated = ssh_negotiate_algorithms(
    _client_kexinit("ssh-ed25519,rsa-sha2-256"),
    _server_kexinit(false, [0x30u8, 0x82u8])
)
expect(negotiated.is_ok()).to_equal(true)
expect(negotiated.unwrap().host_key).to_equal("rsa-sha2-256")
```

</details>

#### refuses every exchange when no host key algorithm is enabled

- refuses every exchange when no host key algorithm is enabled
   - Expected: negotiated.is_ok() is false
   - Expected: negotiated.unwrap_err() equals `no matching host key algorithm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses every exchange when no host key algorithm is enabled")
# No key material at all: the daemon must not fall back to a default.
val negotiated = ssh_negotiate_algorithms(
    _client_kexinit("ssh-ed25519,rsa-sha2-256,rsa-sha2-512,ecdsa-sha2-nistp256"),
    _server_kexinit(false, nil)
)
expect(negotiated.is_ok()).to_equal(false)
expect(negotiated.unwrap_err()).to_equal("no matching host key algorithm")
```

</details>

#### refuses ssh-ed25519 against the real accepted-session KEXINIT when disabled

- refuses ssh-ed25519 against the real accepted-session KEXINIT when disabled
   - Expected: server.server_host_key_algorithms does not contain `ssh-ed25519`
   - Expected: negotiated.is_ok() is false
   - Expected: negotiated.unwrap_err() equals `no matching host key algorithm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses ssh-ed25519 against the real accepted-session KEXINIT when disabled")
# Same oracle, but against the bytes a live accepted session would send:
# parse the production KEXINIT rather than a reconstructed list.
val payload = sshd_build_production_session_kexinit_for_test(
    false, _seed32(), nil, nil, nil, nil, nil, nil
)
val server = ssh_parse_kexinit(payload).unwrap()
expect(server.server_host_key_algorithms.contains("ssh-ed25519")).to_equal(false)
val negotiated = ssh_negotiate_algorithms(_client_kexinit("ssh-ed25519"), server)
expect(negotiated.is_ok()).to_equal(false)
expect(negotiated.unwrap_err()).to_equal("no matching host key algorithm")
```

</details>

#### negotiates ssh-ed25519 against the real accepted-session KEXINIT when enabled

- negotiates ssh-ed25519 against the real accepted-session KEXINIT when enabled
   - Expected: negotiated.is_ok() is true
   - Expected: negotiated.unwrap().host_key equals `ssh-ed25519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negotiates ssh-ed25519 against the real accepted-session KEXINIT when enabled")
val payload = sshd_build_production_session_kexinit_for_test(
    true, _seed32(), nil, nil, nil, nil, nil, nil
)
val server = ssh_parse_kexinit(payload).unwrap()
val negotiated = ssh_negotiate_algorithms(_client_kexinit("ssh-ed25519"), server)
expect(negotiated.is_ok()).to_equal(true)
expect(negotiated.unwrap().host_key).to_equal("ssh-ed25519")
```

</details>

### SSHD certificate-aware host key list follows config

#### omits ssh-ed25519 from the certificate-aware list when disabled

- omits ssh-ed25519 from the certificate-aware list when disabled
   - Expected: algos equals ``
   - Expected: algos does not contain `ssh-ed25519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits ssh-ed25519 from the certificate-aware list when disabled")
val keys = sshd_build_host_keys_for_session_for_test(false, _seed32(), nil, nil, nil)
val algos = host_key_algorithms_with_certificates(keys, _no_certs())
expect(algos).to_equal("")
expect(algos.contains("ssh-ed25519")).to_equal(false)
```

</details>

#### keeps ssh-ed25519 in the certificate-aware list when enabled

- keeps ssh-ed25519 in the certificate-aware list when enabled
   - Expected: host_key_algorithms_with_certificates(keys, _no_certs()) equals `ssh-ed25519`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps ssh-ed25519 in the certificate-aware list when enabled")
val keys = sshd_build_host_keys_for_session_for_test(true, _seed32(), nil, nil, nil)
expect(host_key_algorithms_with_certificates(keys, _no_certs())).to_equal("ssh-ed25519")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/apps/sshd/sshd_host_key_advertise_policy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SSHD host key advertisement follows config, SSHD host key policy fails closed, SSHD startup itself is gated by the host key policy, SSHD never negotiates a disabled host key algorithm, SSHD certificate-aware host key list follows config.
- SSHD host key advertisement follows config
- SSHD host key policy fails closed
- SSHD startup itself is gated by the host key policy
- SSHD never negotiates a disabled host key algorithm
- SSHD certificate-aware host key list follows config

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 22 |
| Active scenarios | 22 |
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

- Canonical SPipe generation for source `61086b826d0bba541a2fb9a7328d56cc75438c3678c5b8a26e776b5b27e052b3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `61086b826d0bba541a2fb9a7328d56cc75438c3678c5b8a26e776b5b27e052b3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `61086b826d0bba541a2fb9a7328d56cc75438c3678c5b8a26e776b5b27e052b3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/apps/sshd/sshd_host_key_advertise_policy_spec.spl
mirror: doc/06_spec/01_unit/os/apps/sshd/sshd_host_key_advertise_policy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/apps/sshd/sshd_host_key_advertise_policy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/apps/sshd/sshd_host_key_advertise_policy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/apps/sshd/sshd_host_key_advertise_policy_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advertises ssh-ed25519 when the config enables it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/sshd_host_key_advertise_policy_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'never advertises ssh-ed25519 when the config disables it' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/apps/sshd/sshd_host_key_advertise_policy_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'advertises only the remaining enabled algorithm when ed25519 is disabled' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
