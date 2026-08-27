# Server Entropy Owner Specification

> Tests covering server handshake entropy admission, the canonical entropy owner reports failure typed, tls13_accept still fails closed before drawing entropy.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Server Entropy Owner Specification

## Scenarios

### server handshake entropy admission

#### rejects an all-zero 32-byte draw

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects an all-zero 32-byte draw


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an all-zero 32-byte draw")
expect(tls13_server_entropy_admits(_zeros(32u64))).to_be("server_entropy_all_zero")
```

</details>

#### rejects an empty draw

- rejects an empty draw


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an empty draw")
expect(tls13_server_entropy_admits([])).to_be("server_entropy_wrong_length")
```

</details>

#### rejects a short draw

- rejects a short draw


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a short draw")
expect(tls13_server_entropy_admits(_zeros(31u64))).to_be("server_entropy_wrong_length")
```

</details>

#### rejects an over-long draw

- rejects an over-long draw


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects an over-long draw")
expect(tls13_server_entropy_admits(_zeros(33u64))).to_be("server_entropy_wrong_length")
```

</details>

#### admits a 32-byte draw with a nonzero byte

- admits a 32-byte draw with a nonzero byte


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("admits a 32-byte draw with a nonzero byte")
var material = _zeros(32u64)
material[31] = 1u8
expect(tls13_server_entropy_admits(material)).to_be("")
```

</details>

### the canonical entropy owner reports failure typed

#### rejects a zero-length request instead of returning empty bytes

- rejects a zero-length request instead of returning empty bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a zero-length request instead of returning empty bytes")
expect(crypto_entropy_bytes(0u64).is_err()).to_be(true)
```

</details>

#### rejects a request over the owner limit

- rejects a request over the owner limit


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a request over the owner limit")
expect(crypto_entropy_bytes(CRYPTO_ENTROPY_MAX_REQUEST + 1u64).is_err()).to_be(true)
```

</details>

#### rejects a provider draw of the wrong length

- rejects a provider draw of the wrong length


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a provider draw of the wrong length")
val checked = crypto_entropy_validate_candidate_for_test(32u64, true, _zeros(16u64))
expect(checked.is_err()).to_be(true)
```

</details>

#### rejects any draw when the platform is not ready

- rejects any draw when the platform is not ready


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects any draw when the platform is not ready")
val checked = crypto_entropy_validate_candidate_for_test(32u64, false, _zeros(32u64))
expect(checked.is_err()).to_be(true)
```

</details>

### tls13_accept still fails closed before drawing entropy

#### rejects a negative socket

- rejects a negative socket


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a negative socket")
match tls13_accept(-1, _test_config()):
    case Tls13AcceptResult.Failed(reason):
        expect(reason).to_be("invalid_socket_fd")
    case Tls13AcceptResult.Accepted(_ctx):
        expect(false).to_be(true)
```

</details>

#### rejects a config with no certificate chain

- rejects a config with no certificate chain


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a config with no certificate chain")
val cfg = Tls13ServerConfig {
    cert_chain: [],
    server_pkcs8: [4u8],
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
}
match tls13_accept(3, cfg):
    case Tls13AcceptResult.Failed(reason):
        expect(reason).to_be("missing_certificate_chain")
    case Tls13AcceptResult.Accepted(_ctx):
        expect(false).to_be(true)
```

</details>

#### rejects a config with no private key

- rejects a config with no private key


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a config with no private key")
val cfg = Tls13ServerConfig {
    cert_chain: [[1u8]],
    server_pkcs8: [],
    server_sig_scheme: 0x0807u16,
    alpn_protocols: []
}
match tls13_accept(3, cfg):
    case Tls13AcceptResult.Failed(reason):
        expect(reason).to_be("missing_server_private_key")
    case Tls13AcceptResult.Accepted(_ctx):
        expect(false).to_be(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/tls13/server_entropy_owner_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering server handshake entropy admission, the canonical entropy owner reports failure typed, tls13_accept still fails closed before drawing entropy.
- server handshake entropy admission
- the canonical entropy owner reports failure typed
- tls13_accept still fails closed before drawing entropy

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `88c1f78ea198372318c646c80a06099cb74668d53c35b0220da39e0309f6e40d`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `88c1f78ea198372318c646c80a06099cb74668d53c35b0220da39e0309f6e40d`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `88c1f78ea198372318c646c80a06099cb74668d53c35b0220da39e0309f6e40d`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/os/tls13/server_entropy_owner_spec.spl
mirror: doc/06_spec/01_unit/os/tls13/server_entropy_owner_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/tls13/server_entropy_owner_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/tls13/server_entropy_owner_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/tls13/server_entropy_owner_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an all-zero 32-byte draw' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tls13/server_entropy_owner_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects an empty draw' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/tls13/server_entropy_owner_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects a short draw' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
