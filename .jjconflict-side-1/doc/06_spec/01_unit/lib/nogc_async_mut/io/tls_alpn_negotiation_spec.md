# Tls Alpn Negotiation Specification

> Tests covering ALPN negotiation wired into the TLS server handshake, ALPN echo in the ServerHello extensions block.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 12 | 12 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tls Alpn Negotiation Specification

## Scenarios

### ALPN negotiation wired into the TLS server handshake

#### finds the ALPN extension data inside a ClientHello block

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- finds the ALPN extension data inside a ClientHello block


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("finds the ALPN extension data inside a ClientHello block")
val data = find_alpn_extension_data(ch_extensions_offering_h2())
assert_equal(len(data), 5)
assert_equal(parse_alpn_extension(data), "h2")
```

</details>

#### reports no ALPN data when the client offered none

- reports no ALPN data when the client offered none


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no ALPN data when the client offered none")
assert_equal(len(find_alpn_extension_data(ch_extensions_without_alpn())), 0)
```

</details>

#### reports no ALPN data for a truncated extensions block

- reports no ALPN data for a truncated extensions block


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports no ALPN data for a truncated extensions block")
assert_equal(len(find_alpn_extension_data([0, 40, 0, 16])), 0)
```

</details>

#### negotiates a protocol the server supports

- negotiates a protocol the server supports


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negotiates a protocol the server supports")
assert_equal(negotiate_alpn(ch_extensions_offering_h2()), "h2")
```

</details>

#### declines a protocol the server cannot serve

- declines a protocol the server cannot serve


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("declines a protocol the server cannot serve")
assert_equal(negotiate_alpn(ch_extensions_offering_spdy()), "")
```

</details>

#### negotiates nothing when the client offered no ALPN

- negotiates nothing when the client offered no ALPN


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negotiates nothing when the client offered no ALPN")
assert_equal(negotiate_alpn(ch_extensions_without_alpn()), "")
```

</details>

#### negotiates nothing for an empty extensions block

- negotiates nothing for an empty extensions block


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("negotiates nothing for an empty extensions block")
assert_equal(negotiate_alpn([]), "")
```

</details>

### ALPN echo in the ServerHello extensions block

#### omits the extensions block when nothing was negotiated

- omits the extensions block when nothing was negotiated


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("omits the extensions block when nothing was negotiated")
assert_equal(build_alpn_extension_block(""), "")
```

</details>

#### emits an 11-byte extensions block for a two-byte protocol

- emits an 11-byte extensions block for a two-byte protocol


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits an 11-byte extensions block for a two-byte protocol")
assert_equal(len(build_alpn_extension_block("h2")), 11)
```

</details>

#### emits exactly the RFC 7301 ServerHello bytes for h2

- emits exactly the RFC 7301 ServerHello bytes for h2


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly the RFC 7301 ServerHello bytes for h2")
assert_equal(
    build_alpn_extension_block("h2"),
    bytes_to_wire([0, 9, 0, 16, 0, 5, 0, 3, 2, 104, 50])
)
```

</details>

#### emits exactly the RFC 7301 ServerHello bytes for http/1.1

- emits exactly the RFC 7301 ServerHello bytes for http/1.1


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("emits exactly the RFC 7301 ServerHello bytes for http/1.1")
assert_equal(
    build_alpn_extension_block("http/1.1"),
    bytes_to_wire([0, 15, 0, 16, 0, 11, 0, 9, 8, 104, 116, 116, 112, 47, 49, 46, 49])
)
```

</details>

#### echoes back a protocol the ClientHello parser can read again

- echoes back a protocol the ClientHello parser can read again


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("echoes back a protocol the ClientHello parser can read again")
assert_equal(parse_alpn_extension([0, 3, 2, 104, 50]), "h2")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering ALPN negotiation wired into the TLS server handshake, ALPN echo in the ServerHello extensions block.
- ALPN negotiation wired into the TLS server handshake
- ALPN echo in the ServerHello extensions block

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

- Canonical SPipe generation for source `49ea2a6fae10364b2c7a523fa7e08a3390d28895879de144f849a54efa38bbd9`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `49ea2a6fae10364b2c7a523fa7e08a3390d28895879de144f849a54efa38bbd9`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `49ea2a6fae10364b2c7a523fa7e08a3390d28895879de144f849a54efa38bbd9`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'finds the ALPN extension data inside a ClientHello block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.spl:38:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no ALPN data when the client offered none' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_async_mut/io/tls_alpn_negotiation_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports no ALPN data for a truncated extensions block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
