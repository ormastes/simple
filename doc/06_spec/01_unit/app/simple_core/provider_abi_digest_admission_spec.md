# Provider Abi Digest Admission Specification

> Tests covering 256-bit ABI digest codec, provider query result V2 wire, host-side exact ABI admission verdict.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Abi Digest Admission Specification

## Scenarios

### 256-bit ABI digest codec

#### round-trips a canonical lowercase 64-hex digest without loss

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trips a canonical lowercase 64-hex digest without loss
   - Expected: simple_abi_digest_to_hex_v1(parsed.value) equals `EXACT_HEX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("round-trips a canonical lowercase 64-hex digest without loss")
val parsed = simple_abi_digest_parse_hex_v1(EXACT_HEX)
assert_true(parsed.ok)
expect(simple_abi_digest_to_hex_v1(parsed.value)).to_equal(EXACT_HEX)
```

</details>

#### rejects malformed digest text instead of silently truncating

- rejects malformed digest text instead of silently truncating
   - Expected: simple_abi_digest_parse_hex_v1("abc").diagnostic equals `abi-digest-length-invalid`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects malformed digest text instead of silently truncating")
expect(simple_abi_digest_parse_hex_v1("abc").diagnostic).to_equal("abi-digest-length-invalid")
expect(simple_abi_digest_parse_hex_v1(
    "F173C682BABECA323ED37F1D64E99AE09694EF2A16934C45D57B3C6BFBA541DB"
).diagnostic).to_equal("abi-digest-not-lowercase-hex")
expect(simple_abi_digest_parse_hex_v1(
    "0000000000000000000000000000000000000000000000000000000000000000"
).diagnostic).to_equal("abi-digest-all-zero")
```

</details>

#### distinguishes digests that agree on the first 64 bits

- distinguishes digests that agree on the first 64 bits
   - Expected: digest_of(EXACT_HEX).w0 equals `digest_of(PREFIX_COLLIDING_HEX).w0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("distinguishes digests that agree on the first 64 bits")
assert_false(simple_abi_digest_equals_v1(digest_of(EXACT_HEX), digest_of(PREFIX_COLLIDING_HEX)))
expect(digest_of(EXACT_HEX).w0).to_equal(digest_of(PREFIX_COLLIDING_HEX).w0)
```

</details>

### provider query result V2 wire

#### keeps every V1 field at its V1 offset and appends 32 digest bytes

- keeps every V1 field at its V1 offset and appends 32 digest bytes
   - Expected: encoded.bytes.len() equals `SIMPLE_PROVIDER_QUERY_RESULT_V2_SIZE as i64`
   - Expected: SIMPLE_PROVIDER_QUERY_RESULT_V2_SIZE as i64 - SIMPLE_PROVIDER_QUERY_RESULT_V1_SIZE as i64 equals `32`
   - Expected: decoded.value.base.interface_handle equals `1129072945`
   - Expected: simple_abi_digest_to_hex_v1(decoded.value.abi_digest_256) equals `EXACT_HEX`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("keeps every V1 field at its V1 offset and appends 32 digest bytes")
val encoded = encode_provider_query_result_v2(result_v2(digest_of(EXACT_HEX)))
assert_true(encoded.ok)
expect(encoded.bytes.len()).to_equal(SIMPLE_PROVIDER_QUERY_RESULT_V2_SIZE as i64)
expect(SIMPLE_PROVIDER_QUERY_RESULT_V2_SIZE as i64 - SIMPLE_PROVIDER_QUERY_RESULT_V1_SIZE as i64).to_equal(32)
val decoded = decode_provider_query_result_v2(encoded.bytes)
assert_true(decoded.ok)
expect(decoded.value.base.interface_handle).to_equal(1129072945)
expect(simple_abi_digest_to_hex_v1(decoded.value.abi_digest_256)).to_equal(EXACT_HEX)
```

</details>

#### decodes a V1-only provider's 60 written bytes as an undeclared digest

- decodes a V1-only provider's 60 written bytes as an undeclared digest
   - Expected: decoded.value.base.interface_handle equals `1129072945`
   - Expected: decoded.value.abi_digest_256.w0 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("decodes a V1-only provider's 60 written bytes as an undeclared digest")
val encoded = encode_provider_query_result_v2(result_v2(digest_of(EXACT_HEX)))
# A V1-only provider writes 60 bytes into the host's zeroed V2 buffer.
var zeroed_tail: [u8] = []
var i = 0
while i < SIMPLE_PROVIDER_QUERY_RESULT_V2_SIZE as i64:
    if i < SIMPLE_PROVIDER_QUERY_RESULT_V1_SIZE as i64:
        zeroed_tail.push(encoded.bytes[i])
    else:
        zeroed_tail.push(0 as u8)
    i = i + 1
val decoded = decode_provider_query_result_v2(zeroed_tail)
assert_true(decoded.ok)
expect(decoded.value.base.interface_handle).to_equal(1129072945)
expect(decoded.value.abi_digest_256.w0).to_equal(0)
```

</details>

### host-side exact ABI admission verdict

#### admits only an exact 256-bit match

- admits only an exact 256-bit match
   - Expected: simple_core_provider_abi_digest_verdict_v1(EXACT_HEX, digest_of(EXACT_HEX)) equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("admits only an exact 256-bit match")
expect(simple_core_provider_abi_digest_verdict_v1(EXACT_HEX, digest_of(EXACT_HEX))).to_equal("")
```

</details>

#### rejects a digest that collides on the first 64 bits

- rejects a digest that collides on the first 64 bits


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a digest that collides on the first 64 bits")
expect(simple_core_provider_abi_digest_verdict_v1(
    EXACT_HEX, digest_of(PREFIX_COLLIDING_HEX)
)).to_equal("provider-abi-digest-mismatch")
```

</details>

#### rejects an unrelated digest

- rejects an unrelated digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects an unrelated digest")
expect(simple_core_provider_abi_digest_verdict_v1(
    EXACT_HEX, digest_of(DIFFERENT_HEX)
)).to_equal("provider-abi-digest-mismatch")
```

</details>

#### rejects a provider that declares no 256-bit digest

- rejects a provider that declares no 256-bit digest


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a provider that declares no 256-bit digest")
expect(simple_core_provider_abi_digest_verdict_v1(
    EXACT_HEX, SimpleAbiDigest256V1(w0: 0, w1: 0, w2: 0, w3: 0)
)).to_equal("provider-abi-digest-not-declared")
```

</details>

#### rejects a malformed locked SCI digest rather than admitting it

- rejects a malformed locked SCI digest rather than admitting it


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects a malformed locked SCI digest rather than admitting it")
expect(simple_core_provider_abi_digest_verdict_v1(
    "not-a-digest", digest_of(EXACT_HEX)
)).to_contain("provider-abi-digest-locked-invalid")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering 256-bit ABI digest codec, provider query result V2 wire, host-side exact ABI admission verdict.
- 256-bit ABI digest codec
- provider query result V2 wire
- host-side exact ABI admission verdict

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 10 |
| Active scenarios | 10 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-COMPOSITION-ABI-DIGEST-EXACT`
- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3c54083242aeeaba1741c2754a44ff94131c3484fd173e2016229228c87a138e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3c54083242aeeaba1741c2754a44ff94131c3484fd173e2016229228c87a138e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3c54083242aeeaba1741c2754a44ff94131c3484fd173e2016229228c87a138e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **80/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl
mirror: doc/06_spec/01_unit/app/simple_core/provider_abi_digest_admission_spec.md (current)
findings: 7 blockers: 1
  narrative=100 structure=100 oracle=70
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=80; blocker cap makes effective=49
doc/06_spec/01_unit/app/simple_core/provider_abi_digest_admission_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/simple_core/provider_abi_digest_admission_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips a canonical lowercase 64-hex digest without loss' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl:65:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects malformed digest text instead of silently truncating' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/simple_core/provider_abi_digest_admission_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'distinguishes digests that agree on the first 64 bits' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
