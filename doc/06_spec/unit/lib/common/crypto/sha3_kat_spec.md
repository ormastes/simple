# Sha3 Kat Specification

> Tests covering SHA3-256 — FIPS 202 known-answer vectors, SHA3-384 — FIPS 202 known-answer vectors, SHA3-512 — FIPS 202 known-answer vectors.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha3 Kat Specification

## Scenarios

### SHA3-256 — FIPS 202 known-answer vectors

#### SHA3-256(\

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- SHA3-256(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA3-256(\")
expect(bytes_to_hex(sha3_256_bytes(_empty()))).to_equal(
    "a7ffc6f8bf1ed76651c14756a061d662f580ff4de43b49fa82d80a4b80f8434a"
)
```

</details>

#### SHA3-256(\

- SHA3-256(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA3-256(\")
expect(bytes_to_hex(sha3_256_bytes(_abc()))).to_equal(
    "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
)
```

</details>

#### Streaming SHA3-256(\

- Streaming SHA3-256(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("Streaming SHA3-256(\")
var ctx = create_sha3_256_context()
ctx = sha3_update(ctx, [0x61])
ctx = sha3_update(ctx, [0x62, 0x63])
expect(bytes_to_hex(sha3_finalize(ctx, 32))).to_equal(
    "3a985da74fe225b2045c172d6bd390bd855f086e3e9d525b46bfe24511431532"
)
```

</details>

### SHA3-384 — FIPS 202 known-answer vectors

#### SHA3-384(\

- SHA3-384(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA3-384(\")
expect(bytes_to_hex(sha3_384_bytes(_empty()))).to_equal(
    "0c63a75b845e4f7d01107d852e4c2485c51a50aaaa94fc61995e71bbee983a2ac3713831264adb47fb6bd1e058d5f004"
)
```

</details>

#### SHA3-384(\

- SHA3-384(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA3-384(\")
expect(bytes_to_hex(sha3_384_bytes(_abc()))).to_equal(
    "ec01498288516fc926459f58e2c6ad8df9b473cb0fc08c2596da7cf0e49be4b298d88cea927ac7f539f1edf228376d25"
)
```

</details>

### SHA3-512 — FIPS 202 known-answer vectors

#### SHA3-512(\

- SHA3-512(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA3-512(\")
expect(bytes_to_hex(sha3_512_bytes(_empty()))).to_equal(
    "a69f73cca23a9ac5c8b567dc185a756e97c982164fe25859e0d1dcc1475c80a615b2123af1f5f94c11e3e9402c3ac558f500199d95b6d3e301758586281dcd26"
)
```

</details>

#### SHA3-512(\

- SHA3-512(\


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("SHA3-512(\")
expect(bytes_to_hex(sha3_512_bytes(_abc()))).to_equal(
    "b751850b1a57168a5693cd924b6b096e08f621827444f70d884f5d0240d2712e10e116e9192af3c91a7ec57647e3934057340b4cf408d5a56592f8274eec53f0"
)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/crypto/sha3_kat_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHA3-256 — FIPS 202 known-answer vectors, SHA3-384 — FIPS 202 known-answer vectors, SHA3-512 — FIPS 202 known-answer vectors.
- SHA3-256 — FIPS 202 known-answer vectors
- SHA3-384 — FIPS 202 known-answer vectors
- SHA3-512 — FIPS 202 known-answer vectors

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 7 |
| Active scenarios | 7 |
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

- Canonical SPipe generation for source `387c29459a9db3786332899879db6e4ac3103b315784327fb18d525fa0b29f23`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `387c29459a9db3786332899879db6e4ac3103b315784327fb18d525fa0b29f23`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `387c29459a9db3786332899879db6e4ac3103b315784327fb18d525fa0b29f23`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/crypto/sha3_kat_spec.spl
mirror: doc/06_spec/unit/lib/common/crypto/sha3_kat_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/crypto/sha3_kat_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/crypto/sha3_kat_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/crypto/sha3_kat_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SHA3-256(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/sha3_kat_spec.spl:74:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'SHA3-256(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/crypto/sha3_kat_spec.spl:81:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'Streaming SHA3-256(\' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
