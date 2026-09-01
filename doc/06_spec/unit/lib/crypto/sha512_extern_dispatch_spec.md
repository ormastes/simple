# Sha512 Extern Dispatch Specification

> Tests covering SHA-512 rt_sha512_* interpreter dispatch — FIPS 180-4 KAT.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha512 Extern Dispatch Specification

## Scenarios

### SHA-512 rt_sha512_* interpreter dispatch — FIPS 180-4 KAT

#### FIPS 180-4 §C.0 empty string digest

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- FIPS 180-4 §C.0 empty string digest
   - Expected: bytes_to_hex(digest) equals `cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIPS 180-4 §C.0 empty string digest")
# Expected: cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce
#           47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e
val empty: [u8] = []
val digest = sha512(empty)
expect(bytes_to_hex(digest)).to_equal("cf83e1357eefb8bdf1542850d66d8007d620e4050b5715dc83f4a921d36ce9ce47d0d13c5d85f2b0ff8318d2877eec2f63b931bd47417a81a538327af927da3e")
```

</details>

#### FIPS 180-4 §C.1 'abc' canary digest

- FIPS 180-4 §C.1 'abc' canary digest
   - Expected: bytes_to_hex(digest) equals `ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("FIPS 180-4 §C.1 'abc' canary digest")
# Expected: ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a
#           2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f
val abc: [u8] = [0x61, 0x62, 0x63]
val digest = sha512(abc)
expect(bytes_to_hex(digest)).to_equal("ddaf35a193617abacc417349ae20413112e6fa4e89a97ea20a9eeee64b55d39a2192992a274fc1a836ba3c23a3feebbd454d4423643ce80e2a9ac94fa54ca49f")
```

</details>

#### multi-block boundary: 256 bytes of 0x61 ('a') — 2 SHA-512 blocks

- multi-block boundary: 256 bytes of 0x61 ('a') — 2 SHA-512 blocks
   - Expected: bytes_to_hex(digest) equals `6a9169eb662f136d87374070e8828b3e615a7eca32a89446e9225b02832709be095e635c824a2... (full value in folded executable source)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("multi-block boundary: 256 bytes of 0x61 ('a') — 2 SHA-512 blocks")
# DEVIATION from FIPS §C.2/§C.3: 'a' × 256 (= 2 SHA-512 blocks of 128 B
# each, since the padding bumps it past one block) instead of the
# 112-byte FIPS string or 1M-byte vector. This keeps the spec
# interpreter-friendly while still exercising the multi-block branch
# of rt_sha512_hash.
# Reference (computed 2026-05-02):
#   python3 -c "import hashlib; print(hashlib.sha512(b'a'*256).hexdigest())"
val input = _make_256_a()
val digest = sha512(input)
expect(bytes_to_hex(digest)).to_equal("6a9169eb662f136d87374070e8828b3e615a7eca32a89446e9225b02832709be095e635c824a2bb70213ba2ea0ababac0809827843992c851903b7ac0c136699")
```

</details>

#### REQ-SHA512ID-002 byte-by-byte readback contract

- REQ-SHA512ID-002 byte-by-byte readback contract
   - Expected: digest.len().to_i64() equals `64i64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-SHA512ID-002 byte-by-byte readback contract")
# The extern API is two-step: rt_sha512_hash stashes into a
# static buffer; rt_sha512_byte(i) reads byte i. The wrapper
# `sha512()` exercises i=0..63 — verify length is exactly 64.
val abc: [u8] = [0x61, 0x62, 0x63]
val digest = sha512(abc)
expect(digest.len().to_i64()).to_equal(64i64)
```

</details>

#### REQ-SHA512ID-002 stash-buffer overwrite — second hash overwrites first

- REQ-SHA512ID-002 stash-buffer overwrite — second hash overwrites first
   - Expected: bytes_to_hex(da) equals `bytes_to_hex(da_again)`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REQ-SHA512ID-002 stash-buffer overwrite — second hash overwrites first")
# Two consecutive sha512() calls with different inputs must
# yield distinct digests (proves the static buffer is rewritten).
val a: [u8] = [0x61]
val b: [u8] = [0x62]
val da = sha512(a)
val db = sha512(b)
# Re-hash 'a' to confirm we still get the original 'a' digest.
val da_again = sha512(a)
expect(bytes_to_hex(da)).to_equal(bytes_to_hex(da_again))
# And the 'b' digest is different from 'a' digest.
assert_not_equal(bytes_to_hex(da), bytes_to_hex(db))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/sha512_extern_dispatch_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SHA-512 rt_sha512_* interpreter dispatch — FIPS 180-4 KAT.
- SHA-512 rt_sha512_* interpreter dispatch — FIPS 180-4 KAT

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-SHA512ID-004`
- `REQ-SHA512ID-005`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `7f46027ccc5877be682692448d97e0e628a85aa135f098d9e5a5ea0228587c76`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `7f46027ccc5877be682692448d97e0e628a85aa135f098d9e5a5ea0228587c76`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `7f46027ccc5877be682692448d97e0e628a85aa135f098d9e5a5ea0228587c76`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/unit/lib/crypto/sha512_extern_dispatch_spec.spl
mirror: doc/06_spec/unit/lib/crypto/sha512_extern_dispatch_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/unit/lib/crypto/sha512_extern_dispatch_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/sha512_extern_dispatch_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/sha512_extern_dispatch_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/unit/lib/crypto/sha512_extern_dispatch_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FIPS 180-4 §C.0 empty string digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/sha512_extern_dispatch_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'FIPS 180-4 §C.1 'abc' canary digest' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/sha512_extern_dispatch_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'multi-block boundary: 256 bytes of 0x61 ('a') — 2 SHA-512 blocks' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
