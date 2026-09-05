# Sha256 Core Vectors Specification

> Tests covering sha256_core cross-module import, sha256_text FIPS 180-4 vectors, sha256_bytes_scalar FIPS 180-4 vectors (core-routed).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 13 | 13 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Sha256 Core Vectors Specification

## Scenarios

### sha256_core cross-module import

#### exports its initial hash constants across a module boundary

- exports its initial hash constants across a module boundary
- import sha256_initial_hash from std.common.crypto.sha256_core
- assert H(0)[0] and H(0)[7] match FIPS 180-4 section 5.3.3


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("exports its initial hash constants across a module boundary")
"""The FIPS 180-4 initial hash value H(0) is frac(sqrt(2)) = 0x6a09e667.
Reading it through a `use` proves bare `fn` is module-exported."""
step("import sha256_initial_hash from std.common.crypto.sha256_core")
val h = sha256_initial_hash()
step("assert H(0)[0] and H(0)[7] match FIPS 180-4 section 5.3.3")
assert_equal(h.len(), 8)
assert_equal(h[0], 1779033703)   # 0x6a09e667
assert_equal(h[7], 1541459225)   # 0x5be0cd19
```

</details>

#### pads an empty message to exactly one 64-byte block

- pads an empty message to exactly one 64-byte block
- pad the empty message via sha256_pad_message
- assert one 64-byte block with the 0x80 terminator first


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("pads an empty message to exactly one 64-byte block")
"""FIPS 180-4 section 5.1.1: append 0x80, then zeros, then a 64-bit
length. An empty message therefore occupies exactly one block."""
step("pad the empty message via sha256_pad_message")
val padded = sha256_pad_message([])
step("assert one 64-byte block with the 0x80 terminator first")
assert_equal(padded.len(), 64)
assert_equal(padded[0], 128)
assert_equal(padded[63], 0)
```

</details>

#### compresses the padded empty block to the known empty digest state

- compresses the padded empty block to the known empty digest state
- process the padded empty block from the FIPS initial state
- assert first state word equals 0xe3b0c442


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("compresses the padded empty block to the known empty digest state")
"""Routing check: the digest of "" must be reproducible by driving
sha256_core's own primitives directly, not only via sha256_text."""
step("process the padded empty block from the FIPS initial state")
val h = sha256_process_block(sha256_initial_hash(), sha256_pad_message([]))
step("assert first state word equals 0xe3b0c442")
assert_equal(h.len(), 8)
assert_equal(h[0], 3820012610)   # 0xe3b0c442
```

</details>

### sha256_text FIPS 180-4 vectors

#### hashes the empty string to the canonical digest

- hashes the empty string to the canonical digest
- hash the empty string


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes the empty string to the canonical digest")
"""The most widely attested SHA-256 vector."""
step("hash the empty string")
assert_equal(sha256_text(""),
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### hashes \

- hashes \
- hash the 24-bit single-block message


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes \")
step("hash the 24-bit single-block message")
assert_equal(sha256_text("abc"),
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
```

</details>

#### hashes the 448-bit message at the two-block padding boundary

- hashes the 448-bit message at the two-block padding boundary
- hash the 56-character FIPS 180-4 section B.2 message


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes the 448-bit message at the two-block padding boundary")
"""56 bytes is the boundary case: the length field no longer fits in the
first block, so padding must spill into a second block."""
step("hash the 56-character FIPS 180-4 section B.2 message")
val msg = "abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq"
assert_equal(msg.len(), 56)
assert_equal(sha256_text(msg),
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
```

</details>

#### hashes the 896-bit multi-block message

- hashes the 896-bit multi-block message
- hash the 112-character multi-block message


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes the 896-bit multi-block message")
step("hash the 112-character multi-block message")
val msg = "abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" +
          "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu"
assert_equal(msg.len(), 112)
assert_equal(sha256_text(msg),
    "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1")
```

</details>

#### hashes 1000 repetitions of \

- hashes 1000 repetitions of \
- build and hash a 1000-byte message


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes 1000 repetitions of \")
"""A long message exercises the block loop well past the padding cases."""
step("build and hash a 1000-byte message")
val msg = repeat_text("a", 1000)
assert_equal(msg.len(), 1000)
assert_equal(sha256_text(msg),
    "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3")
```

</details>

### sha256_bytes_scalar FIPS 180-4 vectors (core-routed)

#### hashes the empty message through the core primitives

- hashes the empty message through the core primitives
- drive the empty message through sha256_bytes_scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes the empty message through the core primitives")
step("drive the empty message through sha256_bytes_scalar")
assert_equal(bytes_to_hex(sha256_bytes_scalar([])),
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
```

</details>

#### hashes \

- hashes \
- drive the 24-bit message through sha256_bytes_scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes \")
step("drive the 24-bit message through sha256_bytes_scalar")
assert_equal(bytes_to_hex(sha256_bytes_scalar(ascii_bytes("abc"))),
    "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")
```

</details>

#### hashes the 448-bit boundary message through the core primitives

- hashes the 448-bit boundary message through the core primitives
- drive the 56-byte message through sha256_bytes_scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes the 448-bit boundary message through the core primitives")
step("drive the 56-byte message through sha256_bytes_scalar")
val msg = ascii_bytes("abcdbcdecdefdefgefghfghighijhijkijkljklmklmnlmnomnopnopq")
assert_equal(msg.len(), 56)
assert_equal(bytes_to_hex(sha256_bytes_scalar(msg)),
    "248d6a61d20638b8e5c026930c3e6039a33ce45964ff2167f6ecedd419db06c1")
```

</details>

#### hashes the 896-bit multi-block message through the core primitives

- hashes the 896-bit multi-block message through the core primitives
- drive the 112-byte message through sha256_bytes_scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes the 896-bit multi-block message through the core primitives")
step("drive the 112-byte message through sha256_bytes_scalar")
val msg = ascii_bytes("abcdefghbcdefghicdefghijdefghijkefghijklfghijklmghijklmn" +
                      "hijklmnoijklmnopjklmnopqklmnopqrlmnopqrsmnopqrstnopqrstu")
assert_equal(msg.len(), 112)
assert_equal(bytes_to_hex(sha256_bytes_scalar(msg)),
    "cf5b16a778af8380036ce59e7b0492370b249b11e8f07a51afac45037afee9d1")
```

</details>

#### hashes 1000 repetitions of \

- hashes 1000 repetitions of \
- drive a 1000-byte message through sha256_bytes_scalar


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("hashes 1000 repetitions of \")
step("drive a 1000-byte message through sha256_bytes_scalar")
val msg = repeat_bytes(97, 1000)
assert_equal(msg.len(), 1000)
assert_equal(bytes_to_hex(sha256_bytes_scalar(msg)),
    "41edece42d63e8d9bf515a9ba6932e1c20cbc9f5a5d134645adb5db1b9737ea3")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/crypto/sha256_core_vectors_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering sha256_core cross-module import, sha256_text FIPS 180-4 vectors, sha256_bytes_scalar FIPS 180-4 vectors (core-routed).
- sha256_core cross-module import
- sha256_text FIPS 180-4 vectors
- sha256_bytes_scalar FIPS 180-4 vectors (core-routed)

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 13 |
| Active scenarios | 13 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-CRYPTO-SHA256-VECTORS`
- `REQ-CRYPTO-SHA256-CORE-ROUTING`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `56d8b78e8f3517313aa79c0511d0e7e571dccd7292a07ae418e0d5b29b2f9d95`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `56d8b78e8f3517313aa79c0511d0e7e571dccd7292a07ae418e0d5b29b2f9d95`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `56d8b78e8f3517313aa79c0511d0e7e571dccd7292a07ae418e0d5b29b2f9d95`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/common/crypto/sha256_core_vectors_spec.spl
mirror: doc/06_spec/01_unit/lib/common/crypto/sha256_core_vectors_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/common/crypto/sha256_core_vectors_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/crypto/sha256_core_vectors_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/crypto/sha256_core_vectors_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/common/crypto/sha256_core_vectors_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'exports its initial hash constants across a module boundary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/sha256_core_vectors_spec.spl:88:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'pads an empty message to exactly one 64-byte block' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/crypto/sha256_core_vectors_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'compresses the padded empty block to the known empty digest state' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
