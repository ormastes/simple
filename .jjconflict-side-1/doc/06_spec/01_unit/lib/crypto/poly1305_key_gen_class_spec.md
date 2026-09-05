# Poly1305 Key Gen Class Specification

> Tests covering poly1305_key_gen block-counter class, poly1305_key_gen module-mirror class.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Poly1305 Key Gen Class Specification

## Scenarios

### poly1305_key_gen block-counter class

#### derives the one-time key from the counter-0 ChaCha20 keystream

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- derives the one-time key from the counter-0 ChaCha20 keystream
   - Expected: _bytes_eq(otk, ks0) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("derives the one-time key from the counter-0 ChaCha20 keystream")
val otk = poly1305_key_gen(_key(), _nonce())
val ks0 = _first32(chacha20_encrypt(_key(), 0, _nonce(), _zeros32()))
expect(_bytes_eq(otk, ks0)).to_equal(true)
```

</details>

#### does not derive the one-time key at block counter 1

- does not derive the one-time key at block counter 1
   - Expected: _bytes_eq(ks0, ks1) is false
   - Expected: _bytes_eq(otk, ks1) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does not derive the one-time key at block counter 1")
# Guard the guard: counter 0 and counter 1 must really differ, else the
# assertion below would pass against a counter-1 implementation too.
val ks0 = _first32(chacha20_encrypt(_key(), 0, _nonce(), _zeros32()))
val ks1 = _first32(chacha20_encrypt(_key(), 1, _nonce(), _zeros32()))
expect(_bytes_eq(ks0, ks1)).to_equal(false)

val otk = poly1305_key_gen(_key(), _nonce())
expect(_bytes_eq(otk, ks1)).to_equal(false)
```

</details>

### poly1305_key_gen module-mirror class

#### os.crypto.poly1305 derives the identical one-time key as std.crypto.poly1305

- os.crypto.poly1305 derives the identical one-time key as std.crypto.poly1305
   - Expected: _bytes_eq(a, b) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("os.crypto.poly1305 derives the identical one-time key as std.crypto.poly1305")
val a = poly1305_key_gen(_key(), _nonce())
val b = os_poly1305_key_gen(_key(), _nonce())
expect(_bytes_eq(a, b)).to_equal(true)
```

</details>

#### both module copies return exactly 32 bytes

- both module copies return exactly 32 bytes
   - Expected: poly1305_key_gen(_key(), _nonce()).len() equals `32u64`
   - Expected: os_poly1305_key_gen(_key(), _nonce()).len() equals `32u64`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("both module copies return exactly 32 bytes")
expect(poly1305_key_gen(_key(), _nonce()).len()).to_equal(32u64)
expect(os_poly1305_key_gen(_key(), _nonce()).len()).to_equal(32u64)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/crypto/poly1305_key_gen_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering poly1305_key_gen block-counter class, poly1305_key_gen module-mirror class.
- poly1305_key_gen block-counter class
- poly1305_key_gen module-mirror class

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-CRYPTO-POLY1305-KEYGEN`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c71b5689c676dc256a86262ed0df16aa5a677e688cd2fb0a44ab4665ef5c4cdd`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c71b5689c676dc256a86262ed0df16aa5a677e688cd2fb0a44ab4665ef5c4cdd`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c71b5689c676dc256a86262ed0df16aa5a677e688cd2fb0a44ab4665ef5c4cdd`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/crypto/poly1305_key_gen_class_spec.spl
mirror: doc/06_spec/01_unit/lib/crypto/poly1305_key_gen_class_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/crypto/poly1305_key_gen_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/crypto/poly1305_key_gen_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/crypto/poly1305_key_gen_class_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/crypto/poly1305_key_gen_class_spec.spl:72:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'derives the one-time key from the counter-0 ChaCha20 keystream' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/poly1305_key_gen_class_spec.spl:79:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does not derive the one-time key at block counter 1' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/crypto/poly1305_key_gen_class_spec.spl:93:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'os.crypto.poly1305 derives the identical one-time key as std.crypto.poly1305' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
