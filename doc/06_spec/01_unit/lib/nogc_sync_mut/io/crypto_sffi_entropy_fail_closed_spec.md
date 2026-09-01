# Crypto Sffi Entropy Fail Closed Specification

> Tests covering crypto_sffi entropy gate fails closed, random_hex / random_salt expose failure instead of hiding it.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 10 | 10 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Crypto Sffi Entropy Fail Closed Specification

## Scenarios

### crypto_sffi entropy gate fails closed

#### provider nil does not become an empty string

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- provider nil does not become an empty string
   - Expected: checked_entropy_hex(nil, 16) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("provider nil does not become an empty string")
# The exact regression: pre-fix this path yielded "" and callers could
# not tell entropy failure from a legitimate value.
expect(checked_entropy_hex(nil, 16)).to_equal(nil)
```

</details>

#### provider empty string is rejected rather than passed through

- provider empty string is rejected rather than passed through
   - Expected: checked_entropy_hex("", 16) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("provider empty string is rejected rather than passed through")
expect(checked_entropy_hex("", 16)).to_equal(nil)
```

</details>

#### a short result is rejected

- a short result is rejected
   - Expected: checked_entropy_hex("abcd", 16) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a short result is rejected")
expect(checked_entropy_hex("abcd", 16)).to_equal(nil)
```

</details>

#### an all-zero result is rejected

- an all-zero result is rejected
   - Expected: checked_entropy_hex("00000000000000000000000000000000", 16) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("an all-zero result is rejected")
expect(checked_entropy_hex("00000000000000000000000000000000", 16)).to_equal(nil)
```

</details>

#### a non-hex result is rejected

- a non-hex result is rejected
   - Expected: checked_entropy_hex("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", 16) equals `nil`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a non-hex result is rejected")
expect(checked_entropy_hex("zzzzzzzzzzzzzzzzzzzzzzzzzzzzzzzz", 16)).to_equal(nil)
```

</details>

#### a well-formed result passes through unchanged

- a well-formed result passes through unchanged
   - Expected: checked_entropy_hex(good, 16) equals `good`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a well-formed result passes through unchanged")
val good = "0123456789abcdef0123456789abcdef"
expect(checked_entropy_hex(good, 16)).to_equal(good)
```

</details>

### random_hex / random_salt expose failure instead of hiding it

#### random_salt returns 32 hex chars on a healthy host

- random_salt returns 32 hex chars on a healthy host
   - Expected: salt.len() equals `32`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("random_salt returns 32 hex chars on a healthy host")
val salt = random_salt() ?? ""
expect(salt.len()).to_equal(32)
```

</details>

#### random_salt output satisfies the entropy post-condition

- random_salt output satisfies the entropy post-condition
   - Expected: secure_entropy_hex_valid(salt) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("random_salt output satisfies the entropy post-condition")
val salt = random_salt() ?? ""
expect(secure_entropy_hex_valid(salt)).to_equal(true)
```

</details>

#### random_hex never returns an empty string for a nonzero request

- random_hex never returns an empty string for a nonzero request
   - Expected: v == "" is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("random_hex never returns an empty string for a nonzero request")
# Empty is now representable only as nil, never as a text value.
val v = random_hex(16)
expect(v == "").to_equal(false)
```

</details>

#### two successive salts differ

- two successive salts differ
   - Expected: a == b is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("two successive salts differ")
val a = random_salt() ?? "a"
val b = random_salt() ?? "b"
expect(a == b).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/nogc_sync_mut/io/crypto_sffi_entropy_fail_closed_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering crypto_sffi entropy gate fails closed, random_hex / random_salt expose failure instead of hiding it.
- crypto_sffi entropy gate fails closed
- random_hex / random_salt expose failure instead of hiding it

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `5e0bc7c794a68b5a54a4910d6f141111612ebdc497c348d0d7c0c060b3ac4356`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5e0bc7c794a68b5a54a4910d6f141111612ebdc497c348d0d7c0c060b3ac4356`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5e0bc7c794a68b5a54a4910d6f141111612ebdc497c348d0d7c0c060b3ac4356`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/nogc_sync_mut/io/crypto_sffi_entropy_fail_closed_spec.spl
mirror: doc/06_spec/01_unit/lib/nogc_sync_mut/io/crypto_sffi_entropy_fail_closed_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/nogc_sync_mut/io/crypto_sffi_entropy_fail_closed_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/nogc_sync_mut/io/crypto_sffi_entropy_fail_closed_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/nogc_sync_mut/io/crypto_sffi_entropy_fail_closed_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/nogc_sync_mut/io/crypto_sffi_entropy_fail_closed_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provider nil does not become an empty string' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/io/crypto_sffi_entropy_fail_closed_spec.spl:37:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'provider empty string is rejected rather than passed through' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/nogc_sync_mut/io/crypto_sffi_entropy_fail_closed_spec.spl:42:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a short result is rejected' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
