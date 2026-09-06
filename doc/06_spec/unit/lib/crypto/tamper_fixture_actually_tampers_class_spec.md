# Tamper Fixture Actually Tampers Class Specification

> Tests covering negative-test fixtures must actually corrupt their input.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Tamper Fixture Actually Tampers Class Specification

## Scenarios

### negative-test fixtures must actually corrupt their input

#### the naive fixed-character substitution is unsafe

#### silently degrades to a no-op when the target is already the replacement

- silently degrades to a no-op when the target is already the replacement
   - Expected: token.substring(15, 16) equals `X`
   - Expected: _naive_flip_at(token, 15) equals `token`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("silently degrades to a no-op when the target is already the replacement")
# Index 15 of the real v4.public RFC vector is "X".
val token = _PUBLIC_TOKEN_PREFIX
expect(token.substring(15, 16)).to_equal("X")
expect(_naive_flip_at(token, 15)).to_equal(token)
```

</details>

#### does mutate when the target differs from the replacement

- does mutate when the target differs from the replacement
   - Expected: _naive_flip_at(token, 14) == token is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("does mutate when the target differs from the replacement")
val token = _PUBLIC_TOKEN_PREFIX
expect(_naive_flip_at(token, 14) == token).to_equal(false)
```

</details>

#### the guarded substitution always corrupts

#### changes a character that is not already the replacement

- changes a character that is not already the replacement
   - Expected: _flip_char_at(token, 14) == token is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes a character that is not already the replacement")
val token = _PUBLIC_TOKEN_PREFIX
expect(_flip_char_at(token, 14) == token).to_equal(false)
```

</details>

#### changes a character that IS already the replacement

- changes a character that IS already the replacement
   - Expected: _flip_char_at(token, 15) == token is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("changes a character that IS already the replacement")
val token = _PUBLIC_TOKEN_PREFIX
expect(_flip_char_at(token, 15) == token).to_equal(false)
```

</details>

#### substitutes Y when the original is X

- substitutes Y when the original is X
   - Expected: _flip_char_at("abXde", 2) equals `abYde`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("substitutes Y when the original is X")
expect(_flip_char_at("abXde", 2)).to_equal("abYde")
```

</details>

#### substitutes X otherwise

- substitutes X otherwise
   - Expected: _flip_char_at("abcde", 2) equals `abXde`


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("substitutes X otherwise")
expect(_flip_char_at("abcde", 2)).to_equal("abXde")
```

</details>

#### preserves length and every other position

- preserves length and every other position
   - Expected: mutated.length() equals `token.length()`
   - Expected: mutated.substring(0, 15) equals `token.substring(0, 15)`
   - Expected: mutated.substring(16, token.length()) equals `token.substring(16, token.length())`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("preserves length and every other position")
val token = _PUBLIC_TOKEN_PREFIX
val mutated = _flip_char_at(token, 15)
expect(mutated.length()).to_equal(token.length())
expect(mutated.substring(0, 15)).to_equal(token.substring(0, 15))
expect(mutated.substring(16, token.length())).to_equal(token.substring(16, token.length()))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/crypto/tamper_fixture_actually_tampers_class_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering negative-test fixtures must actually corrupt their input.
- negative-test fixtures must actually corrupt their input

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

- Canonical SPipe generation for source `f7e306b5461cb4f2d46d16766b985ebbed764748a3c81d3b20610a05fe49f9ec`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `f7e306b5461cb4f2d46d16766b985ebbed764748a3c81d3b20610a05fe49f9ec`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `f7e306b5461cb4f2d46d16766b985ebbed764748a3c81d3b20610a05fe49f9ec`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/crypto/tamper_fixture_actually_tampers_class_spec.spl
mirror: doc/06_spec/unit/lib/crypto/tamper_fixture_actually_tampers_class_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/crypto/tamper_fixture_actually_tampers_class_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/crypto/tamper_fixture_actually_tampers_class_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/crypto/tamper_fixture_actually_tampers_class_spec.spl:52:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'silently degrades to a no-op when the target is already the replacement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/tamper_fixture_actually_tampers_class_spec.spl:60:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'does mutate when the target differs from the replacement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/crypto/tamper_fixture_actually_tampers_class_spec.spl:67:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'changes a character that is not already the replacement' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
