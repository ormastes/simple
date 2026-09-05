# Flat Pool Codec Decode Cost Specification

> Tests covering flat pool codec decode cost.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Flat Pool Codec Decode Cost Specification

## Scenarios

### flat pool codec decode cost

#### decodes a large escape-free text pool in well under the pre-fix cost

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decodes a large escape-free text pool in well under the pre-fix cost
   - Expected: decoded.len() equals `2000`
   - Expected: decoded[0] equals `chunk`
   - Expected: decoded[1999] equals `chunk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("decodes a large escape-free text pool in well under the pre-fix cost")
# 2000 values x 400 chars = 800k characters that the old loop walked
# one slice-and-concat at a time. An unescaped value decodes to itself,
# so the only correct amount of work here is a scan.
var chunk = "abcdefghij"
while chunk.len() < 400:
    chunk = chunk + "abcdefghij"
var pool: [text] = []
while pool.len() < 2000:
    pool = pool.push(chunk)
val blob = flat_pool_enc_text(pool)
val t0 = rt_time_now_unix_micros()
val decoded = flat_pool_dec_text(FlatPoolReader.new(blob))
val elapsed_ms = (rt_time_now_unix_micros() - t0) / 1000
expect(decoded.len()).to_equal(2000)
expect(decoded[0]).to_equal(chunk)
expect(decoded[1999]).to_equal(chunk)
expect(elapsed_ms < 5000).to_be_true()
```

</details>

#### decodes an escaped text pool in bulk, not one character at a time

- decodes an escaped text pool in bulk, not one character at a time
   - Expected: decoded.len() equals `2000`
   - Expected: decoded[0] equals `chunk`
   - Expected: decoded[1999] equals `chunk`


<details>
<summary>Executable SSpec</summary>

Runnable source: 20 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("decodes an escaped text pool in bulk, not one character at a time")
# Escapes miss the identity fast path, so this pins the OTHER half of the
# fix: the two escape forms are rewritten by three bulk runtime replaces
# rather than by an interpreted per-character loop.
var chunk = "alpha\nbeta\\gamma"
while chunk.len() < 400:
    chunk = chunk + "alpha\nbeta\\gamma"
var pool: [text] = []
while pool.len() < 2000:
    pool = pool.push(chunk)
val blob = flat_pool_enc_text(pool)
val t0 = rt_time_now_unix_micros()
val decoded = flat_pool_dec_text(FlatPoolReader.new(blob))
val elapsed_ms = (rt_time_now_unix_micros() - t0) / 1000
expect(decoded.len()).to_equal(2000)
# Fidelity first: a fast decode that loses an escape is worthless.
expect(decoded[0]).to_equal(chunk)
expect(decoded[1999]).to_equal(chunk)
expect(elapsed_ms < 5000).to_be_true()
```

</details>

#### returns an escape-free value unchanged, byte for byte

- returns an escape-free value unchanged, byte for byte
   - Expected: flat_pool_unescape("") equals ``
   - Expected: flat_pool_unescape("plain identifier") equals `plain identifier`
   - Expected: flat_pool_unescape("n not an escape") equals `n not an escape`
   - Expected: flat_pool_unescape("a\\nb") equals `a\nb`
   - Expected: flat_pool_unescape("a\\\\b") equals `a\\b`
   - Expected: flat_pool_unescape("\\") equals `\\`
   - Expected: flat_pool_unescape("a\\qb") equals `a\\qb`
   - Expected: flat_pool_unescape("\\\\n") equals `\\n`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-COMPILER
step("returns an escape-free value unchanged, byte for byte")
# The fast path is only sound because the encoder emits a backslash
# ONLY as the lead byte of an escape. Pin that it is identity, not an
# approximation: a value that merely LOOKS escaped after decoding
# would be a silent miscompile.
expect(flat_pool_unescape("")).to_equal("")
expect(flat_pool_unescape("plain identifier")).to_equal("plain identifier")
expect(flat_pool_unescape("n not an escape")).to_equal("n not an escape")
# And the slow path still handles the adversarial shapes.
expect(flat_pool_unescape("a\\nb")).to_equal("a\nb")
expect(flat_pool_unescape("a\\\\b")).to_equal("a\\b")
expect(flat_pool_unescape("\\")).to_equal("\\")
expect(flat_pool_unescape("a\\qb")).to_equal("a\\qb")
expect(flat_pool_unescape("\\\\n")).to_equal("\\n")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Compiler |
| Status | Active |
| Source | `test/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering flat pool codec decode cost.
- flat pool codec decode cost

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 3 |
| Active scenarios | 3 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-COMPILER`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `0db07d113c1d76c090e814d1b72e4edcfb37918555c74521e2be3f9dee757c69`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `0db07d113c1d76c090e814d1b72e4edcfb37918555c74521e2be3f9dee757c69`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `0db07d113c1d76c090e814d1b72e4edcfb37918555c74521e2be3f9dee757c69`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.spl
mirror: doc/06_spec/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.spl:33:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes a large escape-free text pool in well under the pre-fix cost' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.spl:54:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decodes an escaped text pool in bulk, not one character at a time' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/compiler/frontend/flat_pool_codec_decode_cost_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns an escape-free value unchanged, byte for byte' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
