# Deflate Specification

> Tests covering DEFLATE RFC 1951 encoder/decoder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Deflate Specification

## Scenarios

### DEFLATE RFC 1951 encoder/decoder

#### decompresses known fixed-Huffman stream for Hello

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- decompresses known fixed-Huffman stream for Hello
   - Expected: decompressed.len() equals `5`
   - Expected: decompressed equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decompresses known fixed-Huffman stream for Hello")
val compressed = _make_known_deflate_hello()
val decompressed = deflate_decompress(compressed)
val expected = _make_hello_bytes()
expect(decompressed.len()).to_equal(5)
expect(decompressed).to_equal(expected)
```

</details>

#### round-trips empty input

- round-trips empty input
   - Expected: decompressed.len() equals `0`
   - Expected: decompressed equals `empty`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips empty input")
var empty: [u8] = []
val compressed = deflate_compress(empty)
val decompressed = deflate_decompress(compressed)
expect(decompressed.len()).to_equal(0)
expect(decompressed).to_equal(empty)
```

</details>

#### round-trips Hello World

- round-trips Hello World
   - Expected: decompressed.len() equals `input.len()`
   - Expected: decompressed equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips Hello World")
val input = _make_hello_world_bytes()
val compressed = deflate_compress(input)
val decompressed = deflate_decompress(compressed)
expect(decompressed.len()).to_equal(input.len())
expect(decompressed).to_equal(input)
```

</details>

#### round-trips 1000 bytes of repeated pattern

- round-trips 1000 bytes of repeated pattern
   - Expected: compressed.len() < input.len() is true
   - Expected: decompressed.len() equals `input.len()`
   - Expected: decompressed equals `input`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trips 1000 bytes of repeated pattern")
val input = _make_repeated_pattern(1000)
val compressed = deflate_compress(input)
# Repeated data should compress significantly
expect(compressed.len() < input.len()).to_equal(true)
val decompressed = deflate_decompress(compressed)
expect(decompressed.len()).to_equal(input.len())
expect(decompressed).to_equal(input)
```

</details>

#### compressed output is smaller than input for repetitive data

- compressed output is smaller than input for repetitive data
   - Expected: compressed.len() < 100 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("compressed output is smaller than input for repetitive data")
val input = _make_repeated_pattern(1000)
val compressed = deflate_compress(input)
expect(compressed.len() < 100).to_equal(true)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/unit/lib/common/compress/deflate_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering DEFLATE RFC 1951 encoder/decoder.
- DEFLATE RFC 1951 encoder/decoder

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
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c89e20d57c28dc5959331569b3769be36ade033435a7393046221069a3279284`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c89e20d57c28dc5959331569b3769be36ade033435a7393046221069a3279284`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c89e20d57c28dc5959331569b3769be36ade033435a7393046221069a3279284`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/unit/lib/common/compress/deflate_spec.spl
mirror: doc/06_spec/unit/lib/common/compress/deflate_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/compress/deflate_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/compress/deflate_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/compress/deflate_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/lib/common/compress/deflate_spec.spl:69:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'decompresses known fixed-Huffman stream for Hello' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress/deflate_spec.spl:78:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress/deflate_spec.spl:87:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trips Hello World' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
