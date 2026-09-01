# Snappy Block Compression Unit Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Snappy Block Compression Unit Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPRESS-SNAPPY |
| Category | Compression |
| Status | Implemented |
| Source | `test/unit/lib/common/compress/snappy_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### Snappy block compression

#### round-trip empty input

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trip empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip empty input")
var empty: [u8] = []
val compressed = snappy_compress(empty)
check(compressed.len() == 1)
check(compressed[0] == 0x00u8)
val decompressed = snappy_decompress(compressed)
check(decompressed.len() == 0)
```

</details>

#### round-trip Hello World

- round-trip Hello World


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip Hello World")
var data: [u8] = [0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8, 0x2cu8, 0x20u8, 0x57u8, 0x6fu8, 0x72u8, 0x6cu8, 0x64u8, 0x21u8]
val compressed = snappy_compress(data)
val decompressed = snappy_decompress(compressed)
check(decompressed.len() == 13)
check(decompressed[0] == 0x48u8)
check(decompressed[1] == 0x65u8)
check(decompressed[4] == 0x6fu8)
check(decompressed[12] == 0x21u8)
```

</details>

#### known vector Hello literal

- known vector Hello literal


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("known vector Hello literal")
var expected: [u8] = [0x05u8, 0x10u8, 0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
var data: [u8] = [0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val compressed = snappy_compress(data)
check(compressed.len() == 7)
check(compressed[0] == 0x05u8)
check(compressed[1] == 0x10u8)
check(compressed[2] == 0x48u8)
check(compressed[3] == 0x65u8)
check(compressed[4] == 0x6cu8)
check(compressed[5] == 0x6cu8)
check(compressed[6] == 0x6fu8)
```

</details>

#### round-trip repeated data compresses well

- round-trip repeated data compresses well


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip repeated data compresses well")
val data = _make_repeated_bytes(0x41u8, 1000)
val compressed = snappy_compress(data)
check(compressed.len() < 100)
val decompressed = snappy_decompress(compressed)
check(decompressed.len() == 1000)
check(decompressed[0] == 0x41u8)
check(decompressed[999] == 0x41u8)
```

</details>

#### round-trip ABCABCABC has copy elements

- round-trip ABCABCABC has copy elements


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip ABCABCABC has copy elements")
var data: [u8] = [0x41u8, 0x42u8, 0x43u8, 0x41u8, 0x42u8, 0x43u8, 0x41u8, 0x42u8, 0x43u8]
val compressed = snappy_compress(data)
val decompressed = snappy_decompress(compressed)
check(decompressed.len() == 9)
check(decompressed[0] == 0x41u8)
check(decompressed[3] == 0x41u8)
check(decompressed[6] == 0x41u8)
check(decompressed[8] == 0x43u8)
```

</details>

#### decompress rejects truncated input

- decompress rejects truncated input


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decompress rejects truncated input")
var bad: [u8] = [0x05u8, 0x10u8]
val result = try_snappy_decompress(bad)
check(result.is_err())
```

</details>

#### decompress rejects length mismatch

- decompress rejects length mismatch


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("decompress rejects length mismatch")
var bad: [u8] = [0x0Au8, 0x10u8, 0x48u8, 0x65u8, 0x6cu8, 0x6cu8, 0x6fu8]
val result = try_snappy_decompress(bad)
check(result.is_err())
```

</details>

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

- Canonical SPipe generation for source `eaad64ff7505270c22c34464d2002d3ae9836eb54ddf149bec4e980a6efab978`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `eaad64ff7505270c22c34464d2002d3ae9836eb54ddf149bec4e980a6efab978`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `eaad64ff7505270c22c34464d2002d3ae9836eb54ddf149bec4e980a6efab978`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/compress/snappy_spec.spl
mirror: doc/06_spec/unit/lib/common/compress/snappy_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/compress/snappy_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/compress/snappy_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/compress/snappy_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trip empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress/snappy_spec.spl:41:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trip Hello World' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress/snappy_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'known vector Hello literal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
