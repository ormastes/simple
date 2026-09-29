# LZ4 Block Compression Round-Trip Tests

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# LZ4 Block Compression Round-Trip Tests

## At a Glance

| Field | Value |
|-------|-------|
| Feature IDs | #COMPRESS-LZ4 |
| Category | Compression |
| Status | Implemented |
| Source | `test/unit/lib/common/compress/lz4_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Scenarios

### LZ4 block compression

#### round-trip Hello World

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- round-trip Hello World


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip Hello World")
val data = _make_hello_world_bytes()
val compressed = lz4_compress_block(data)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 13)
check(decompressed[0] == 0x48u8)
check(decompressed[1] == 0x65u8)
check(decompressed[4] == 0x6fu8)
check(decompressed[12] == 0x21u8)
```

</details>

#### round-trip repeated data compresses

- round-trip repeated data compresses


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip repeated data compresses")
val data = _make_repeated_bytes(0x41u8, 10)
val compressed = lz4_compress_block(data)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 10)
check(decompressed[0] == 0x41u8)
check(decompressed[9] == 0x41u8)
```

</details>

#### round-trip empty input

- round-trip empty input


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip empty input")
var empty: [u8] = []
val compressed = lz4_compress_block(empty)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 0)
```

</details>

#### round-trip longer data 128 bytes

- round-trip longer data 128 bytes


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("round-trip longer data 128 bytes")
val data = _make_sequential_bytes(128)
val compressed = lz4_compress_block(data)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 128)
check(decompressed[0] == 0x00u8)
check(decompressed[127] == 0x7fu8)
```

</details>

#### repeated data compressed is smaller

- repeated data compressed is smaller


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("repeated data compressed is smaller")
val data = _make_repeated_bytes(0x42u8, 1000)
val compressed = lz4_compress_block_with_level(data, 6)
check(compressed.len() < 1000)
val result = lz4_decompress_block(compressed)
check(result.is_ok())
val decompressed = result.unwrap()
check(decompressed.len() == 1000)
check(decompressed[0] == 0x42u8)
check(decompressed[999] == 0x42u8)
```

</details>

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

- Canonical SPipe generation for source `d0a11f28b5d8b7658067e6939f5da31ffd9b2150291bc2b5c1e50b3bbfc3a85c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d0a11f28b5d8b7658067e6939f5da31ffd9b2150291bc2b5c1e50b3bbfc3a85c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d0a11f28b5d8b7658067e6939f5da31ffd9b2150291bc2b5c1e50b3bbfc3a85c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/unit/lib/common/compress/lz4_spec.spl
mirror: doc/06_spec/unit/lib/common/compress/lz4_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/lib/common/compress/lz4_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/lib/common/compress/lz4_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/lib/common/compress/lz4_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trip Hello World' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress/lz4_spec.spl:58:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trip repeated data compresses' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/lib/common/compress/lz4_spec.spl:70:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'round-trip empty input' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
