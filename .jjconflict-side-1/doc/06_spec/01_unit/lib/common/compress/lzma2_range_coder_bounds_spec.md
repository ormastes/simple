# Lzma2 Range Coder Bounds Specification

> Tests covering LZMA range coder bounds validation.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 9 | 9 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Lzma2 Range Coder Bounds Specification

## Scenarios

### LZMA range coder bounds validation

#### rejects negative range positions before indexing

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- rejects negative range positions before indexing
   - Expected: result.is_err() is true
   - Expected: false is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative range positions before indexing")
val probs: [u32] = [1024u32]
val input: [u8] = [0x00u8]
val rd = LzmaRange(range_v: 0u32, code_v: 0u32, pos: -1)
val result = _lzma_decode_bit(rd, probs, 0, input)
expect(result.is_err()).to_equal(true)
val err = result.unwrap_err()
match err:
    CompressionError.TruncatedInput(message):
        expect(message).to_contain("range decoder")
    _:
        expect(false).to_equal(true)
```

</details>

#### rejects probability indexes outside the table

- rejects probability indexes outside the table


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects probability indexes outside the table")
val probs: [u32] = [1024u32]
val input: [u8] = []
expect_corrupt_bit(_lzma_decode_bit(fresh_range(), probs, 2, input), "probability index")
```

</details>

#### rejects negative bittree offsets before indexing

- rejects negative bittree offsets before indexing


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative bittree offsets before indexing")
val probs: [u32] = [1024u32, 1024u32]
val input: [u8] = []
expect_corrupt_bit(_lzma_decode_bittree(fresh_range(), probs, -1, 1, input), "bittree offset")
```

</details>

#### rejects bittree widths that would overflow shift-derived ranges

- rejects bittree widths that would overflow shift-derived ranges


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bittree widths that would overflow shift-derived ranges")
val probs: [u32] = [1024u32, 1024u32]
val input: [u8] = []
expect_corrupt_bit(_lzma_decode_bittree_reverse(fresh_range(), probs, 0, 31, input), "bittree width")
```

</details>

#### rejects bittree spans beyond the probability table

- rejects bittree spans beyond the probability table


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects bittree spans beyond the probability table")
val probs: [u32] = [1024u32, 1024u32]
val input: [u8] = []
expect_corrupt_bit(_lzma_decode_bittree(fresh_range(), probs, 1, 1, input), "bittree range")
```

</details>

#### rejects negative direct bit counts

- rejects negative direct bit counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects negative direct bit counts")
val input: [u8] = []
expect_corrupt_direct(_lzma_decode_direct(fresh_range(), -1, input), "direct bit count")
```

</details>

#### rejects oversized direct bit counts

- rejects oversized direct bit counts


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects oversized direct bit counts")
val input: [u8] = []
expect_corrupt_direct(_lzma_decode_direct(fresh_range(), 31, input), "direct bit count")
```

</details>

#### rejects length decoder pos_state values outside the four-state table

- rejects length decoder pos_state values outside the four-state table


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects length decoder pos_state values outside the four-state table")
val probs = _lzma_init_probs(LZMA_PROBS_TOTAL)
val input: [u8] = []
expect_corrupt_bit(_lzma_decode_len(fresh_range(), probs, LZMA_PROBS_LEN_BASE, -1, input), "length pos_state")
expect_corrupt_bit(_lzma_decode_len(fresh_range(), probs, LZMA_PROBS_LEN_BASE, 4, input), "length pos_state")
```

</details>

#### rejects distance decoding for lengths below the LZMA match minimum

- rejects distance decoding for lengths below the LZMA match minimum


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects distance decoding for lengths below the LZMA match minimum")
val probs = _lzma_init_probs(LZMA_PROBS_TOTAL)
val input: [u8] = []
expect_corrupt_bit(_lzma_decode_distance(fresh_range(), probs, LZMA_MATCH_MIN_LEN - 1, input), "distance length")
expect_corrupt_bit(_lzma_decode_distance_lclp(fresh_range(), probs, LZMA_MATCH_MIN_LEN - 1, input, 3, 0), "distance length")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/common/compress/lzma2_range_coder_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering LZMA range coder bounds validation.
- LZMA range coder bounds validation

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 9 |
| Active scenarios | 9 |
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

- Canonical SPipe generation for source `47f37186f8d2de8e0b75da4f48d60e466b3c0d3ca0bee2622397ad9313e2a980`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `47f37186f8d2de8e0b75da4f48d60e466b3c0d3ca0bee2622397ad9313e2a980`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `47f37186f8d2de8e0b75da4f48d60e466b3c0d3ca0bee2622397ad9313e2a980`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/common/compress/lzma2_range_coder_bounds_spec.spl
mirror: doc/06_spec/01_unit/lib/common/compress/lzma2_range_coder_bounds_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/common/compress/lzma2_range_coder_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/common/compress/lzma2_range_coder_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/common/compress/lzma2_range_coder_bounds_spec.spl:35:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative range positions before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/lzma2_range_coder_bounds_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects probability indexes outside the table' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/common/compress/lzma2_range_coder_bounds_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects negative bittree offsets before indexing' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
