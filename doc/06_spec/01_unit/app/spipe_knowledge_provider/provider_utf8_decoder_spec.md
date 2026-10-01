# Provider Utf8 Decoder Specification

> Tests covering SPipe provider strict incremental UTF-8 decoder.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Provider Utf8 Decoder Specification

## Scenarios

### SPipe provider strict incremental UTF-8 decoder

#### decodes exact scalar boundaries and charges admitted work before growth

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


<details>
<summary>Executable SSpec</summary>

Runnable source: 1 line folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-UTF8
```

</details>

#### preserves explicit carry at every split position without retaining prefixes

- preserves explicit carry at every split position without retaining prefixes


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("preserves explicit carry at every split position without retaining prefixes")
expect_split_scalar([194u8, 162u8], 1, 162)
expect_split_scalar([226u8, 130u8, 172u8], 1, 8364)
expect_split_scalar([226u8, 130u8, 172u8], 2, 8364)
expect_split_scalar([240u8, 159u8, 152u8, 128u8], 1, 128512)
expect_split_scalar([240u8, 159u8, 152u8, 128u8], 2, 128512)
expect_split_scalar([240u8, 159u8, 152u8, 128u8], 3, 128512)
```

</details>

#### rejects invalid leaders, continuations, overlong forms, and scalar exclusions

- rejects invalid leaders, continuations, overlong forms, and scalar exclusions


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects invalid leaders, continuations, overlong forms, and scalar exclusions")
expect_invalid_utf8([128u8])
expect_invalid_utf8([192u8, 128u8])
expect_invalid_utf8([193u8, 191u8])
expect_invalid_utf8([245u8, 128u8, 128u8, 128u8])
expect_invalid_utf8([255u8])
expect_invalid_utf8([226u8, 40u8, 161u8])
expect_invalid_utf8([224u8, 128u8, 128u8])
expect_invalid_utf8([240u8, 128u8, 128u8, 128u8])
expect_invalid_utf8([237u8, 160u8, 128u8])
expect_invalid_utf8([244u8, 144u8, 128u8, 128u8])
# Reject impossible prefixes as soon as their first continuation is
# known; a later byte can never repair any of these prefixes.
expect_invalid_utf8([224u8, 128u8], false)
expect_invalid_utf8([237u8, 160u8], false)
expect_invalid_utf8([240u8, 128u8], false)
expect_invalid_utf8([244u8, 144u8], false)
```

</details>

#### rejects every incomplete final sequence and accepts it only before final

- rejects every incomplete final sequence and accepts it only before final
   - Expected: decoder.carry_bytes_count() equals `3`


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects every incomplete final sequence and accepts it only before final")
expect_invalid_utf8([194u8])
expect_invalid_utf8([226u8])
expect_invalid_utf8([226u8, 130u8])
expect_invalid_utf8([240u8])
expect_invalid_utf8([240u8, 159u8])
expect_invalid_utf8([240u8, 159u8, 152u8])

var decoder = ProviderUtf8DecoderV1.configured()
var budget = utf8_budget()
var checkpoint = utf8_checkpoint()
expect(decoder.push([240u8, 159u8, 152u8], 0, 3, false,
    budget, checkpoint).unwrap()).to_equal([])
expect(decoder.carry_bytes_count()).to_equal(3)
expect(decoder.push([128u8], 0, 1, true,
    budget, checkpoint).unwrap()).to_equal([128512])
```

</details>

#### bounds checkpoint gaps and propagates budget and checkpoint rejection

- bounds checkpoint gaps and propagates budget and checkpoint rejection
   - Expected: checkpoint.checkpoint_count equals `4`
   - Expected: limited_decoder.carry_bytes_count() equals `0`
   - Expected: stopped_decoder.carry_bytes_count() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("bounds checkpoint gaps and propagates budget and checkpoint rejection")
var bytes: [u8] = []
var i = 0
while i < 4096:
    bytes.push(97u8)
    i = i + 1
var decoder = ProviderUtf8DecoderV1.configured()
var budget = utf8_budget()
var checkpoint = utf8_checkpoint()
expect(decoder.push(bytes, 0, bytes.len(), true,
    budget, checkpoint).unwrap().len()).to_equal(4096)
expect(checkpoint.checkpoint_count).to_equal(4)

var oversized_decoder = ProviderUtf8DecoderV1.configured()
var oversized_budget = utf8_budget()
var oversized_checkpoint = utf8_checkpoint()
bytes.push(97u8)
expect(oversized_decoder.push(bytes, 0, bytes.len(), true,
    oversized_budget, oversized_checkpoint)).to_equal(
        Err("limit_exceeded"))
expect(oversized_budget.consumed(
    provider_budget_category_raw_bytes())).to_equal(0)

var limited_decoder = ProviderUtf8DecoderV1.configured()
var limited_budget = utf8_budget(1, 1, 0, 0)
var limited_checkpoint = utf8_checkpoint()
expect(limited_decoder.push([65u8], 0, 1, true,
    limited_budget, limited_checkpoint)).to_equal(Err("limit_exceeded"))
expect(limited_budget.consumed(
    provider_budget_category_logical_allocations())).to_equal(0)
expect(limited_decoder.carry_bytes_count()).to_equal(0)
expect(limited_decoder.push([65u8], 0, 1, true,
    limited_budget, limited_checkpoint)).to_equal(Err("limit_exceeded"))

var stopped_decoder = ProviderUtf8DecoderV1.configured()
var stopped_budget = utf8_budget()
var stopped_checkpoint = utf8_checkpoint(0, "deadline_exceeded")
expect(stopped_decoder.push([65u8], 0, 1, true,
    stopped_budget, stopped_checkpoint)).to_equal(
        Err("deadline_exceeded"))
expect(stopped_decoder.carry_bytes_count()).to_equal(0)
expect(stopped_decoder.push([66u8], 0, 1, true,
    stopped_budget, stopped_checkpoint)).to_equal(
        Err("deadline_exceeded"))
```

</details>

#### decodes the same owned scalars across varied deterministic partitions

- decodes the same owned scalars across varied deterministic partitions
   - Expected: actual equals `expected`
   - Expected: decode_with_partitions(encoded, [1, 3, 2, 5]) equals `expected`
   - Expected: decode_with_partitions(encoded, [4, 1, 1, 3, 2]) equals `expected`
   - Expected: decode_with_partitions(encoded, [6, 2, 1, 2]) equals `expected`
   - Expected: decode_with_seeded_partitions(encoded, 1) equals `expected`
   - Expected: decode_with_seeded_partitions(encoded, 7) equals `expected`
   - Expected: decode_with_seeded_partitions(encoded, 42) equals `expected`
   - Expected: decode_with_seeded_partitions(encoded, 20260825) equals `expected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 38 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("decodes the same owned scalars across varied deterministic partitions")
val encoded = [65u8, 194u8, 162u8, 226u8, 130u8, 172u8,
    240u8, 159u8, 152u8, 128u8, 66u8,
    101u8, 204u8, 129u8]
# Keep decomposed `e` + U+0301 explicit: this decoder validates and
# owns Unicode scalars; a later normalization stage owns NFC changes.
val expected = [65, 162, 8364, 128512, 66, 101, 769]
for width in 1..5:
    var decoder = ProviderUtf8DecoderV1.configured()
    var budget = utf8_budget()
    var checkpoint = utf8_checkpoint()
    var actual: [i64] = []
    var offset = 0
    while offset < encoded.len():
        var take = width
        if take > encoded.len() - offset:
            take = encoded.len() - offset
        val final_chunk = offset + take == encoded.len()
        val chunk = decoder.push(encoded, offset, take, final_chunk,
            budget, checkpoint).unwrap()
        for scalar in chunk:
            actual.push(scalar)
        offset = offset + take
    expect(actual).to_equal(expected)

# Fixed mixed partitions deliberately cross the two-, three-, and
# four-byte scalar boundaries in different combinations.
expect(decode_with_partitions(encoded, [1, 3, 2, 5])).to_equal(expected)
expect(decode_with_partitions(encoded, [4, 1, 1, 3, 2])).to_equal(expected)
expect(decode_with_partitions(encoded, [6, 2, 1, 2])).to_equal(expected)

# Fixed seeds provide deterministic pseudo-random partitions without
# introducing a flaky runtime RNG dependency.
expect(decode_with_seeded_partitions(encoded, 1)).to_equal(expected)
expect(decode_with_seeded_partitions(encoded, 7)).to_equal(expected)
expect(decode_with_seeded_partitions(encoded, 42)).to_equal(expected)
expect(decode_with_seeded_partitions(encoded, 20260825)).to_equal(expected)
```

</details>

#### rejects invalid ranges before work and remains terminal

- rejects invalid ranges before work and remains terminal


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("rejects invalid ranges before work and remains terminal")
expect_invalid_range(-1, 1)
expect_invalid_range(0, -1)
expect_invalid_range(2, 0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering SPipe provider strict incremental UTF-8 decoder.
- SPipe provider strict incremental UTF-8 decoder

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

- `REQ-SSPEC-APP`
- `REQ-UTF8`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `3cfd87af7bd4fae4963dd23283a8927c6e4a2b47cd82246680549cafb017a57f`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `3cfd87af7bd4fae4963dd23283a8927c6e4a2b47cd82246680549cafb017a57f`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `3cfd87af7bd4fae4963dd23283a8927c6e4a2b47cd82246680549cafb017a57f`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **85/100**; effective score: **85/100**; blockers: **0**.

SSpec documentization score: 85/100
source: test/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.spl
mirror: doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.md (current)
findings: 7 blockers: 0
  narrative=100 structure=90 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.spl:117:1: warning SSDOC-BEH-001 [structure] (-10): scenario 'decodes exact scalar boundaries and charges admitted work before growth' has no visible step flow
  why: Ordered visible actions make the manual operable.
  improve: Add ordered step("...") calls for meaningful actions.
test/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.spl:142:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'preserves explicit carry at every split position without retaining prefixes' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.spl:152:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects invalid leaders, continuations, overlong forms, and scalar exclusions' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/spipe_knowledge_provider/provider_utf8_decoder_spec.spl:172:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'rejects every incomplete final sequence and accepts it only before final' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
