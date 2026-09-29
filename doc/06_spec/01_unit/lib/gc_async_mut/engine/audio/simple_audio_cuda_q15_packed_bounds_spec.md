# Q15 CUDA staging-buffer bounds

> As an audio-engine maintainer I need the Q15 CUDA staging writer to be sized by

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Q15 CUDA staging-buffer bounds

As an audio-engine maintainer I need the Q15 CUDA staging writer to be sized by

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15_packed_bounds_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

As an audio-engine maintainer I need the Q15 CUDA staging writer to be sized by
the *packed* byte count, not the lane count, so an odd-length payload can never
write past the end of its host allocation.

The packed form stores two u32 lanes per i64 word, so an odd lane count still
touches a whole trailing 8-byte word. A `count * 4` allocation is 4 bytes short
of that word, and the old writer wrote into it unconditionally.

## Scenarios

### Q15 CUDA staging buffer bounds

#### sizes odd payloads to a whole trailing word, above the naive count*4

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- sizes odd payloads to a whole trailing word, above the naive count*4
- even lane counts pack exactly
   - Expected: simple_audio_q15_packed_bytes(0) equals `0`
   - Expected: simple_audio_q15_packed_bytes(2) equals `8`
   - Expected: simple_audio_q15_packed_bytes(4) equals `16`
- odd lane counts round up to the whole word actually written
   - Expected: simple_audio_q15_packed_bytes(1) equals `8`
   - Expected: simple_audio_q15_packed_bytes(3) equals `16`
   - Expected: simple_audio_q15_packed_bytes(5) equals `24`
- the packed size is never smaller than the write reaches


<details>
<summary>Executable SSpec</summary>

Runnable source: 19 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("sizes odd payloads to a whole trailing word, above the naive count*4")
step("even lane counts pack exactly")
expect(simple_audio_q15_packed_bytes(0)).to_equal(0)
expect(simple_audio_q15_packed_bytes(2)).to_equal(8)
expect(simple_audio_q15_packed_bytes(4)).to_equal(16)

step("odd lane counts round up to the whole word actually written")
# 3 lanes: the naive `3 * 4 == 12` byte allocation is what overran.
expect(simple_audio_q15_packed_bytes(1)).to_equal(8)
expect(simple_audio_q15_packed_bytes(3)).to_equal(16)
expect(simple_audio_q15_packed_bytes(5)).to_equal(24)

step("the packed size is never smaller than the write reaches")
var lanes = 1
while lanes <= 33:
    val words = (lanes + 1) / 2
    expect(simple_audio_q15_packed_bytes(lanes)).to_be_greater_than(words * 8 - 1)
    lanes = lanes + 1
```

</details>

#### refuses to stage a payload into an undersized buffer

- refuses to stage a payload into an undersized buffer
- a count*4 capacity is rejected instead of overrun
- one byte short of the packed size is still rejected
- a null destination is rejected


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("refuses to stage a payload into an undersized buffer")
val values: [u32] = [1u32, 2u32, 3u32]
val naive_bytes = 3 * 4

step("a count*4 capacity is rejected instead of overrun")
assert_false(simple_audio_q15_write_packed(1024, values, naive_bytes))

step("one byte short of the packed size is still rejected")
assert_false(simple_audio_q15_write_packed(1024, values, simple_audio_q15_packed_bytes(3) - 1))

step("a null destination is rejected")
assert_false(simple_audio_q15_write_packed(0, values, 4096))
```

</details>

#### stages an odd payload into a correctly sized buffer

- stages an odd payload into a correctly sized buffer
- the write is accepted at exactly the packed capacity
- both packed words read back with the lanes and a zero-filled tail
   - Expected: rt_ptr_read_i64(ptr, 0) equals `7 | (9 << 32)`
   - Expected: rt_ptr_read_i64(ptr, 8) equals `11`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stages an odd payload into a correctly sized buffer")
val values: [u32] = [7u32, 9u32, 11u32]
val bytes = simple_audio_q15_packed_bytes(3)
val ptr = raw_alloc(bytes)
assert_true(ptr != 0)

step("the write is accepted at exactly the packed capacity")
assert_true(simple_audio_q15_write_packed(ptr, values, bytes))

step("both packed words read back with the lanes and a zero-filled tail")
expect(rt_ptr_read_i64(ptr, 0)).to_equal(7 | (9 << 32))
expect(rt_ptr_read_i64(ptr, 8)).to_equal(11)
raw_free(ptr, bytes)
```

</details>

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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `cb1a6fc8164221206c4061bf1fe4aee1c98e8f2cca3d7731977b3fe643629434`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `cb1a6fc8164221206c4061bf1fe4aee1c98e8f2cca3d7731977b3fe643629434`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `cb1a6fc8164221206c4061bf1fe4aee1c98e8f2cca3d7731977b3fe643629434`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **86/100**; blockers: **0**.

SSpec documentization score: 86/100
source: test/01_unit/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15_packed_bounds_spec.spl
mirror: doc/06_spec/01_unit/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15_packed_bounds_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15_packed_bounds_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15_packed_bounds_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15_packed_bounds_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 7 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15_packed_bounds_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'sizes odd payloads to a whole trailing word, above the naive count*4' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15_packed_bounds_spec.spl:51:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'refuses to stage a payload into an undersized buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gc_async_mut/engine/audio/simple_audio_cuda_q15_packed_bounds_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'stages an odd payload into a correctly sized buffer' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
