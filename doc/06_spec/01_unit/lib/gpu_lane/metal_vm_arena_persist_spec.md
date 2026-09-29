# metal_vm_arena_persist_spec

> Proves `build_svmg_arena_persisting_data` copies prior DATA by absolute

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 7 | 7 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# metal_vm_arena_persist_spec

Proves `build_svmg_arena_persisting_data` copies prior DATA by absolute

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Proves `build_svmg_arena_persisting_data` copies prior DATA by absolute
    arena index, not relative to data_off, across cells whose code lengths
    DIFFER -- the only configuration in which the correct and the buggy form
    produce different bytes.

## Scenarios

### MetalVmExecutor arena carry-forward uses ABSOLUTE offsets

#### should preserve absolute DATA offsets when the next cell's code is LONGER

- should preserve absolute DATA offsets when the next cell's code is LONGER
- Prior launch ran the SHORT program; its data_off is 36+2=38
- Next cell is the LONGER program; its data_off is 36+13=49
- Carry the prior arena forward
- Values written by the prior launch keep their ABSOLUTE offsets
- The NEW cell's code is installed, not overwritten by prior DATA
- LOG and RECORD rings ride forward verbatim
- DBG-1 saved state rides forward, INCLUDING seq and record_count


<details>
<summary>Executable SSpec</summary>

Runnable source: 41 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve absolute DATA offsets when the next cell's code is LONGER")
step("Prior launch ran the SHORT program; its data_off is 36+2=38")
val short_code = svmg_asm(_SHORT_SRC)
val prior_data_off = SGP_HEADER_SIZE + short_code.len()
assert_equal(prior_data_off, 38)
val prior = _prior_arena_for(_SHORT_SRC)

step("Next cell is the LONGER program; its data_off is 36+13=49")
val long_code = svmg_asm(_LONG_SRC)
val next_data_off = SGP_HEADER_SIZE + long_code.len()
assert_equal(next_data_off, 49)
assert_true(next_data_off != prior_data_off)

step("Carry the prior arena forward")
val next = build_svmg_arena_persisting_data(long_code, 10000, 0, prior, prior_data_off)
assert_equal(next.len(), ARENA_TOTAL_SIZE)

step("Values written by the prior launch keep their ABSOLUTE offsets")
# A relative copy would have written prior[prior_data_off + (1000 -
# next_data_off)] = prior[989] here, which is zero -- so this
# assertion is exactly the regression fence.
assert_equal(_read_u32(next, _MARK_A), 0x11223344)
assert_equal(_read_u32(next, _MARK_B), 0x55667788)

step("The NEW cell's code is installed, not overwritten by prior DATA")
var i = 0
while i < long_code.len():
    assert_equal(next[SGP_HEADER_SIZE + i] as i64, long_code[i] as i64)
    i = i + 1

step("LOG and RECORD rings ride forward verbatim")
assert_equal(_read_u32(next, LOG_HEAD_OFFSET), 1)
assert_equal(next[LOG_DATA_OFFSET] as i64, 88)
val rec_base = LOG_DATA_OFFSET + DEFAULT_LOG_CAP
assert_equal(_read_u32(next, rec_base + 8), 42)

step("DBG-1 saved state rides forward, INCLUDING seq and record_count")
assert_equal(_read_u32(next, DBG_SAVED_PC_OFFSET), 5)
assert_equal(_read_u32(next, DBG_SAVED_SEQ_OFFSET), 9)
assert_equal(_read_u32(next, DBG_SAVED_RECORD_COUNT_OFFSET), 1)
```

</details>

#### should preserve absolute DATA offsets when the next cell's code is SHORTER

- should preserve absolute DATA offsets when the next cell's code is SHORTER
- Prior launch ran the LONG program (data_off 49); next cell is SHORT (38)
- Carry forward; copy_start must be max(38, 49) = 49
- Absolute offsets preserved in the shrink direction too
- The prior (longer) program's tail code bytes are NOT resurrected


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should preserve absolute DATA offsets when the next cell's code is SHORTER")
step("Prior launch ran the LONG program (data_off 49); next cell is SHORT (38)")
val long_code = svmg_asm(_LONG_SRC)
val prior_data_off = SGP_HEADER_SIZE + long_code.len()
val prior = _prior_arena_for(_LONG_SRC)
val short_code = svmg_asm(_SHORT_SRC)
val next_data_off = SGP_HEADER_SIZE + short_code.len()
assert_true(next_data_off < prior_data_off)

step("Carry forward; copy_start must be max(38, 49) = 49")
val next = build_svmg_arena_persisting_data(short_code, 10000, 0, prior, prior_data_off)

step("Absolute offsets preserved in the shrink direction too")
assert_equal(_read_u32(next, _MARK_A), 0x11223344)
assert_equal(_read_u32(next, _MARK_B), 0x55667788)

step("The prior (longer) program's tail code bytes are NOT resurrected " +
    "into the new cell's code region")
# Bytes [38, 49) belong to the prior program's code. copy_start=49
# means they are NOT copied, so they stay whatever the fresh build
# left them: zero, because the short program's code ends at 38.
var i = next_data_off
while i < prior_data_off:
    assert_equal(next[i] as i64, 0)
    i = i + 1
```

</details>

#### should degrade to a fresh build when there is no prior arena

- should degrade to a fresh build when there is no prior arena
- An empty prior arena means 'no prior state'
- A wrong-sized prior arena is also treated as 'no prior state',


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should degrade to a fresh build when there is no prior arena")
step("An empty prior arena means 'no prior state'")
val code = svmg_asm(_LONG_SRC)
val fresh = build_svmg_arena(code, 10000, 0)
val degraded = build_svmg_arena_persisting_data(code, 10000, 0, [], 0)
assert_equal(degraded.len(), fresh.len())
assert_equal(_read_u32(degraded, _MARK_A), 0)
assert_equal(_read_u32(degraded, LOG_CAP_OFFSET), DEFAULT_LOG_CAP)

step("A wrong-sized prior arena is also treated as 'no prior state', " +
    "never partially applied")
val truncated: [u8] = [1 as u8, 2 as u8, 3 as u8]
val degraded2 = build_svmg_arena_persisting_data(code, 10000, 0, truncated, 38)
assert_equal(degraded2.len(), ARENA_TOTAL_SIZE)
assert_equal(_read_u32(degraded2, _MARK_A), 0)
```

</details>

### MetalVmExecutor DBG-1 block placement and sentinel decoding

#### should place the DBG-1 block above ARENA_DATA_SIZE so bounds_ok hides it

- should place the DBG-1 block above ARENA_DATA_SIZE so bounds_ok hides it
- bounds_ok(offset,width) requires offset+width <= ARENA_DATA_SIZE
- ...and the block ends exactly at the top of the arena


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should place the DBG-1 block above ARENA_DATA_SIZE so bounds_ok hides it")
step("bounds_ok(offset,width) requires offset+width <= ARENA_DATA_SIZE")
# Therefore no LOAD32/STORE32/LOAD8/STORE8 can reach DBG_BASE_OFFSET:
# a program cannot scribble on its own debugger state.
assert_true(DBG_BASE_OFFSET >= ARENA_DATA_SIZE)
assert_equal(DBG_BASE_OFFSET, 0x1F000)
step("...and the block ends exactly at the top of the arena")
assert_equal(DBG_BASE_OFFSET + 0x1000, ARENA_TOTAL_SIZE)
```

</details>

#### should detect a debug break by SENTINEL identity, never by exit code

- should detect a debug break by SENTINEL identity, never by exit code
- SENTINEL_DEBUG_BREAK aliases a clean exit with code 0xDB
- A clean exit with a different code is NOT a debug break


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should detect a debug break by SENTINEL identity, never by exit code")
step("SENTINEL_DEBUG_BREAK aliases a clean exit with code 0xDB")
# This is the trap: 0xCAFE00DB is BOTH the debug-break sentinel and
# what `SENTINEL_EXIT_MASK | 0xDB` produces. Exit code 0xDB is
# therefore reserved, and only exact sentinel equality is sound.
assert_equal(SENTINEL_DEBUG_BREAK, SENTINEL_EXIT_MASK | 0xDB)
assert_true(debug_break_of(SENTINEL_DEBUG_BREAK))

step("A clean exit with a different code is NOT a debug break")
assert_false(debug_break_of(SENTINEL_EXIT_MASK | 0x00))
assert_false(debug_break_of(SENTINEL_EXIT_MASK | 0x7F))
assert_false(debug_break_of(SENTINEL_TIMEOUT))
assert_false(debug_break_of(0))
```

</details>

### MetalVmExecutor readback decoders

#### should decode sentinel, LOG text and RECORD ring from a synthetic arena

- should decode sentinel, LOG text and RECORD ring from a synthetic arena
- Stamp a synthetic post-launch arena
- Sentinel decodes to a clean exit with code 7
- LOG decodes to printable text with the newline preserved
- RECORD ring stops at the first all-zero record
- ...and a negative record value decodes as SIGNED i32, not 4294967295


<details>
<summary>Executable SSpec</summary>

Runnable source: 34 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should decode sentinel, LOG text and RECORD ring from a synthetic arena")
step("Stamp a synthetic post-launch arena")
var a = build_svmg_arena(svmg_asm(_SHORT_SRC), 10000, 0)
a = _write_u32(a, RAM_SENTINEL_OFFSET, SENTINEL_EXIT_MASK | 0x07)
# LOG: "Hi\n"
a[LOG_DATA_OFFSET + 0] = 72 as u8
a[LOG_DATA_OFFSET + 1] = 105 as u8
a[LOG_DATA_OFFSET + 2] = 10 as u8
a = _write_u32(a, LOG_HEAD_OFFSET, 3)
val rec_base = LOG_DATA_OFFSET + DEFAULT_LOG_CAP
a = _write_u32(a, rec_base + 0, 1)
a = _write_u32(a, rec_base + 4, 1)
a = _write_u32(a, rec_base + 8, 123)
# Second record carries a NEGATIVE value (raw u32 wire pattern).
a = _write_u32(a, rec_base + RECORD_SIZE + 0, 2)
a = _write_u32(a, rec_base + RECORD_SIZE + 4, 0)
a = _write_u32(a, rec_base + RECORD_SIZE + 8, 0xFFFFFFFF)

step("Sentinel decodes to a clean exit with code 7")
assert_equal(read_sentinel(a), SENTINEL_EXIT_MASK | 0x07)
assert_false(debug_break_of(read_sentinel(a)))

step("LOG decodes to printable text with the newline preserved")
assert_equal(read_log(a), "Hi\n")

step("RECORD ring stops at the first all-zero record")
val recs = read_records(a, 64)
assert_equal(recs.len(), 2)
assert_equal(recs[0].passed, 1)
assert_equal(recs[0].value, 123)
step("...and a negative record value decodes as SIGNED i32, not 4294967295")
assert_equal(recs[1].passed, 0)
assert_equal(recs[1].value, -1)
```

</details>

#### should expose the Metal kernel entry point name the pipeline is built against

- should expose the Metal kernel entry point name the pipeline is built against
- MetalLaneSession.init passes this to rt_metal_create_compute_pipeline
- Step budget default is shared with the CUDA/Vulkan lanes


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("should expose the Metal kernel entry point name the pipeline is built against")
step("MetalLaneSession.init passes this to rt_metal_create_compute_pipeline")
assert_equal(SVMG_ENTRY, "svmg_interpret")
step("Step budget default is shared with the CUDA/Vulkan lanes")
assert_equal(DEFAULT_STEP_BUDGET, 100000)
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

- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `d3d04804be245f2da3d154b072274a02b26b7ac2cabc75b0c97605f82ded23b5`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d3d04804be245f2da3d154b072274a02b26b7ac2cabc75b0c97605f82ded23b5`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d3d04804be245f2da3d154b072274a02b26b7ac2cabc75b0c97605f82ded23b5`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl:100:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve absolute DATA offsets when the next cell's code is LONGER' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl:100:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve absolute DATA offsets when the next cell's code is LONGER' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl:143:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should preserve absolute DATA offsets when the next cell's code is SHORTER' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl:143:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should preserve absolute DATA offsets when the next cell's code is SHORTER' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl:171:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should degrade to a fresh build when there is no prior arena' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl:171:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should degrade to a fresh build when there is no prior arena' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl:196:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should place the DBG-1 block above ARENA_DATA_SIZE so bounds_ok hides it' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl:207:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should detect a debug break by SENTINEL identity, never by exit code' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_vm_arena_persist_spec.spl:229:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should decode sentinel, LOG text and RECORD ring from a synthetic arena' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
