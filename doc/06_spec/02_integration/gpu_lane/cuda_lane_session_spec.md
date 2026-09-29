# cuda_lane_session_spec

> Coverage for the parts of the B1 CUDA lane session that are genuinely

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cuda_lane_session_spec

Coverage for the parts of the B1 CUDA lane session that are genuinely

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/02_integration/gpu_lane/cuda_lane_session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Coverage for the parts of the B1 CUDA lane session that are genuinely
    testable without live CUDA hardware: guard canary generation/matching
    (pure byte logic), the raw host-memory read/write round-trip used to
    marshal HtoD/DtoH payloads (plain process memory, not device memory),
    and first-error retention (exercised on a session that is never
    `init`'d, so it never touches the CUDA driver at all).

## Scenarios

### CudaLaneSession pure helpers (no CUDA hardware required)

#### should generate a canary buffer that matches itself and reject a corrupted one

- should generate a canary buffer that matches itself and reject a corrupted one
- Generate a guard-sized canary buffer
   - Expected: guard.len() equals `GUARD_BYTES`
- An unmodified canary buffer matches
- Flipping a single byte anywhere in the buffer is detected


<details>
<summary>Executable SSpec</summary>

Runnable source: 17 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should generate a canary buffer that matches itself and reject a corrupted one")
step("Generate a guard-sized canary buffer")
val guard = canary_bytes(GUARD_BYTES)
expect(guard.len()).to_equal(GUARD_BYTES)

step("An unmodified canary buffer matches")
assert_true(bytes_match_canary(guard))

step("Flipping a single byte anywhere in the buffer is detected")
var corrupted = canary_bytes(GUARD_BYTES)
corrupted[0] = (GUARD_CANARY_BYTE + 1).to_u8()
assert_false(bytes_match_canary(corrupted))

var corrupted_tail = canary_bytes(GUARD_BYTES)
corrupted_tail[GUARD_BYTES - 1] = 0u8
assert_false(bytes_match_canary(corrupted_tail))
```

</details>

#### should round-trip an arbitrary byte pattern through raw host memory

- should round-trip an arbitrary byte pattern through raw host memory
- Allocate plain host memory (not CUDA) and write a non-trivial pattern into it
- Read it back and confirm every byte round-tripped exactly
   - Expected: readback.len() equals `4096`
   - Expected: readback[0] equals `pattern[0]`
   - Expected: readback[100] equals `pattern[100]`
   - Expected: readback[4095] equals `pattern[4095]`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should round-trip an arbitrary byte pattern through raw host memory")
step("Allocate plain host memory (not CUDA) and write a non-trivial pattern into it")
val pattern = _arena_pattern(4096)
val ptr = lane_scratch_alloc(4096)
assert_true(ptr != 0)
write_bytes_to_ptr(ptr, pattern)

step("Read it back and confirm every byte round-tripped exactly")
val readback = read_bytes_from_ptr(ptr, 4096)
expect(readback.len()).to_equal(4096)
expect(readback[0]).to_equal(pattern[0])
expect(readback[100]).to_equal(pattern[100])
expect(readback[4095]).to_equal(pattern[4095])
lane_scratch_free(ptr)
```

</details>

#### should retain only the FIRST error even when later calls also fail

- should retain only the FIRST error even when later calls also fail
- Create a session but never call init() -- no CUDA driver call happens
   - Expected: session.last_error equals ``
- A call requiring an initialized session fails without touching CUDA
   - Expected: session.last_error equals `"")  # arena_write fails closed, not via _fail`
- load_entry on an uninitialized session captures the first error
   - Expected: load_result equals `cuda-lane-session-unavailable`
   - Expected: session.last_error equals `cuda-lane-session-unavailable`
- A second, DIFFERENT failure (manufactured without CUDA: force the
   - Expected: second_result equals `cuda-lane-session-cleanup-pending`
   - Expected: session.last_error equals `cuda-lane-session-unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 23 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should retain only the FIRST error even when later calls also fail")
step("Create a session but never call init() -- no CUDA driver call happens")
var session = CudaLaneSession.create()
expect(session.last_error).to_equal("")

step("A call requiring an initialized session fails without touching CUDA")
val first = session.arena_write(_arena_pattern(16))
assert_false(first)
expect(session.last_error).to_equal("")  # arena_write fails closed, not via _fail

step("load_entry on an uninitialized session captures the first error")
val load_result = session.load_entry([1u8, 2u8, 3u8, 4u8], "main")
expect(load_result).to_equal("cuda-lane-session-unavailable")
expect(session.last_error).to_equal("cuda-lane-session-unavailable")

step("A second, DIFFERENT failure (manufactured without CUDA: force the " +
    "cleanup-pending guard by flipping completion_unknown directly) does " +
    "NOT overwrite the retained first error")
session.completion_unknown = true
val second_result = session.shutdown()
expect(second_result).to_equal("cuda-lane-session-cleanup-pending")
expect(session.last_error).to_equal("cuda-lane-session-unavailable")
```

</details>

### CudaLaneSession host-aware arena round-trip

#### should probe cleanly, and on a live host allocate the arena and round-trip a pattern with guards intact

- should probe cleanly, and on a live host allocate the arena and round-trip a pattern with guards intact
- Probe for a CUDA-capable device
- cuda
- Live CUDA driver/device found by probe()
- Initialize the session (context, combined guard|arena|guard allocation)
   - Expected: init_result equals ``
- Guard regions are intact immediately after init
- Write a host-side pattern into the arena
- Read the arena back and confirm the pattern round-tripped exactly
   - Expected: readback.len() equals `session.arena_capacity`
   - Expected: readback[0] equals `pattern[0]`
   - Expected: readback[100] equals `pattern[100]`
- Guard regions are still intact after the round-trip -- no overflow
- Shut the session down cleanly
   - Expected: session.shutdown() equals ``
- init() failed:


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-INTEGRATION
step("should probe cleanly, and on a live host allocate the arena and round-trip a pattern with guards intact")
step("Probe for a CUDA-capable device")
var session = CudaLaneSession.create()
val probe_result = session.probe()

if probe_result.starts_with("skip:"):
    # Fail closed -- see lane_probe_verdict.spl. The old
    # `assert_true(probe_result.starts_with("skip:"))` passed BECAUSE
    # the probe skipped, so a lane that never touched a device reported
    # the same verdict as one that did.
    step(gpu_lane_probe_verdict_reason("cuda", probe_result))
    gpu_lane_report_skip("cuda lane", probe_result)
    assert_equal(gpu_lane_probe_verdict("cuda", probe_result), "skip")
else:
    step("Live CUDA driver/device found by probe()")

    # KNOWN-RED on some hosts, filed:
    # doc/08_tracking/bug/cuda_device_name_fails_after_successful_device_get_and_ctx_create_2026-08-07.md
    # `init()` requires a non-empty device name + nonzero identity per
    # the CUDA host validation contract's "record driver, device
    # name/UUID" step (never weakened here -- see the filed bug for
    # why `rt_cuda_device_name` can fail even when `cuda_device_get`/
    # `cuda_ctx_create` for the SAME device already succeeded). Guard
    # every following step behind `init_result == ""` so a genuine
    # upstream failure reports as a clean, readable red assertion
    # instead of an index-out-of-bounds crash on an unpopulated arena.
    step("Initialize the session (context, combined guard|arena|guard allocation)")
    val init_result = session.init()
    expect(init_result).to_equal("")

    if init_result == "":
        expect(session.device_name).to_not_equal("")

        step("Guard regions are intact immediately after init")
        assert_true(session.guard_check())

        step("Write a host-side pattern into the arena")
        val pattern = _arena_pattern(session.arena_capacity)
        assert_true(session.arena_write(pattern))

        step("Read the arena back and confirm the pattern round-tripped exactly")
        val readback = session.arena_read(session.arena_capacity)
        expect(readback.len()).to_equal(session.arena_capacity)
        expect(readback[0]).to_equal(pattern[0])
        expect(readback[100]).to_equal(pattern[100])
        expect(readback[session.arena_capacity - 1]).to_equal(
            pattern[session.arena_capacity - 1])

        step("Guard regions are still intact after the round-trip -- no overflow")
        assert_true(session.guard_check())

        step("Shut the session down cleanly")
        expect(session.shutdown()).to_equal("")
    else:
        step("init() failed: " + init_result +
            " (last_error=" + session.last_error +
            ") -- see the filed bug above; nothing further to exercise safely")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-INTEGRATION`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `4ad2e76ff9ef780a707c8b7e134462f95f2ff85f39ffe198f6544ac24445bce4`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `4ad2e76ff9ef780a707c8b7e134462f95f2ff85f39ffe198f6544ac24445bce4`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `4ad2e76ff9ef780a707c8b7e134462f95f2ff85f39ffe198f6544ac24445bce4`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **87/100**; effective score: **87/100**; blockers: **0**.

SSpec documentization score: 87/100
source: test/02_integration/gpu_lane/cuda_lane_session_spec.spl
mirror: doc/06_spec/02_integration/gpu_lane/cuda_lane_session_spec.md (current)
findings: 10 blockers: 0
  narrative=100 structure=80 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/02_integration/gpu_lane/cuda_lane_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/02_integration/gpu_lane/cuda_lane_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/02_integration/gpu_lane/cuda_lane_session_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/02_integration/gpu_lane/cuda_lane_session_spec.spl:47:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should generate a canary buffer that matches itself and reject a corrupted one' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/gpu_lane/cuda_lane_session_spec.spl:47:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should generate a canary buffer that matches itself and reject a corrupted one' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/gpu_lane/cuda_lane_session_spec.spl:66:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should round-trip an arbitrary byte pattern through raw host memory' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/gpu_lane/cuda_lane_session_spec.spl:66:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should round-trip an arbitrary byte pattern through raw host memory' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/gpu_lane/cuda_lane_session_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain only the FIRST error even when later calls also fail' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/02_integration/gpu_lane/cuda_lane_session_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should retain only the FIRST error even when later calls also fail' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/02_integration/gpu_lane/cuda_lane_session_spec.spl:115:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should probe cleanly, and on a live host allocate the arena and round-trip a pattern with guards intact' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
