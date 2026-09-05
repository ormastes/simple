# Audio Capture Specification

> Tests covering audio capture (recording).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 3 | 3 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Audio Capture Specification

## Scenarios

### audio capture (recording)

#### fail-closed: on a host with no capture device, start() reports inactive and creates no file

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- fail-closed: on a host with no capture device, start() reports inactive and creates no file
   - Expected: file_exists(tmp_path) is false
   - Expected: audio_capture_is_active() is false
   - Expected: audio_capture_is_active() is true
   - Expected: file_exists(tmp_path) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("fail-closed: on a host with no capture device, start() reports inactive and creates no file")
val engine = audio_init()
val tmp_path = "/tmp/simple_audio_capture_test_{getpid()}.wav"
val cap = audio_capture_start(tmp_path, 8000, 1)
if not cap.active:
    # No capture device (expected in headless CI): no file, no active session.
    expect(file_exists(tmp_path)).to_equal(false)
    expect(audio_capture_is_active()).to_equal(false)
else:
    # A real capture device is present: a session is active and can be stopped.
    expect(audio_capture_is_active()).to_equal(true)
    val frames = audio_capture_stop()
    expect(frames).to_be_greater_than(-1)
    expect(file_exists(tmp_path)).to_equal(true)
audio_shutdown(engine)
```

</details>

#### stop() without a prior start() is a safe no-op that returns 0

- stop() without a prior start() is a safe no-op that returns 0
   - Expected: frames equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("stop() without a prior start() is a safe no-op that returns 0")
val frames = audio_capture_stop()
expect(frames).to_equal(0)
```

</details>

#### a second start() while already active is rejected (single active-capture contract)

- a second start() while already active is rejected (single active-capture contract)
   - Expected: cap_b.active is false
   - Expected: cap_a.active is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-APP
step("a second start() while already active is rejected (single active-capture contract)")
val tmp_a = "/tmp/simple_audio_capture_a_{getpid()}.wav"
val tmp_b = "/tmp/simple_audio_capture_b_{getpid()}.wav"
val cap_a = audio_capture_start(tmp_a, 8000, 1)
if cap_a.active:
    val cap_b = audio_capture_start(tmp_b, 8000, 1)
    expect(cap_b.active).to_equal(false)
    audio_capture_stop()
else:
    # No device to prove the contract against on this host — the
    # fail-closed case is already covered above.
    expect(cap_a.active).to_equal(false)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/io/audio_capture_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering audio capture (recording).
- audio capture (recording)

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

- `REQ-SSPEC-APP`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `aac0789f9a4821cd5c3e13e35bea5a09b86daeb7802480d266a2546ed6a06c17`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `aac0789f9a4821cd5c3e13e35bea5a09b86daeb7802480d266a2546ed6a06c17`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `aac0789f9a4821cd5c3e13e35bea5a09b86daeb7802480d266a2546ed6a06c17`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **95/100**; effective score: **95/100**; blockers: **0**.

SSpec documentization score: 95/100
source: test/01_unit/app/io/audio_capture_spec.spl
mirror: doc/06_spec/01_unit/app/io/audio_capture_spec.md (current)
findings: 3 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=100 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/io/audio_capture_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/io/audio_capture_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/io/audio_capture_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
<!-- sspec-maintain:scorecard:end -->
