# Cuda Native Profile Specification

> Tests covering CudaNativeProfileTarget plausibility rule, CudaNativeProfileTarget arming, CudaNativeProfileTarget honest absence, CudaNativeProfileTarget live device timing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 14 | 14 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Cuda Native Profile Specification

## Scenarios

### CudaNativeProfileTarget plausibility rule

#### accepts a device window shorter than the enclosing host window

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- accepts a device window shorter than the enclosing host window
   - Expected: cuda_native_plausible(1000, 5000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a device window shorter than the enclosing host window")
expect(cuda_native_plausible(1000, 5000)).to_equal(true)
```

</details>

#### accepts a device window equal to the host window

- accepts a device window equal to the host window
   - Expected: cuda_native_plausible(5000, 5000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts a device window equal to the host window")
expect(cuda_native_plausible(5000, 5000)).to_equal(true)
```

</details>

#### accepts slack up to the tolerance, for unrelated clock oscillators

- accepts slack up to the tolerance, for unrelated clock oscillators
   - Expected: cuda_native_plausible(5000 + CUDA_NATIVE_TOLERANCE_NS, 5000) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("accepts slack up to the tolerance, for unrelated clock oscillators")
expect(cuda_native_plausible(5000 + CUDA_NATIVE_TOLERANCE_NS, 5000)).to_equal(true)
```

</details>

#### REJECTS a device window that outlasts the host window beyond tolerance

- REJECTS a device window that outlasts the host window beyond tolerance
   - Expected: cuda_native_plausible(5000 + CUDA_NATIVE_TOLERANCE_NS + 1, 5000) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 3 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS a device window that outlasts the host window beyond tolerance")
expect(cuda_native_plausible(5000 + CUDA_NATIVE_TOLERANCE_NS + 1, 5000)).to_equal(false)
```

</details>

#### REJECTS the millisecond/nanosecond mis-scaling of cuEventElapsedTime

- REJECTS the millisecond/nanosecond mis-scaling of cuEventElapsedTime
   - Expected: cuda_native_plausible(device_ns_correct, wall_ns) is true
   - Expected: cuda_native_plausible(device_ns_misscaled, wall_ns) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("REJECTS the millisecond/nanosecond mis-scaling of cuEventElapsedTime")
# cuEventElapsedTime returns MILLISECONDS. Forgetting the ms->ns
# conversion inflates device_ns by 1e6. A 2ms device window inside a
# 3ms host window is plausible; the same number left unscaled is not.
val wall_ns = 3000000
val device_ns_correct = 2000000
val device_ns_misscaled = 2000000 * 1000000
expect(cuda_native_plausible(device_ns_correct, wall_ns)).to_equal(true)
expect(cuda_native_plausible(device_ns_misscaled, wall_ns)).to_equal(false)
```

</details>

### CudaNativeProfileTarget arming

#### reports Unavailable when profiling was not armed at attach

- reports Unavailable when profiling was not armed at attach
   - Expected: cap_level_name(t.profile_level()) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports Unavailable when profiling was not armed at attach")
val t = CudaNativeProfileTarget.disarmed_target()
expect(cap_level_name(t.profile_level())).to_equal("unavailable")
```

</details>

#### takes its arming from AttachOpts.profile, not from a later toggle

- takes its arming from AttachOpts.profile, not from a later toggle
   - Expected: cap_level_name(unarmed.profile_level()) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("takes its arming from AttachOpts.profile, not from a later toggle")
val unarmed = CudaNativeProfileTarget.new(AttachOpts(step_budget: 10, entry_pc: 0, log_cap: 8, profile: false))
expect(cap_level_name(unarmed.profile_level())).to_equal("unavailable")
```

</details>

### CudaNativeProfileTarget honest absence

#### an unarmed target reports every quantity absent, never zero

- an unarmed target reports every quantity absent, never zero
   - Expected: cap_level_name(r.level) equals `unavailable`
   - Expected: r.device_ns equals `PROFILE_ABSENT`
   - Expected: r.wall_ns equals `PROFILE_ABSENT`
   - Expected: r.steps equals `PROFILE_ABSENT`
   - Expected: profile_has_device_time(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unarmed target reports every quantity absent, never zero")
var t = CudaNativeProfileTarget.disarmed_target()
t.profile_begin()
val r = t.profile_end()
expect(cap_level_name(r.level)).to_equal("unavailable")
expect(r.device_ns).to_equal(PROFILE_ABSENT)
expect(r.wall_ns).to_equal(PROFILE_ABSENT)
expect(r.steps).to_equal(PROFILE_ABSENT)
expect(profile_has_device_time(r)).to_equal(false)
```

</details>

#### an unarmed target's device_ns is -1 and specifically NOT 0

- an unarmed target's device_ns is -1 and specifically NOT 0
   - Expected: r.device_ns == 0 is false
   - Expected: r.device_ns equals `PROFILE_ABSENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("an unarmed target's device_ns is -1 and specifically NOT 0")
var t = CudaNativeProfileTarget.disarmed_target()
t.profile_begin()
val r = t.profile_end()
expect(r.device_ns == 0).to_equal(false)
expect(r.device_ns).to_equal(PROFILE_ABSENT)
```

</details>

#### profile_end without a matching profile_begin never fabricates a number

- profile_end without a matching profile_begin never fabricates a number
   - Expected: cap_level_name(r.level) equals `unavailable`
   - Expected: r.device_ns equals `PROFILE_ABSENT`
   - Expected: profile_has_device_time(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("profile_end without a matching profile_begin never fabricates a number")
var t = CudaNativeProfileTarget.armed_target()
val r = t.profile_end()
expect(cap_level_name(r.level)).to_equal("unavailable")
expect(r.device_ns).to_equal(PROFILE_ABSENT)
expect(profile_has_device_time(r)).to_equal(false)
```

</details>

#### never reports steps: cuEvent times a launch, it does not count instructions

- never reports steps: cuEvent times a launch, it does not count instructions
   - Expected: profile_has_steps(r) is false
   - Expected: r.steps equals `PROFILE_ABSENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("never reports steps: cuEvent times a launch, it does not count instructions")
var t = CudaNativeProfileTarget.armed_target()
t.profile_begin()
val r = t.profile_end()
expect(profile_has_steps(r)).to_equal(false)
expect(r.steps).to_equal(PROFILE_ABSENT)
```

</details>

### CudaNativeProfileTarget live device timing

#### claims Native only where real cuEvent timing is obtainable

- claims Native only where real cuEvent timing is obtainable
   - Expected: cap_level_name(t.profile_level()) equals `native`
   - Expected: cap_level_name(t.profile_level()) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("claims Native only where real cuEvent timing is obtainable")
val t = CudaNativeProfileTarget.armed_target()
val available = cuda_native_events_available()
if available:
    expect(cap_level_name(t.profile_level())).to_equal("native")
else:
    # No GPU / no cuEvent: Unavailable is the CORRECT outcome, and is
    # asserted so that a device-less host still checks something.
    expect(cap_level_name(t.profile_level())).to_equal("unavailable")
```

</details>

#### measures a real device window enclosed by the host window

- measures a real device window enclosed by the host window
   - Expected: cuda_native_events_available() is false
   - Expected: cap_level_name(r.level) equals `native`
   - Expected: profile_has_device_time(r) is true
   - Expected: r.device_ns >= 0 is true
   - Expected: r.device_ns == PROFILE_ABSENT is false
   - Expected: r.wall_ns >= 0 is true
   - Expected: r.device_ns <= r.wall_ns + CUDA_NATIVE_TOLERANCE_NS is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 21 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("measures a real device window enclosed by the host window")
if not cuda_native_events_available():
    # Host-aware skip, with the reason asserted rather than silent.
    expect(cuda_native_events_available()).to_equal(false)
else:
    var t = CudaNativeProfileTarget.armed_target()
    t.profile_begin()
    val r = t.profile_end()
    expect(cap_level_name(r.level)).to_equal("native")
    # A real measurement: present, non-negative, and NOT the absent
    # sentinel.
    expect(profile_has_device_time(r)).to_equal(true)
    expect(r.device_ns >= 0).to_equal(true)
    expect(r.device_ns == PROFILE_ABSENT).to_equal(false)
    # wall_ns is always measured, so it is the cross-check.
    expect(r.wall_ns >= 0).to_equal(true)
    # THE PLAUSIBILITY ASSERTION: device time must not exceed the
    # enclosing host time beyond measurement noise.
    expect(r.device_ns <= r.wall_ns + CUDA_NATIVE_TOLERANCE_NS).to_equal(true)
    t.release()
```

</details>

#### reports device_ns and wall_ns from independent clocks, both present

- reports device_ns and wall_ns from independent clocks, both present
   - Expected: cuda_native_events_available() is false
   - Expected: r.device_ns >= 0 is true
   - Expected: r.wall_ns >= 0 is true
   - Expected: cuda_native_plausible(r.device_ns, r.wall_ns) is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports device_ns and wall_ns from independent clocks, both present")
if not cuda_native_events_available():
    expect(cuda_native_events_available()).to_equal(false)
else:
    var t = CudaNativeProfileTarget.armed_target()
    t.profile_begin()
    val r = t.profile_end()
    expect(r.device_ns >= 0).to_equal(true)
    expect(r.wall_ns >= 0).to_equal(true)
    expect(cuda_native_plausible(r.device_ns, r.wall_ns)).to_equal(true)
    t.release()
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/cuda_native_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering CudaNativeProfileTarget plausibility rule, CudaNativeProfileTarget arming, CudaNativeProfileTarget honest absence, CudaNativeProfileTarget live device timing.
- CudaNativeProfileTarget plausibility rule
- CudaNativeProfileTarget arming
- CudaNativeProfileTarget honest absence
- CudaNativeProfileTarget live device timing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 14 |
| Active scenarios | 14 |
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

- Canonical SPipe generation for source `6ce6872ee7cb7790f8000110f65cd3d9758c2a40201baa3482a09171d5291aa3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `6ce6872ee7cb7790f8000110f65cd3d9758c2a40201baa3482a09171d5291aa3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `6ce6872ee7cb7790f8000110f65cd3d9758c2a40201baa3482a09171d5291aa3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/lib/debug/cuda_native_profile_spec.spl
mirror: doc/06_spec/01_unit/lib/debug/cuda_native_profile_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/debug/cuda_native_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/debug/cuda_native_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/debug/cuda_native_profile_spec.spl:39:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a device window shorter than the enclosing host window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/cuda_native_profile_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts a device window equal to the host window' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/cuda_native_profile_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'accepts slack up to the tolerance, for unrelated clock oscillators' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
