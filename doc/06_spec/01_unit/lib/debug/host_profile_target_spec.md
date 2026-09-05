# Host Profile Target Specification

> Tests covering HostProfileTarget tiering, HostProfileTarget measurement, HostProfileTarget refuses to fabricate, HostProfileTarget disabled-path cost.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Host Profile Target Specification

## Scenarios

### HostProfileTarget tiering

#### reports Native when profiling was armed at attach

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- reports Native when profiling was armed at attach
   - Expected: cap_level_name(t.profile_level()) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports Native when profiling was armed at attach")
val t = HostProfileTarget.armed_target()
expect(cap_level_name(t.profile_level())).to_equal("native")
```

</details>

#### reports Unavailable when profiling was not armed at attach

- reports Unavailable when profiling was not armed at attach
   - Expected: cap_level_name(t.profile_level()) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports Unavailable when profiling was not armed at attach")
val t = HostProfileTarget.disarmed_target()
expect(cap_level_name(t.profile_level())).to_equal("unavailable")
```

</details>

#### takes its arming from AttachOpts.profile, not from a later toggle

- takes its arming from AttachOpts.profile, not from a later toggle
   - Expected: cap_level_name(armed_t.profile_level()) equals `native`
   - Expected: cap_level_name(unarmed_t.profile_level()) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("takes its arming from AttachOpts.profile, not from a later toggle")
val armed_t = HostProfileTarget.new(AttachOpts(step_budget: 10, entry_pc: 0, log_cap: 8, profile: true))
val unarmed_t = HostProfileTarget.new(AttachOpts(step_budget: 10, entry_pc: 0, log_cap: 8, profile: false))
expect(cap_level_name(armed_t.profile_level())).to_equal("native")
expect(cap_level_name(unarmed_t.profile_level())).to_equal("unavailable")
```

</details>

#### defaults to armed under attach_opts_default

- defaults to armed under attach_opts_default
   - Expected: cap_level_name(t.profile_level()) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("defaults to armed under attach_opts_default")
val t = HostProfileTarget.new(attach_opts_default())
expect(cap_level_name(t.profile_level())).to_equal("native")
```

</details>

### HostProfileTarget measurement

#### measures a positive wall_ns across real work

- measures a positive wall_ns across real work
   - Expected: sum > 0 is true
   - Expected: r.wall_ns > 0 is true
   - Expected: cap_level_name(r.level) equals `native`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("measures a positive wall_ns across real work")
var t = HostProfileTarget.armed_target()
t.profile_begin()
val sum = burn(200000)
val r = t.profile_end()
# Guard against the loop being elided: 200000 rounds of (i % 7) is a
# large positive sum.
expect(sum > 0).to_equal(true)
expect(r.wall_ns > 0).to_equal(true)
expect(cap_level_name(r.level)).to_equal("native")
```

</details>

#### reports steps as absent and NEVER as a number

- reports steps as absent and NEVER as a number
   - Expected: r.steps equals `PROFILE_ABSENT`
   - Expected: profile_has_steps(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports steps as absent and NEVER as a number")
var t = HostProfileTarget.armed_target()
t.profile_begin()
burn(1000)
val r = t.profile_end()
expect(r.steps).to_equal(PROFILE_ABSENT)
expect(profile_has_steps(r)).to_equal(false)
```

</details>

#### reports device_ns as absent, not zero

- reports device_ns as absent, not zero
   - Expected: r.device_ns equals `PROFILE_ABSENT`
   - Expected: profile_has_device_time(r) is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reports device_ns as absent, not zero")
var t = HostProfileTarget.armed_target()
t.profile_begin()
burn(1000)
val r = t.profile_end()
expect(r.device_ns).to_equal(PROFILE_ABSENT)
expect(profile_has_device_time(r)).to_equal(false)
```

</details>

#### states in detail which fields were measured and which are absent

- states in detail which fields were measured and which are absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("states in detail which fields were measured and which are absent")
var t = HostProfileTarget.armed_target()
t.profile_begin()
burn(1000)
val r = t.profile_end()
expect(r.detail).to_contain("wall_ns=measured")
expect(r.detail).to_contain("device_ns=absent")
expect(r.detail).to_contain("steps=absent")
```

</details>

#### measures a longer window as at least as long as a shorter one

- measures a longer window as at least as long as a shorter one
   - Expected: long_r.wall_ns >= short_r.wall_ns is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("measures a longer window as at least as long as a shorter one")
var short_t = HostProfileTarget.armed_target()
short_t.profile_begin()
burn(20000)
val short_r = short_t.profile_end()
var long_t = HostProfileTarget.armed_target()
long_t.profile_begin()
burn(400000)
val long_r = long_t.profile_end()
# 20x the work. Asserting only >= keeps this robust on a loaded
# machine while still failing outright if wall_ns is a constant.
expect(long_r.wall_ns >= short_r.wall_ns).to_equal(true)
```

</details>

### HostProfileTarget refuses to fabricate

#### returns Unavailable with everything absent when not armed

- returns Unavailable with everything absent when not armed
   - Expected: cap_level_name(r.level) equals `unavailable`
   - Expected: r.wall_ns equals `PROFILE_ABSENT`
   - Expected: r.device_ns equals `PROFILE_ABSENT`
   - Expected: r.steps equals `PROFILE_ABSENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Unavailable with everything absent when not armed")
var t = HostProfileTarget.disarmed_target()
t.profile_begin()
burn(50000)
val r = t.profile_end()
expect(cap_level_name(r.level)).to_equal("unavailable")
expect(r.wall_ns).to_equal(PROFILE_ABSENT)
expect(r.device_ns).to_equal(PROFILE_ABSENT)
expect(r.steps).to_equal(PROFILE_ABSENT)
expect(r.detail).to_contain("not armed at attach")
```

</details>

#### returns Unavailable when profile_end has no matching profile_begin

- returns Unavailable when profile_end has no matching profile_begin
   - Expected: cap_level_name(r.level) equals `unavailable`
   - Expected: r.wall_ns equals `PROFILE_ABSENT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns Unavailable when profile_end has no matching profile_begin")
var t = HostProfileTarget.armed_target()
val r = t.profile_end()
expect(cap_level_name(r.level)).to_equal("unavailable")
expect(r.wall_ns).to_equal(PROFILE_ABSENT)
expect(r.detail).to_contain("no matching profile_begin")
```

</details>

#### honours last-begin-wins per the trait contract

- honours last-begin-wins per the trait contract
   - Expected: cap_level_name(r.level) equals `native`
   - Expected: r.wall_ns < 300000 is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("honours last-begin-wins per the trait contract")
var t = HostProfileTarget.armed_target()
t.profile_begin()
burn(300000)
t.profile_begin()          # re-arm: the first window is discarded
val r = t.profile_end()
expect(cap_level_name(r.level)).to_equal("native")
# The reported window starts at the SECOND begin, so it must be far
# shorter than the 300000-round burn that preceded it. Measured on
# this host that burn is >1ms; 300us is a wide margin that still
# fails if the first begin_ns were kept.
expect(r.wall_ns < 300000).to_equal(true)
```

</details>

#### closes the window so a second end without a begin is Unavailable

- closes the window so a second end without a begin is Unavailable
   - Expected: cap_level_name(first.level) equals `native`
   - Expected: cap_level_name(second.level) equals `unavailable`


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("closes the window so a second end without a begin is Unavailable")
var t = HostProfileTarget.armed_target()
t.profile_begin()
burn(1000)
val first = t.profile_end()
val second = t.profile_end()
expect(cap_level_name(first.level)).to_equal("native")
expect(cap_level_name(second.level)).to_equal("unavailable")
```

</details>

### HostProfileTarget disabled-path cost

#### stores no clock reading when not armed

- stores no clock reading when not armed
   - Expected: t.begin_ns equals `0`
   - Expected: t.running is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("stores no clock reading when not armed")
var t = HostProfileTarget.disarmed_target()
t.profile_begin()
expect(t.begin_ns).to_equal(0)
expect(t.running).to_equal(false)
```

</details>

#### does store a clock reading when armed (control for the above)

- does store a clock reading when armed (control for the above)
   - Expected: t.begin_ns > 0 is true
   - Expected: t.running is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("does store a clock reading when armed (control for the above)")
# Without this control the assertion above could pass because the
# clock is broken rather than because the guard works.
var t = HostProfileTarget.armed_target()
t.profile_begin()
expect(t.begin_ns > 0).to_equal(true)
expect(t.running).to_equal(true)
```

</details>

#### reads no clock at all when not armed, however long the window

- reads no clock at all when not armed, however long the window
   - Expected: r.wall_ns equals `PROFILE_ABSENT`
   - Expected: t.begin_ns equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("reads no clock at all when not armed, however long the window")
# Structural half of the zero-overhead claim: even across a large
# window the disarmed target produces no duration, proving no
# reading was taken rather than merely discarded.
var t = HostProfileTarget.disarmed_target()
t.profile_begin()
burn(200000)
val r = t.profile_end()
expect(r.wall_ns).to_equal(PROFILE_ABSENT)
expect(t.begin_ns).to_equal(0)
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/debug/host_profile_target_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering HostProfileTarget tiering, HostProfileTarget measurement, HostProfileTarget refuses to fabricate, HostProfileTarget disabled-path cost.
- HostProfileTarget tiering
- HostProfileTarget measurement
- HostProfileTarget refuses to fabricate
- HostProfileTarget disabled-path cost

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 16 |
| Active scenarios | 16 |
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

- Canonical SPipe generation for source `724274d82e9491774e789d7a437c1b7a6192328ee4742e5246f39edb79c9ad21`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `724274d82e9491774e789d7a437c1b7a6192328ee4742e5246f39edb79c9ad21`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `724274d82e9491774e789d7a437c1b7a6192328ee4742e5246f39edb79c9ad21`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/debug/host_profile_target_spec.spl
mirror: doc/06_spec/01_unit/lib/debug/host_profile_target_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=80
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/debug/host_profile_target_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/debug/host_profile_target_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/debug/host_profile_target_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-20): 2 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/debug/host_profile_target_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports Native when profiling was armed at attach' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/host_profile_target_spec.spl:50:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'reports Unavailable when profiling was not armed at attach' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/debug/host_profile_target_spec.spl:56:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'takes its arming from AttachOpts.profile, not from a later toggle' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
