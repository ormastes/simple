# metal_debug_session_spec

> Purpose: Verify MetalDebugSession -- host-side contract (no Metal device required).

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 8 | 8 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# metal_debug_session_spec

Purpose: Verify MetalDebugSession -- host-side contract (no Metal device required).

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Purpose and audience
Purpose: Verify MetalDebugSession -- host-side contract (no Metal device required).
Audience: compiler and tooling engineers who maintain this spec.

## Scenarios

### MetalDebugSession -- host-side contract (no Metal device required)

#### should report its capability tier before any attach

- should report its capability tier before any attach
- Verify: should report its capability tier before any attach
   - Expected: s.kind() equals `metal`
   - Expected: cap_level_name(s.debug_level()) equals `emulated`
   - Expected: cap_level_name(s.profile_level()) equals `emulated`


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should report its capability tier before any attach")
step("Verify: should report its capability tier before any attach")
# @req: REQ-LIB-METAL-DEBUG-SESSION-001
# Runs on EVERY host, including this one. Nothing here touches a
# device, so this `it` is never a skip.
var s = MetalDebugSession.create()
expect(s.kind()).to_equal("metal")
# Emulated, NOT Native: breakpoints are SVM-G-level, maintained by
# our own MSL kernel. Claiming Native would assert a Metal debug
# facility this lane does not use.
expect(cap_level_name(s.debug_level())).to_equal("emulated")
expect(cap_level_name(s.profile_level())).to_equal("emulated")
```

</details>

#### should fail closed on launch before attach, naming the exact reason

- should fail closed on launch before attach, naming the exact reason
- Verify: should fail closed on launch before attach, naming the exact reason
   - Expected: o.ok is false
   - Expected: o.error equals `METAL_DEBUG_NOT_ATTACHED`
   - Expected: o.debug_break is false
   - Expected: o.trapped is false
   - Expected: o.timed_out is false
   - Expected: o.sentinel equals `0`
   - Expected: o.records.len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should fail closed on launch before attach, naming the exact reason")
step("Verify: should fail closed on launch before attach, naming the exact reason")
var s = MetalDebugSession.create()
val o = s.launch(false, false, false, [])
expect(o.ok).to_equal(false)
# The EXACT error, not merely "some non-empty string": a substring or
# non-empty check would also be satisfied by an unrelated fallback
# message from deeper in the stack.
expect(o.error).to_equal(METAL_DEBUG_NOT_ATTACHED)
# And the outcome must not look like a successful zero-step run.
expect(o.debug_break).to_equal(false)
expect(o.trapped).to_equal(false)
expect(o.timed_out).to_equal(false)
expect(o.sentinel).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(o.records.len()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should keep step and resume harmless before attach

- should keep step and resume harmless before attach
- Verify: should keep step and resume harmless before attach
   - Expected: st.pc equals `0`
   - Expected: st.pc_kind equals `PC_KIND_SVMG`
   - Expected: st.stop_reason equals `STOP_STEP`
   - Expected: st.stack.len() equals `0`
   - Expected: rs.stop_reason equals `STOP_HALT`
   - Expected: s.state().stop_reason equals `STOP_HALT`


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should keep step and resume harmless before attach")
step("Verify: should keep step and resume harmless before attach")
var s = MetalDebugSession.create()
val st = s.step()
expect(st.pc).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(st.pc_kind).to_equal(PC_KIND_SVMG)
expect(st.stop_reason).to_equal(STOP_STEP)
expect(st.stack.len()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
val rs = s.resume()
# No break, no trap, no timeout on an unattached session, so the
# stop reason degrades to HALT rather than inventing a breakpoint.
expect(rs.stop_reason).to_equal(STOP_HALT)
# `state()` reflects the same empty last-outcome.
expect(s.state().stop_reason).to_equal(STOP_HALT)
```

</details>

#### should record, dedupe and clear breakpoints in the DBG-1 table

- should record, dedupe and clear breakpoints in the DBG-1 table
- Verify: should record, dedupe and clear breakpoints in the DBG-1 table
   - Expected: s.breakpoints().len() equals `0`
   - Expected: s.set_breakpoint(4) is true
   - Expected: s.set_breakpoint(9) is true
   - Expected: s.set_breakpoint(4) is true
   - Expected: s.breakpoints().len() equals `2`
   - Expected: s.breakpoints()[0] equals `4`
   - Expected: s.breakpoints()[1] equals `9`
   - Expected: dbg_read_break_count(s.arena) equals `2`
   - Expected: dbg_read_breakpoint(s.arena, 0) equals `4`
   - Expected: dbg_read_breakpoint(s.arena, 1) equals `9`
   - Expected: s.clear_breakpoint(99) is false
   - Expected: s.breakpoints().len() equals `2`
   - Expected: dbg_read_break_count(s.arena) equals `2`
   - Expected: s.clear_breakpoint(4) is true
   - Expected: s.breakpoints().len() equals `1`
   - Expected: s.breakpoints()[0] equals `9`
   - Expected: dbg_read_break_count(s.arena) equals `1`
   - Expected: dbg_read_breakpoint(s.arena, 0) equals `9`


<details>
<summary>Executable SSpec</summary>

Runnable source: 30 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should record, dedupe and clear breakpoints in the DBG-1 table")
step("Verify: should record, dedupe and clear breakpoints in the DBG-1 table")
var s = _session_with_arena()
expect(s.breakpoints().len()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(s.set_breakpoint(4)).to_equal(true)
expect(s.set_breakpoint(9)).to_equal(true)
# Duplicate: reported as already-set, and must NOT grow the table.
expect(s.set_breakpoint(4)).to_equal(true)
expect(s.breakpoints().len()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
expect(s.breakpoints()[0]).to_equal(4)  # oracle: authoritative expected value documented by this spec's contract
expect(s.breakpoints()[1]).to_equal(9)  # oracle: authoritative expected value documented by this spec's contract
# The arena's DBG-1 breakpoint table must agree with the list -- a
# list-only check would pass even if the arena write were dropped,
# which is exactly the aliasing failure mode this file guards.
expect(dbg_read_break_count(s.arena)).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
expect(dbg_read_breakpoint(s.arena, 0)).to_equal(4)  # oracle: authoritative expected value documented by this spec's contract
expect(dbg_read_breakpoint(s.arena, 1)).to_equal(9)  # oracle: authoritative expected value documented by this spec's contract

# Clearing a breakpoint that was never set reports false and changes
# nothing.
expect(s.clear_breakpoint(99)).to_equal(false)
expect(s.breakpoints().len()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
expect(dbg_read_break_count(s.arena)).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract

expect(s.clear_breakpoint(4)).to_equal(true)
expect(s.breakpoints().len()).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
expect(s.breakpoints()[0]).to_equal(9)  # oracle: authoritative expected value documented by this spec's contract
expect(dbg_read_break_count(s.arena)).to_equal(1)  # oracle: authoritative expected value documented by this spec's contract
expect(dbg_read_breakpoint(s.arena, 0)).to_equal(9)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should bound read_mem instead of reading past the arena

- should bound read_mem instead of reading past the arena
- Verify: should bound read_mem instead of reading past the arena
   - Expected: s.read_mem(-1, 4).len() equals `0`
   - Expected: s.read_mem(0, 0).len() equals `0`
   - Expected: s.read_mem(0, -4).len() equals `0`
   - Expected: s.read_mem(0, 4).len() equals `4`
   - Expected: s.read_mem(n - 2, 16).len() equals `2`
   - Expected: s.read_mem(n, 8).len() equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should bound read_mem instead of reading past the arena")
step("Verify: should bound read_mem instead of reading past the arena")
var s = _session_with_arena()
val n = s.arena.len()
expect(n).to_be_greater_than(0)
# Negative offset and non-positive length yield nothing rather than
# panicking or wrapping.
expect(s.read_mem(-1, 4).len()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(s.read_mem(0, 0).len()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(s.read_mem(0, -4).len()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
# An in-range read returns exactly what was asked for...
expect(s.read_mem(0, 4).len()).to_equal(4)  # oracle: authoritative expected value documented by this spec's contract
# ...and a read that straddles the end is TRUNCATED, not extended.
expect(s.read_mem(n - 2, 16).len()).to_equal(2)  # oracle: authoritative expected value documented by this spec's contract
expect(s.read_mem(n, 8).len()).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
```

</details>

#### should report absent profile quantities as -1 and never as 0

- should report absent profile quantities as -1 and never as 0
- Verify: should report absent profile quantities as -1 and never as 0
   - Expected: cap_level_name(r.level) equals `emulated`
   - Expected: r.wall_ns == 0 is false
   - Expected: r.device_ns == 0 is false
   - Expected: r.wall_ns equals `PROFILE_ABSENT`
   - Expected: r.device_ns equals `PROFILE_ABSENT`
   - Expected: profile_has_device_time(r) is false
   - Expected: profile_has_steps(r) is true
   - Expected: r.steps equals `0`
   - Expected: r.detail equals `METAL_PROFILE_DETAIL`


<details>
<summary>Executable SSpec</summary>

Runnable source: 22 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should report absent profile quantities as -1 and never as 0")
step("Verify: should report absent profile quantities as -1 and never as 0")
var s = _session_with_arena()
s.profile_begin()
val r = s.profile_end()
expect(cap_level_name(r.level)).to_equal("emulated")
# THE contract point of this stream. 0 is a LEGITIMATE measurement,
# so a never-measured quantity reported as 0 reads as
# "instantaneous" instead of "not measured". Both the `== 0` and the
# `== PROFILE_ABSENT` forms are asserted so a regression to 0 cannot
# hide behind a loose comparison.
expect(r.wall_ns == 0).to_equal(false)
expect(r.device_ns == 0).to_equal(false)
expect(r.wall_ns).to_equal(PROFILE_ABSENT)
expect(r.device_ns).to_equal(PROFILE_ABSENT)
expect(profile_has_device_time(r)).to_equal(false)
# Steps ARE measured (exactly, from DBG_STEP_COUNT) -- with no launch
# between begin and end the honest answer is 0, not absent.
expect(profile_has_steps(r)).to_equal(true)
expect(r.steps).to_equal(0)  # oracle: authoritative expected value documented by this spec's contract
expect(r.detail).to_equal(METAL_PROFILE_DETAIL)
```

</details>

#### should skip cleanly on a host with no Metal, or name the device branch

- should skip cleanly on a host with no Metal, or name the device branch
- Verify: should skip cleanly on a host with no Metal, or name the device branch
   - Expected: probe_result equals `_EXPECTED_HOST_SKIP`
   - Expected: probe_result equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 18 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should skip cleanly on a host with no Metal, or name the device branch")
step("Verify: should skip cleanly on a host with no Metal, or name the device branch")
# BRANCHING TEST. On Linux this always takes the SKIPPED branch, and
# that skip is CORRECT -- not a failure to repair.
var s = MetalDebugSession.create()
val probe_result = s.probe()
if probe_result.starts_with("skip:"):
    print "[metal_debug_session] SKIPPED: {probe_result} -- the DEVICE-RAN branch did NOT run"
    if _require_gpu():
        # SIMPLE_REQUIRE_GPU=1 makes the skip a FAILURE, and the
        # failure message itself states both branches so the report
        # is readable without this file.
        assert_equal("SKIPPED: " + probe_result, "DEVICE-RAN: metal")
    expect(probe_result).to_equal(_EXPECTED_HOST_SKIP)
else:
    print "[metal_debug_session] DEVICE-RAN: probe() returned no skip reason; a live Metal device is present"
    expect(probe_result).to_equal("")
```

</details>

#### should pass a no-device attach failure through verbatim, never as success

- should pass a no-device attach failure through verbatim, never as success
- Verify: should pass a no-device attach failure through verbatim, never as success
   - Expected: err equals `_EXPECTED_HOST_SKIP`
   - Expected: s.attached is false
   - Expected: o.ok is false
   - Expected: o.error equals `METAL_DEBUG_NOT_ATTACHED`
   - Expected: err equals ``
   - Expected: s.attached is true
   - Expected: s.shutdown() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 35 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("should pass a no-device attach failure through verbatim, never as success")
step("Verify: should pass a no-device attach failure through verbatim, never as success")
# The honesty rule for `attach_kernel`: a missing device must surface
# as the underlying "skip:" string, NOT be rewritten into a generic
# error and NOT be swallowed into "".
val kernel_msl = file_read_text(_KERNEL_MSL_PATH)
# The MSL source must exist and be non-trivial on EVERY host -- this
# part is not device-gated. (It has still never been compiled by any
# Metal compiler; see the tracking doc.)
expect(kernel_msl.len()).to_be_greater_than(1000)

var s = MetalDebugSession.create()
val opts = attach_opts_default()
val err = s.attach_kernel(kernel_msl, _TINY_SRC, opts)
if err.starts_with("skip:"):
    print "[metal_debug_session] SKIPPED: attach returned {err} -- the DEVICE-RAN branch did NOT run"
    if _require_gpu():
        assert_equal("SKIPPED: " + err, "DEVICE-RAN: metal attach")
    expect(err).to_equal(_EXPECTED_HOST_SKIP)
    # Fail-closed: a failed attach must leave the session UNATTACHED,
    # so the next launch still refuses rather than dispatching into a
    # half-built session.
    expect(s.attached).to_equal(false)
    val o = s.launch(false, false, false, [])
    expect(o.ok).to_equal(false)
    expect(o.error).to_equal(METAL_DEBUG_NOT_ATTACHED)
else:
    print "[metal_debug_session] DEVICE-RAN: attach_kernel succeeded on a live Metal device"
    expect(err).to_equal("")
    expect(s.attached).to_equal(true)
    # Positive proof of a real attach: the arena was built at full
    # size, which the skip branch (arena stays empty) cannot reach.
    expect(s.arena.len()).to_be_greater_than(0)
    expect(s.shutdown()).to_equal("")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 8 |
| Active scenarios | 8 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-UNIT`
- `REQ-LIB-METAL-DEBUG-SESSION-001`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a00aece994ed5c2de45569cbc836dbee2aa6d70c1784c1d63ceb1f5329f66797`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a00aece994ed5c2de45569cbc836dbee2aa6d70c1784c1d63ceb1f5329f66797`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a00aece994ed5c2de45569cbc836dbee2aa6d70c1784c1d63ceb1f5329f66797`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu_lane/metal_debug_session_spec.md (current)
findings: 11 blockers: 0
  narrative=100 structure=70 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu_lane/metal_debug_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu_lane/metal_debug_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report its capability tier before any attach' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl:108:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report its capability tier before any attach' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl:123:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should fail closed on launch before attach, naming the exact reason' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should fail closed on launch before attach, naming the exact reason' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl:141:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep step and resume harmless before attach' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl:141:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should keep step and resume harmless before attach' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl:158:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should record, dedupe and clear breakpoints in the DBG-1 table' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl:190:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should bound read_mem instead of reading past the arena' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/01_unit/lib/gpu_lane/metal_debug_session_spec.spl:208:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report absent profile quantities as -1 and never as 0' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
