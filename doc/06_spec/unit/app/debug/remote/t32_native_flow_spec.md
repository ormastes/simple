# T32 Native Flow Specification

> Tests covering T32 Power Debug T32 Native config, T32 Power Debug T32 Native flash and reset, T32 Power Debug T32 Native trace and coverage, T32 Power Debug T32 Native debug ops.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 16 | 16 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# T32 Native Flow Specification

## Scenarios

### T32 Power Debug T32 Native config

#### has correct T32 config

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- has correct T32 config
   - Expected: s.t32_cfg equals `t32_startup.cmm`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has correct T32 config")
val s = T32NativeSession.for_t32_target()
expect(s.t32_cfg).to_equal("t32_startup.cmm")
```

</details>

#### has T32 port 20000

- has T32 port 20000
   - Expected: s.t32_port equals `20000`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("has T32 port 20000")
val s = T32NativeSession.for_t32_target()
expect(s.t32_port).to_equal(20000)
```

</details>

#### target name is T32 Power Debug

- target name is T32 Power Debug
   - Expected: s.target_name equals `T32 Power Debug`


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("target name is T32 Power Debug")
val s = T32NativeSession.for_t32_target()
expect(s.target_name).to_equal("T32 Power Debug")
```

</details>

### T32 Power Debug T32 Native flash and reset

#### connect then flash succeeds

- connect then flash succeeds
   - Expected: s.flashed is true
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("connect then flash succeeds")
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("target_app.elf")
expect(s.flashed).to_equal(true)
expect(s.state).to_equal("halted")
```

</details>

#### system reset transitions to halted

- system reset transitions to halted
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("system reset transitions to halted")
var s = T32NativeSession.for_t32_target()
s.connect()
s.system_reset()
expect(s.state).to_equal("halted")
```

</details>

#### flash without connect fails

- flash without connect fails
   - Expected: s.flashed is false


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("flash without connect fails")
var s = T32NativeSession.for_t32_target()
val result = s.flash_program("app.elf")
expect(s.flashed).to_equal(false)
```

</details>

### T32 Power Debug T32 Native trace and coverage

#### trace capture returns trace data

- trace capture returns trace data


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace capture returns trace data")
var s = T32NativeSession.for_t32_target()
s.connect()
s.trace_capture(500)
expect(s.trace_data).to_contain("Trace.Arm")
expect(s.trace_data).to_contain("500ms")
```

</details>

#### coverage collect returns coverage data

- coverage collect returns coverage data


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("coverage collect returns coverage data")
var s = T32NativeSession.for_t32_target()
s.connect()
s.coverage_collect("main")
expect(s.coverage_data).to_contain("COVerage.ListFunc")
expect(s.coverage_data).to_contain("main")
```

</details>

#### trace capture when disconnected fails

- trace capture when disconnected fails
   - Expected: s.trace_data equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("trace capture when disconnected fails")
var s = T32NativeSession.for_t32_target()
val result = s.trace_capture(1000)
expect(s.trace_data).to_equal("")
```

</details>

### T32 Power Debug T32 Native debug ops

#### halt from running

- halt from running
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("halt from running")
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
s.resume()
s.halt()
expect(s.state).to_equal("halted")
```

</details>

#### resume from halted

- resume from halted
   - Expected: s.state equals `running`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("resume from halted")
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
s.resume()
expect(s.state).to_equal("running")
```

</details>

#### single step while halted

- single step while halted
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("single step while halted")
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
s.single_step()
expect(s.state).to_equal("halted")
```

</details>

#### read memory while halted

- read memory while halted
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read memory while halted")
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
val mem = s.read_memory(0x08000000, 16)
expect(s.state).to_equal("halted")
```

</details>

#### read register while halted

- read register while halted
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("read register while halted")
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("app.elf")
val reg = s.read_register("pc")
expect(s.state).to_equal("halted")
```

</details>

#### set breakpoint

- set breakpoint
   - Expected: s.state equals `connected`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("set breakpoint")
var s = T32NativeSession.for_t32_target()
s.connect()
s.set_breakpoint("main\\10")
expect(s.state).to_equal("connected")
```

</details>

#### full debug cycle: flash -> resume -> halt -> step

- full debug cycle: flash -> resume -> halt -> step
   - Expected: s.state equals `halted`
   - Expected: s.state equals `running`
   - Expected: s.state equals `halted`
   - Expected: s.state equals `halted`


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("full debug cycle: flash -> resume -> halt -> step")
var s = T32NativeSession.for_t32_target()
s.connect()
s.flash_program("target_app.elf")
expect(s.state).to_equal("halted")
s.resume()
expect(s.state).to_equal("running")
s.halt()
expect(s.state).to_equal("halted")
s.single_step()
expect(s.state).to_equal("halted")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/unit/app/debug/remote/t32_native_flow_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering T32 Power Debug T32 Native config, T32 Power Debug T32 Native flash and reset, T32 Power Debug T32 Native trace and coverage, T32 Power Debug T32 Native debug ops.
- T32 Power Debug T32 Native config
- T32 Power Debug T32 Native flash and reset
- T32 Power Debug T32 Native trace and coverage
- T32 Power Debug T32 Native debug ops

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

- `REQ-SSPEC-UNIT`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e20ab5e56da7091fec14a38040cdb0553dfc1ee7a894c92b2739146f0f5f5631`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e20ab5e56da7091fec14a38040cdb0553dfc1ee7a894c92b2739146f0f5f5631`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e20ab5e56da7091fec14a38040cdb0553dfc1ee7a894c92b2739146f0f5f5631`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/unit/app/debug/remote/t32_native_flow_spec.spl
mirror: doc/06_spec/unit/app/debug/remote/t32_native_flow_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/unit/app/debug/remote/t32_native_flow_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/unit/app/debug/remote/t32_native_flow_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/unit/app/debug/remote/t32_native_flow_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/unit/app/debug/remote/t32_native_flow_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has correct T32 config' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/t32_native_flow_spec.spl:110:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'has T32 port 20000' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/unit/app/debug/remote/t32_native_flow_spec.spl:116:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'target name is T32 Power Debug' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
