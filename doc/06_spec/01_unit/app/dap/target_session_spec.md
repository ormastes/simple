# Target Session Specification

> Tests covering TargetDapSession routing, TargetDapSession DAP round-trips, TargetDapSession profile requests, TargetDapSession capability aliasing.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 29 | 29 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Target Session Specification

## Scenarios

### TargetDapSession routing

#### defaults to the host lane with an empty mode spec

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- defaults to the host lane with an empty mode spec


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("defaults to the host lane with an empty mode spec")
val s = target_dap_session_host(FIXTURE)
assert_equal(s.target_kind, "host")
assert_equal(s.mode_spec, "")
assert_equal(s.error, "")
assert_true(s.is_usable())
```

</details>

#### keeps the host lane when the launch config says gpu:false

- keeps the host lane when the launch config says gpu:false


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the host lane when the launch config says gpu:false")
val s = target_dap_session_launch(
    "{\"program\":\"{FIXTURE}\",\"gpu\":false}",
    default_gpu_config(), FakeGpuProbe.with_available(["cuda"]))
assert_equal(s.target_kind, "host")
assert_equal(s.mode_spec, "")
assert_true(s.is_usable())
```

</details>

#### routes gpu:true through the resolver to the configured backend

- routes gpu:true through the resolver to the configured backend


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("routes gpu:true through the resolver to the configured backend")
val s = target_dap_session_launch(
    "{\"program\":\"{FIXTURE}\",\"gpu\":true}",
    config_of("cuda", "interpreter", "auto"), FakeGpuProbe.none_available())
assert_equal(s.target_kind, "cuda")
assert_equal(s.mode_spec, "interpreter(remote(cuda(sm80)))")
```

</details>

#### auto-probes cuda -> vulkan -> metal and takes the first available

- auto-probes cuda -> vulkan -> metal and takes the first available


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("auto-probes cuda -> vulkan -> metal and takes the first available")
val s = target_dap_session_launch(
    "{\"program\":\"{FIXTURE}\",\"gpu\":true}",
    default_gpu_config(), FakeGpuProbe.with_available(["vulkan"]))
assert_equal(s.target_kind, "vulkan")
assert_true(has(s.mode_spec, "remote(vulkan("))
```

</details>

#### passes an explicit gpuModeSpec through verbatim

- passes an explicit gpuModeSpec through verbatim


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("passes an explicit gpuModeSpec through verbatim")
val s = target_dap_session_launch(
    "{\"program\":\"{FIXTURE}\",\"gpuModeSpec\":\"jit(remote(cuda(sm90)))\"}",
    default_gpu_config(), FakeGpuProbe.none_available())
assert_equal(s.mode_spec, "jit(remote(cuda(sm90)))")
assert_equal(s.target_kind, "cuda")
```

</details>

#### prefers an explicit gpuModeSpec over a bare gpu:true tag

- prefers an explicit gpuModeSpec over a bare gpu:true tag


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("prefers an explicit gpuModeSpec over a bare gpu:true tag")
val s = target_dap_session_launch(
    "{\"program\":\"{FIXTURE}\",\"gpu\":true,\"gpuModeSpec\":\"jit(remote(vulkan(spv15)))\"}",
    config_of("cuda", "interpreter", "auto"), FakeGpuProbe.with_available(["cuda"]))
assert_equal(s.mode_spec, "jit(remote(vulkan(spv15)))")
assert_equal(s.target_kind, "vulkan")
```

</details>

#### reports every backend's own reason when no GPU is available

- reports every backend's own reason when no GPU is available


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports every backend's own reason when no GPU is available")
val s = target_dap_session_launch(
    "{\"program\":\"{FIXTURE}\",\"gpu\":true}",
    default_gpu_config(), FakeGpuProbe.none_available())
assert_true(s.error != "")
assert_true(has(s.error, "cuda-absent-in-fake-probe"))
assert_true(has(s.error, "vulkan-absent-in-fake-probe"))
assert_true(has(s.error, "metal-absent-in-fake-probe"))
assert_true(not s.launched)
```

</details>

#### refuses to silently fall back to the host when a GPU lane resolves

- refuses to silently fall back to the host when a GPU lane resolves


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses to silently fall back to the host when a GPU lane resolves")
# Routing succeeded; there is no .spl -> SVM-G attach path, and the
# session says so instead of debugging the WRONG program on the host.
val s = target_dap_session_launch(
    "{\"program\":\"{FIXTURE}\",\"gpu\":true}",
    default_gpu_config(), FakeGpuProbe.with_available(["cuda"]))
assert_equal(s.target_kind, "cuda")
assert_true(not s.launched)
assert_true(has(s.error, "no DAP attach path"))
```

</details>

#### rejects a launch configuration with no program

- rejects a launch configuration with no program


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("rejects a launch configuration with no program")
val s = target_dap_session_launch(
    "{\"type\":\"simple\"}", default_gpu_config(), FakeGpuProbe.none_available())
assert_true(not s.launched)
assert_true(has(s.error, "no 'program'"))
```

</details>

### TargetDapSession DAP round-trips

#### answers initialize by naming both custom profile requests

- answers initialize by naming both custom profile requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers initialize by naming both custom profile requests")
var s = target_dap_session_host(FIXTURE)
val out = s.handle(req(1, "initialize"))
assert_true(has(out, "\"success\":true"))
assert_true(has(out, "\"request_seq\":1"))
assert_true(has(out, "simple/profileBegin"))
assert_true(has(out, "simple/profileEnd"))
```

</details>

#### reports the stop point with its pc_kind unit

- reports the stop point with its pc_kind unit


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports the stop point with its pc_kind unit")
var s = target_dap_session_host(FIXTURE)
val out = s.handle(req(2, "stackTrace"))
assert_true(has(out, "\"pc\":4"))
assert_true(has(out, "\"pcKind\":\"line\""))
assert_true(has(out, "\"target\":\"host\""))
```

</details>

#### verifies breakpoints the target accepted and rejects the rest

- verifies breakpoints the target accepted and rejects the rest


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("verifies breakpoints the target accepted and rejects the rest")
var s = target_dap_session_host(FIXTURE)
val out = s.handle(
    "{\"seq\":3,\"command\":\"setBreakpoints\",\"arguments\":{\"breakpoints\":[{\"line\":6},{\"line\":900}]}}")
assert_true(has(out, "{\"verified\":true,\"line\":6}"))
assert_true(has(out, "{\"verified\":false,\"line\":900}"))
```

</details>

#### replaces the breakpoint set on each setBreakpoints, DAP semantics

- replaces the breakpoint set on each setBreakpoints, DAP semantics


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("replaces the breakpoint set on each setBreakpoints, DAP semantics")
var s = target_dap_session_host(FIXTURE)
s.handle("{\"seq\":4,\"command\":\"setBreakpoints\",\"arguments\":{\"breakpoints\":[{\"line\":5}]}}")
s.handle("{\"seq\":5,\"command\":\"setBreakpoints\",\"arguments\":{\"breakpoints\":[{\"line\":7}]}}")
val bps = s.target.breakpoints()
assert_equal(bps.len(), 1)
assert_equal(bps[0], 7)
```

</details>

#### steps exactly one source line per next request

- steps exactly one source line per next request


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("steps exactly one source line per next request")
var s = target_dap_session_host(FIXTURE)
val out = s.handle(req(6, "next"))
assert_true(has(out, "\"pc\":5"))
assert_true(has(out, "\"stopReason\":\"step\""))
```

</details>

#### continues to the next breakpoint

- continues to the next breakpoint


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("continues to the next breakpoint")
var s = target_dap_session_host(FIXTURE)
s.handle("{\"seq\":7,\"command\":\"setBreakpoints\",\"arguments\":{\"breakpoints\":[{\"line\":7}]}}")
val out = s.handle(req(8, "continue"))
assert_true(has(out, "\"pc\":7"))
assert_true(has(out, "\"stopReason\":\"breakpoint\""))
```

</details>

#### answers threads with the single host thread

- answers threads with the single host thread


<details>
<summary>Executable SSpec</summary>

Runnable source: 4 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("answers threads with the single host thread")
var s = target_dap_session_host(FIXTURE)
assert_true(has(s.handle(req(9, "threads")), "\"name\":\"main\""))
```

</details>

#### returns a DAP error, not a silent success, for an unknown command

- returns a DAP error, not a silent success, for an unknown command


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a DAP error, not a silent success, for an unknown command")
var s = target_dap_session_host(FIXTURE)
val out = s.handle(req(10, "wibble"))
assert_true(has(out, "\"success\":false"))
assert_true(has(out, "unsupported request 'wibble'"))
```

</details>

#### returns a DAP error for a request with no command

- returns a DAP error for a request with no command


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a DAP error for a request with no command")
var s = target_dap_session_host(FIXTURE)
val out = s.handle("{\"seq\":11}")
assert_true(has(out, "\"success\":false"))
assert_true(has(out, "no 'command'"))
```

</details>

#### refuses debug requests on a session whose routing failed, stating why

- refuses debug requests on a session whose routing failed, stating why


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("refuses debug requests on a session whose routing failed, stating why")
var s = target_dap_session_launch(
    "{\"program\":\"{FIXTURE}\",\"gpu\":true}",
    default_gpu_config(), FakeGpuProbe.none_available())
val out = s.handle(req(12, "stackTrace"))
assert_true(has(out, "\"success\":false"))
assert_true(has(out, "cuda-absent-in-fake-probe"))
```

</details>

#### detaches cleanly and is safe to disconnect twice

- detaches cleanly and is safe to disconnect twice


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("detaches cleanly and is safe to disconnect twice")
var s = target_dap_session_host(FIXTURE)
assert_true(has(s.handle(req(13, "disconnect")), "\"detached\":\"\""))
assert_true(has(s.handle(req(14, "disconnect")), "\"detached\":\"\""))
```

</details>

### TargetDapSession profile requests

#### arms profiling at the Native tier on the host

- arms profiling at the Native tier on the host


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("arms profiling at the Native tier on the host")
var s = target_dap_session_host(FIXTURE)
val out = s.handle(req(20, "simple/profileBegin"))
assert_true(has(out, "\"armed\":true"))
assert_true(has(out, "\"level\":\"native\""))
```

</details>

#### returns a measured wall time and ABSENT device/steps, never zero

- returns a measured wall time and ABSENT device/steps, never zero


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("returns a measured wall time and ABSENT device/steps, never zero")
var s = target_dap_session_host(FIXTURE)
s.handle(req(21, "simple/profileBegin"))
s.handle(req(22, "next"))
val out = s.handle(req(23, "simple/profileEnd"))
assert_true(has(out, "\"level\":\"native\""))
assert_true(has(out, "\"deviceNs\":-1"))
assert_true(has(out, "\"steps\":-1"))
assert_true(not has(out, "\"wallNs\":-1"))
```

</details>

#### reports Unavailable for profileEnd with no matching begin

- reports Unavailable for profileEnd with no matching begin


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports Unavailable for profileEnd with no matching begin")
var s = target_dap_session_host(FIXTURE)
val out = s.handle(req(24, "simple/profileEnd"))
assert_true(has(out, "\"level\":\"unavailable\""))
assert_true(has(out, "\"wallNs\":-1"))
assert_true(has(out, "no matching profile_begin"))
```

</details>

#### reports Unavailable, not zero, on a session that never launched

- reports Unavailable, not zero, on a session that never launched


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("reports Unavailable, not zero, on a session that never launched")
var s = target_dap_session_launch(
    "{\"program\":\"{FIXTURE}\",\"gpu\":true}",
    default_gpu_config(), FakeGpuProbe.none_available())
val out = s.handle(req(25, "simple/profileEnd"))
assert_true(has(out, "\"level\":\"unavailable\""))
assert_true(has(out, "\"wallNs\":-1"))
assert_true(has(out, "\"deviceNs\":-1"))
```

</details>

#### re-arms on a second begin (last-begin-wins), no error

- re-arms on a second begin (last-begin-wins), no error


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("re-arms on a second begin (last-begin-wins), no error")
var s = target_dap_session_host(FIXTURE)
s.handle(req(26, "simple/profileBegin"))
s.handle(req(27, "simple/profileBegin"))
val out = s.handle(req(28, "simple/profileEnd"))
assert_true(has(out, "\"level\":\"native\""))
```

</details>

#### renders an absent report with -1 fields, not nulls

- renders an absent report with -1 fields, not nulls


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("renders an absent report with -1 fields, not nulls")
val json = profile_report_json(profile_report_unavailable("no target"))
assert_true(has(json, "\"wallNs\":-1"))
assert_true(has(json, "\"deviceNs\":-1"))
assert_true(has(json, "\"steps\":-1"))
assert_true(has(json, "\"detail\":\"no target\""))
```

</details>

### TargetDapSession capability aliasing

#### keeps a breakpoint set through the session visible on the target

- keeps a breakpoint set through the session visible on the target


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a breakpoint set through the session visible on the target")
# Under the non-tail-expression handle shape this passes `set_breakpoint`
# to a COPY and the target's list stays empty while step/resume work.
var s = target_dap_session_host(FIXTURE)
s.handle("{\"seq\":30,\"command\":\"setBreakpoints\",\"arguments\":{\"breakpoints\":[{\"line\":6}]}}")
val bps = s.target.breakpoints()
assert_equal(bps.len(), 1)
assert_equal(bps[0], 6)
```

</details>

#### keeps a profile window armed through the session

- keeps a profile window armed through the session


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps a profile window armed through the session")
# Under the broken shape `profile_begin` is discarded, so `profile_end`
# reports "no matching profile_begin" instead of a measurement.
var s = target_dap_session_host(FIXTURE)
s.handle(req(31, "simple/profileBegin"))
val out = s.handle(req(32, "simple/profileEnd"))
assert_true(not has(out, "no matching profile_begin"))
assert_true(has(out, "\"level\":\"native\""))
```

</details>

#### keeps the stepped position visible across separate requests

- keeps the stepped position visible across separate requests


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-UNIT
step("keeps the stepped position visible across separate requests")
var s = target_dap_session_host(FIXTURE)
s.handle(req(33, "next"))
s.handle(req(34, "next"))
assert_true(has(s.handle(req(35, "stackTrace")), "\"pc\":6"))
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/01_unit/app/dap/target_session_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering TargetDapSession routing, TargetDapSession DAP round-trips, TargetDapSession profile requests, TargetDapSession capability aliasing.
- TargetDapSession routing
- TargetDapSession DAP round-trips
- TargetDapSession profile requests
- TargetDapSession capability aliasing

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 29 |
| Active scenarios | 29 |
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

- Canonical SPipe generation for source `e3f01d49efec97fdb234a3091c7da8e5ca19923a7dbabf450f2859d6d6e48cba`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e3f01d49efec97fdb234a3091c7da8e5ca19923a7dbabf450f2859d6d6e48cba`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e3f01d49efec97fdb234a3091c7da8e5ca19923a7dbabf450f2859d6d6e48cba`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/app/dap/target_session_spec.spl
mirror: doc/06_spec/01_unit/app/dap/target_session_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/app/dap/target_session_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/app/dap/target_session_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/app/dap/target_session_spec.spl:95:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'defaults to the host lane with an empty mode spec' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/target_session_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'keeps the host lane when the launch config says gpu:false' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/app/dap/target_session_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'routes gpu:true through the resolver to the configured backend' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
