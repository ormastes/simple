# Mem Profile Specification

> Tests covering run_under_compute_sanitizer, device_trace_to_memory_viz.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# Mem Profile Specification

## Scenarios

### run_under_compute_sanitizer

#### returns a clear 127 result when compute-sanitizer is not on PATH

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- returns a clear 127 result when compute-sanitizer is not on PATH
   - Expected: code equals `127`
   - Expected: err equals `compute-sanitizer not found`
   - Expected: out equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("returns a clear 127 result when compute-sanitizer is not on PATH")
# Force a PATH that cannot contain compute-sanitizer, regardless of
# whether this box has CUDA installed, so the test is deterministic
# on both GPU and GPU-less machines.
val saved_path = rt_env_get("PATH")
rt_env_set("PATH", "/nonexistent_dir_for_gpu_sanitize_test")

val (out, err, code) = run_under_compute_sanitizer("memcheck", ["echo", "hi"])

rt_env_set("PATH", saved_path)

expect(code).to_equal(127)
expect(err).to_equal("compute-sanitizer not found")
expect(out).to_equal("")
```

</details>

### device_trace_to_memory_viz

#### emits a well-formed, versioned JSON snapshot with the right event count

- emits a well-formed, versioned JSON snapshot with the right event count


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("emits a well-formed, versioned JSON snapshot with the right event count")
val events = [
    DeviceAllocEvent(ts: 1000, owner: "mod_a", ptr: 4096, bytes: 256, kind: "alloc"),
    DeviceAllocEvent(ts: 1010, owner: "mod_b", ptr: 8192, bytes: 512, kind: "alloc"),
    DeviceAllocEvent(ts: 1020, owner: "mod_a", ptr: 4096, bytes: 256, kind: "free")
]

val json = device_trace_to_memory_viz(events)

expect(json).to_contain("\"schema\":\"simple-gpu-trace\"")
expect(json).to_contain("\"version\":1")
expect(json).to_contain("\"event_count\":3")
```

</details>

#### names each event's owner and records ptr/bytes/kind

- names each event's owner and records ptr/bytes/kind


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("names each event's owner and records ptr/bytes/kind")
val events = [
    DeviceAllocEvent(ts: 5, owner: "cuda_owner_1", ptr: 111, bytes: 64, kind: "alloc"),
    DeviceAllocEvent(ts: 6, owner: "cuda_owner_2", ptr: 222, bytes: 128, kind: "free")
]

val json = device_trace_to_memory_viz(events)

expect(json).to_contain("\"owner\":\"cuda_owner_1\"")
expect(json).to_contain("\"owner\":\"cuda_owner_2\"")
expect(json).to_contain("\"ptr\":111")
expect(json).to_contain("\"bytes\":128")
expect(json).to_contain("\"kind\":\"alloc\"")
expect(json).to_contain("\"kind\":\"free\"")
```

</details>

#### produces balanced braces/brackets (structurally parseable JSON)

- produces balanced braces/brackets (structurally parseable JSON)
   - Expected: open_braces equals `close_braces`
   - Expected: open_brackets equals `close_brackets`


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("produces balanced braces/brackets (structurally parseable JSON)")
val events = [
    DeviceAllocEvent(ts: 1, owner: "a", ptr: 1, bytes: 1, kind: "alloc")
]
val json = device_trace_to_memory_viz(events)

var open_braces = 0
var close_braces = 0
var open_brackets = 0
var close_brackets = 0
var i = 0
while i < json.len():
    val ch = json.slice(i, i + 1)
    if ch == "{":
        open_braces = open_braces + 1
    elif ch == "}":
        close_braces = close_braces + 1
    elif ch == "[":
        open_brackets = open_brackets + 1
    elif ch == "]":
        close_brackets = close_brackets + 1
    i = i + 1

expect(open_braces).to_equal(close_braces)
expect(open_brackets).to_equal(close_brackets)
```

</details>

#### handles zero events without producing malformed output

- handles zero events without producing malformed output


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("handles zero events without producing malformed output")
val events: [DeviceAllocEvent] = []
val json = device_trace_to_memory_viz(events)

expect(json).to_contain("\"event_count\":0")
expect(json).to_contain("\"events\":[]")
```

</details>

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/gpu/mem_profile_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

Tests covering run_under_compute_sanitizer, device_trace_to_memory_viz.
- run_under_compute_sanitizer
- device_trace_to_memory_viz

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 5 |
| Active scenarios | 5 |
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

- Canonical SPipe generation for source `571e49a10652f963305c66e99601a57b8dca0c6c3eccebec5691022e7f3b94f3`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `571e49a10652f963305c66e99601a57b8dca0c6c3eccebec5691022e7f3b94f3`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `571e49a10652f963305c66e99601a57b8dca0c6c3eccebec5691022e7f3b94f3`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/lib/gpu/mem_profile_spec.spl
mirror: doc/06_spec/01_unit/lib/gpu/mem_profile_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/lib/gpu/mem_profile_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/gpu/mem_profile_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/gpu/mem_profile_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/lib/gpu/mem_profile_spec.spl:30:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'returns a clear 127 result when compute-sanitizer is not on PATH' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/mem_profile_spec.spl:49:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'emits a well-formed, versioned JSON snapshot with the right event count' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/gpu/mem_profile_spec.spl:64:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'names each event's owner and records ptr/bytes/kind' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
