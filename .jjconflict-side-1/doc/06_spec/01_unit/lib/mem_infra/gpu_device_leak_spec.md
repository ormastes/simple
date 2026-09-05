# GPU device-memory leak detection (M7 GPU lane)

> `test/01_unit/lib/gpu/mem_profile_device_counters_spec.spl` proves the `device_live_bytes()`/`device_peak_bytes()` counter ARITHMETIC in isolation (no GPU required, no allocation activity). It explicitly does NOT cover "device_live_bytes() actually increasing after a real rt_cuda_mem_alloc_fn call ... needs SIMPLE_MEM_ATTR=1 AND a CUDA driver AND a physical GPU" — its own header calls this gap out by name.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# GPU device-memory leak detection (M7 GPU lane)

`test/01_unit/lib/gpu/mem_profile_device_counters_spec.spl` proves the `device_live_bytes()`/`device_peak_bytes()` counter ARITHMETIC in isolation (no GPU required, no allocation activity). It explicitly does NOT cover "device_live_bytes() actually increasing after a real rt_cuda_mem_alloc_fn call ... needs SIMPLE_MEM_ATTR=1 AND a CUDA driver AND a physical GPU" — its own header calls this gap out by name.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Standard Library |
| Status | Active |
| Source | `test/01_unit/lib/mem_infra/gpu_device_leak_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

## Overview

`test/01_unit/lib/gpu/mem_profile_device_counters_spec.spl` proves the
`device_live_bytes()`/`device_peak_bytes()` counter ARITHMETIC in isolation
(no GPU required, no allocation activity). It explicitly does NOT cover
"device_live_bytes() actually increasing after a real rt_cuda_mem_alloc_fn
call ... needs SIMPLE_MEM_ATTR=1 AND a CUDA driver AND a physical GPU" — its
own header calls this gap out by name.

This spec closes that gap: it drives the real CUDA driver-API choke points
(`src/compiler_rust/compiler/src/interpreter_extern/gpu.rs`
`rt_cuda_mem_alloc_fn`/`rt_cuda_mem_free_fn`) on whatever GPU is actually
present, via `test/fixture/mem_infra/gpu_device_leak_workload.spl`, and
proves the counters detect a deliberately SEEDED device-memory leak — not
just that the arithmetic is internally consistent.

Per plan `doc/03_plan/runtime/memory_analysis/memory_infra_next_phase_plan_2026-07-29.md`
M7 exit: "seeded device leak ... fixtures caught". This spec is that fixture.

## Why a child process, not an in-process call

Mirrors `test/01_unit/compiler/interp/mem_guard_rate_spec.spl`'s
`run_with`/`contract_binary` pattern exactly, for the same reason stated
there: `SIMPLE_MEM_ATTR` gates a `OnceLock<bool>`
(`rt_mem_attr_enabled()`, `simple_runtime::value::heap`) latched on first
read, and `bin/simple test` spec bodies run under the session daemon, which
freezes env vars at daemon start — so flipping the gate mid-process from
inside a running spec would silently no-op. A genuine child process, forced
onto the interpreter engine (device-counter externs live in
`interpreter_extern`, not the native/cranelift `rt_alloc` path), is the only
way to observe the gate actually flip.

## GPU-less hosts

The fixture prints `no_cuda` and exits 0 when `cuda_available()` is false or
no device is present (verified via `cuda_device_count()`), and this spec
treats that path as an explicit, logged skip rather than a failure — the
same posture `mem_profile_device_counters_spec.spl` and
`gc_gpu_instrumentation_design.md` already take for GPU-less CI.

## Scenarios

### GPU device-memory leak detection (real CUDA driver, seeded defect)

#### runs cleanly and reports whether a CUDA device was available

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- runs cleanly and reports whether a CUDA device was available
- Run the device-leak workload fixture in a child process with SIMPLE_MEM_ATTR=1
- Confirm the child process exited cleanly and the extern is known


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("runs cleanly and reports whether a CUDA device was available")
step("Run the device-leak workload fixture in a child process with SIMPLE_MEM_ATTR=1")
val (out, err, code) = run_leak_workload_child()

step("Confirm the child process exited cleanly and the extern is known")
assert_equal(code, 0)
assert_equal(err.contains("unknown extern function"), false)
assert_equal(out.contains("gpu_device_leak_workload:"), true)
```

</details>

#### on a GPU-less host: reports no_cuda rather than a false leak signal

- on a GPU-less host: reports no_cuda rather than a false leak signal


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("on a GPU-less host: reports no_cuda rather than a false leak signal")
val (out, _err, _code) = run_leak_workload_child()
if out.contains("no_cuda"):
    assert_true(true, "no CUDA device present -- skip is the correct, honest result")
else:
    assert_true(out.contains("live_before="), "expected a real counter trace when CUDA is available")
```

</details>

#### a balanced alloc+free pair leaves live bytes exactly where it started

- a balanced alloc+free pair leaves live bytes exactly where it started


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("a balanced alloc+free pair leaves live bytes exactly where it started")
val (out, _err, _code) = run_leak_workload_child()
if out.contains("no_cuda"):
    assert_true(true, "skipped: no CUDA device present")
else:
    val before = extract_field(out, "gpu_device_leak_workload: live_before=")
    val after_balanced = extract_field(out, "gpu_device_leak_workload: live_after_balanced=")
    assert_equal(before, 0)
    assert_equal(after_balanced, 0)
```

</details>

#### SEEDED LEAK: an allocation with no matching free is caught -- live bytes equal exactly the leaked size

- SEEDED LEAK: an allocation with no matching free is caught -- live bytes equal exactly the leaked size
- Run the fixture: alloc " + ALLOC_SIZE.to_text() + " bytes on-device and deliberately skip the free
- Confirm device_live_bytes() reports exactly the leaked allocation, not 0 and not some other value


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("SEEDED LEAK: an allocation with no matching free is caught -- live bytes equal exactly the leaked size")
step("Run the fixture: alloc " + ALLOC_SIZE.to_text() + " bytes on-device and deliberately skip the free")
val (out, _err, _code) = run_leak_workload_child()
if out.contains("no_cuda"):
    assert_true(true, "skipped: no CUDA device present")
else:
    step("Confirm device_live_bytes() reports exactly the leaked allocation, not 0 and not some other value")
    val after_leak = extract_field(out, "gpu_device_leak_workload: live_after_leak=")
    assert_equal(after_leak, ALLOC_SIZE)
```

</details>

#### peak survives both the free and the leak, tracking cumulative high-water device usage

- peak survives both the free and the leak, tracking cumulative high-water device usage


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-LIB
step("peak survives both the free and the leak, tracking cumulative high-water device usage")
val (out, _err, _code) = run_leak_workload_child()
if out.contains("no_cuda"):
    assert_true(true, "skipped: no CUDA device present")
else:
    val peak_after_leak = extract_field(out, "gpu_device_leak_workload: peak_after_leak=")
    # The balanced pair and the leaked allocation are the same size,
    # so peak is reached at whichever alloc drove live bytes to
    # ALLOC_SIZE last (the leaked one) -- must be at least ALLOC_SIZE,
    # and must never be BELOW the leaked live-bytes reading itself.
    assert_true(peak_after_leak >= ALLOC_SIZE,
        "expected peak >= " + ALLOC_SIZE.to_text() + ", got " + peak_after_leak.to_text())
```

</details>

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

- `REQ-SSPEC-UNIT`
- `REQ-MEM-GPU-DEVICE-LEAK-001`
- `REQ-SSPEC-LIB`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `e9b41b70d4e75e03063e3193041c1eb02967b03c1d822e96fe1a30cdc618401e`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `e9b41b70d4e75e03063e3193041c1eb02967b03c1d822e96fe1a30cdc618401e`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `e9b41b70d4e75e03063e3193041c1eb02967b03c1d822e96fe1a30cdc618401e`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **86/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/01_unit/lib/mem_infra/gpu_device_leak_spec.spl
mirror: doc/06_spec/01_unit/lib/mem_infra/gpu_device_leak_spec.md (current)
findings: 6 blockers: 1
  narrative=100 structure=100 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=86; blocker cap makes effective=49
doc/06_spec/01_unit/lib/mem_infra/gpu_device_leak_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/lib/mem_infra/gpu_device_leak_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/lib/mem_infra/gpu_device_leak_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 2 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/01_unit/lib/mem_infra/gpu_device_leak_spec.spl:103:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'runs cleanly and reports whether a CUDA device was available' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/mem_infra/gpu_device_leak_spec.spl:114:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'on a GPU-less host: reports no_cuda rather than a false leak signal' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/lib/mem_infra/gpu_device_leak_spec.spl:123:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'a balanced alloc+free pair leaves live bytes exactly where it started' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
