# gpu_backend_failure_injection_spec

> Live CUDA/Vulkan ProcessingIR failure seams with process-isolated env.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 5 | 5 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_backend_failure_injection_spec

Live CUDA/Vulkan ProcessingIR failure seams with process-isolated env.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simpleos_gpu_host/gpu_backend_failure_injection_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Live CUDA/Vulkan ProcessingIR failure seams with process-isolated env.

## Scenarios

### live CUDA and Vulkan ProcessingIR fault injection

#### leaves the CUDA production default unmodified when the gate is absent

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- leaves the CUDA production default unmodified when the gate is absent


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves the CUDA production default unmodified when the gate is absent")
if _probe_mode(): return
expect(_assert_default("cuda")).to_contain(
    "backend=cuda phase=none fault_active=false")
```

</details>

#### leaves the Vulkan production default unmodified when the gate is absent

- leaves the Vulkan production default unmodified when the gate is absent
   - Expected: out does not contain `reason=vulkan-init-failed`


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("leaves the Vulkan production default unmodified when the gate is absent")
if _probe_mode(): return
val out = _run_case("vulkan", "none", false, false)
if out == VULKAN_RUNTIME_UNAVAILABLE:
    pending("existing runtime lacks rt_vulkan_dependency_quarantine_lock")
    return
expect(out).to_contain("GPU_FAULT_PROBE backend=vulkan phase=none fault_active=false")
expect(out.contains("reason=vulkan-init-failed")).to_equal(false)
if out.contains("completed=true"):
    expect(out).to_contain("reason=ok")
```

</details>

#### requires both fault gate variables

- requires both fault gate variables


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("requires both fault gate variables")
if _probe_mode(): return
expect(_run_case("cuda", "init", true, false)).to_contain(
    "phase=init fault_active=false")
expect(_run_case("cuda", "init", false, true)).to_contain(
    "phase=init fault_active=false")
```

</details>

#### returns typed CUDA unavailable, init, submit, readback, and mismatch failures

- returns typed CUDA unavailable, init, submit, readback, and mismatch failures
   - Expected: _assert_injected("cuda", "unavailable", "cuda-unavailable") is true
   - Expected: _assert_injected("cuda", "init", "cuda-init-failed") is true
   - Expected: _assert_injected("cuda", "submit", "cuda-submit-failed") is true
   - Expected: _assert_injected("cuda", "readback", "cuda-readback-failed") is true
   - Expected: _assert_injected("cuda", "mismatch", "checksum-mismatch") is true


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns typed CUDA unavailable, init, submit, readback, and mismatch failures")
if _probe_mode(): return
expect(_assert_injected("cuda", "unavailable", "cuda-unavailable")).to_equal(true)
expect(_assert_injected("cuda", "init", "cuda-init-failed")).to_equal(true)
expect(_assert_injected("cuda", "submit", "cuda-submit-failed")).to_equal(true)
expect(_assert_injected("cuda", "readback", "cuda-readback-failed")).to_equal(true)
expect(_assert_injected("cuda", "mismatch", "checksum-mismatch")).to_equal(true)
```

</details>

#### returns typed Vulkan lifecycle and dispatch failures

- returns typed Vulkan lifecycle and dispatch failures


<details>
<summary>Executable SSpec</summary>

Runnable source: 15 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("returns typed Vulkan lifecycle and dispatch failures")
if _probe_mode(): return
val unavailable = _run_case("vulkan", "unavailable", true, true)
if unavailable == VULKAN_RUNTIME_UNAVAILABLE:
    pending("existing runtime lacks rt_vulkan_dependency_quarantine_lock")
    return
expect(unavailable).to_contain(
    "backend=vulkan phase=unavailable fault_active=true completed=false reason=vulkan-unavailable values=0 handle=0 identity=0")
if not _assert_injected("vulkan", "init", "vulkan-init-failed") or
   not _assert_injected("vulkan", "submit", "vulkan-submit-failed") or
   not _assert_injected("vulkan", "readback", "vulkan-readback-failed") or
   not _assert_injected("vulkan", "mismatch", "checksum-mismatch") or
   not _assert_injected("vulkan", "dispatch-ineligible", "vulkan-dispatch-ineligible"):
    pending("existing runtime lacks rt_vulkan_dependency_quarantine_lock")
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

- `REQ-SSPEC-SYSTEM`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `9859969d0fbf8740c1a86f44afdf26e26c26413562543a8de9e88a445da01710`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `9859969d0fbf8740c1a86f44afdf26e26c26413562543a8de9e88a445da01710`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `9859969d0fbf8740c1a86f44afdf26e26c26413562543a8de9e88a445da01710`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/app/simpleos_gpu_host/gpu_backend_failure_injection_spec.spl
mirror: doc/06_spec/03_system/app/simpleos_gpu_host/gpu_backend_failure_injection_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/app/simpleos_gpu_host/gpu_backend_failure_injection_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simpleos_gpu_host/gpu_backend_failure_injection_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simpleos_gpu_host/gpu_backend_failure_injection_spec.spl:76:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves the CUDA production default unmodified when the gate is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/gpu_backend_failure_injection_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'leaves the Vulkan production default unmodified when the gate is absent' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simpleos_gpu_host/gpu_backend_failure_injection_spec.spl:96:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires both fault gate variables' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
