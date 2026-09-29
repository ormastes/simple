# simpleos_arm64_unified_showcase_evidence_spec

> Static admission coverage for the one-process ARM showcase evidence lane.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_arm64_unified_showcase_evidence_spec

Static admission coverage for the one-process ARM showcase evidence lane.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/01_unit/scripts/simpleos_arm64_unified_showcase_evidence_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Static admission coverage for the one-process ARM showcase evidence lane.

## Scenarios

### SimpleOS ARM64 unified showcase evidence

#### collects twenty completed device frames and nearest-rank p95

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- collects twenty completed device frames and nearest-rank p95


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("collects twenty completed device frames and nearest-rank p95")
val check = source("scripts/check/check-simpleos-arm64-unified-live.shs")
expect(check.contains("tail -n 20") and
    check.contains("test \"$sample_count\" -eq 20") and
    check.contains("sed -n '19p'") and
    check.contains("elapsed_us=//p")).to_equal(true)
```

</details>

#### captures the same live RAMFB session and measures both resident processes

- captures the same live RAMFB session and measures both resident processes


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("captures the same live RAMFB session and measures both resident processes")
val check = source("scripts/check/check-simpleos-arm64-unified-live.shs")
val qmp = source("scripts/check/qmp-send-virtio-input.py")
expect(check.contains("--capture-only \"$capture\"") and
    check.contains("/proc/$qemu_pid/status") and
    check.contains("/proc/$daemon_pid/status") and
    check.contains("showcase_capture_sha256") and
    check.contains("VmHWM:") and
    qmp.contains("execute(sock, \"screendump\"") and
    qmp.contains("validate_ppm_capture") and
    qmp.contains("capture is a uniform surface")).to_equal(true)
```

</details>

#### requires transient Vulkan font evidence and rejects every fallback marker

- requires transient Vulkan font evidence and rejects every fallback marker


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("requires transient Vulkan font evidence and rejects every fallback marker")
val check = source("scripts/check/check-simpleos-arm64-unified-live.shs")
val daemon = source("src/app/simpleos_gpu_host/daemon_runner.spl")
expect(check.contains("transient-vulkan-font-receipt-missing") and
    check.contains("font unavailable fallback=bitmap") and
    check.contains("fallback-used") and
    daemon.contains("font_device_executed=") and
    daemon.contains("font_atlas_upload_bytes=")).to_equal(true)
```

</details>

#### uses guest monotonic scene animation without host Tab substitution

- uses guest monotonic scene animation without host Tab substitution


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("uses guest monotonic scene animation without host Tab substitution")
val check = source("scripts/check/check-simpleos-arm64-unified-live.shs")
val qmp = source("scripts/check/qmp-send-virtio-input.py")
val guest = source("examples/09_embedded/simple_os/arch/arm64/gui_entry_desktop.spl")
expect(not qmp.contains("\"data\": \"tab\"") and
    guest.contains("source=guest-monotonic") and
    guest.contains("showcase_animation_next_us") and
    guest.contains("backend_required and preferred_backend_code == SIMPLEOS_HOST_GPU_BACKEND_VULKAN") and
    guest.contains("input_compositor.move_window(editor_id") and
    check.contains("distinct_checksums") and
    check.contains("showcase-animation-static") and
    check.contains("showcase_animation_status=pass")).to_equal(true)
```

</details>

#### requires distinct samples and correlates font and input rendering

- requires distinct samples and correlates font and input rendering


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("requires distinct samples and correlates font and input rendering")
val check = source("scripts/check/check-simpleos-arm64-unified-live.shs")
expect(check.contains("showcase-frame-identities-not-distinct") and
    check.contains("transient-font-frame-not-sampled") and
    check.contains("showcase-animation-device-correlation") and
    check.contains("keyboard-render-correlation-missing") and
    check.contains("pointer-render-correlation-missing")).to_equal(true)
```

</details>

#### binds latency to the accepted device receipt rather than wall-clock inference

- binds latency to the accepted device receipt rather than wall-clock inference


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SCRIPTS
step("binds latency to the accepted device receipt rather than wall-clock inference")
val executor = source("src/os/compositor/engine2d_wm_frame_executor.spl")
expect(executor.contains("readback=device checksum=") and
    executor.contains("scene_revision=") and
    executor.contains("elapsed_us=")).to_equal(true)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 6 |
| Active scenarios | 6 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-SCRIPTS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `c07919103ca7dcc2dcbc8e2f9498e7fb59869c42502bbf0b68d51cfa0c56cb42`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `c07919103ca7dcc2dcbc8e2f9498e7fb59869c42502bbf0b68d51cfa0c56cb42`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `c07919103ca7dcc2dcbc8e2f9498e7fb59869c42502bbf0b68d51cfa0c56cb42`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/01_unit/scripts/simpleos_arm64_unified_showcase_evidence_spec.spl
mirror: doc/06_spec/01_unit/scripts/simpleos_arm64_unified_showcase_evidence_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/scripts/simpleos_arm64_unified_showcase_evidence_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/scripts/simpleos_arm64_unified_showcase_evidence_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/scripts/simpleos_arm64_unified_showcase_evidence_spec.spl:23:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'collects twenty completed device frames and nearest-rank p95' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/simpleos_arm64_unified_showcase_evidence_spec.spl:46:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'requires transient Vulkan font evidence and rejects every fallback marker' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/scripts/simpleos_arm64_unified_showcase_evidence_spec.spl:57:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses guest monotonic scene animation without host Tab substitution' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
