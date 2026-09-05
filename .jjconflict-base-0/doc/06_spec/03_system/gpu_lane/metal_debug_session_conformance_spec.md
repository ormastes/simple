# metal_debug_session_conformance_spec

> Runs every D3 debug conformance vector's full launch SEQUENCE (break,

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# metal_debug_session_conformance_spec

Runs every D3 debug conformance vector's full launch SEQUENCE (break,

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gpu_lane/metal_debug_session_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Runs every D3 debug conformance vector's full launch SEQUENCE (break,
    inspect, resume, single-step) through the real svmg_metal_kernel.metal on
    a live Metal device, and diffs each launch field-for-field against both
    the declared expectation and the host reference VM. Skips cleanly, and
    says so, on any host without Metal.

## Scenarios

### MetalDebugSession -- DBG-1/PROF-1 debug vectors on a live device

#### should ship an MSL kernel and a non-empty debug vector table on every host

- should ship an MSL kernel and a non-empty debug vector table on every host
   - Expected: kernel_msl contains `svmg_interpret`


<details>
<summary>Executable SSpec</summary>

Runnable source: 14 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should ship an MSL kernel and a non-empty debug vector table on every host")
# Runs EVERYWHERE, including this Linux host -- so this file is not
# purely a skip. It checks the two inputs the device branch depends
# on, which are host-readable even though the device is not.
val kernel_msl = file_read_text(_KERNEL_MSL_PATH)
expect(kernel_msl.len()).to_be_greater_than(1000)
# The MSL entry point the pipeline is created for must be present in
# the source. This is a TEXT check, not a compile: there is no MSL
# compiler on this host, so a syntax error elsewhere in the kernel
# remains invisible here. See the tracking doc.
expect(kernel_msl.contains("svmg_interpret")).to_equal(true)
val vectors = all_debug_vectors()
expect(vectors.len()).to_be_greater_than(0)
```

</details>

#### should skip cleanly, or match ref_vm on every debug vector field

- should skip cleanly, or match ref_vm on every debug vector field
   - Expected: probe_result equals `_EXPECTED_HOST_SKIP`
- Vector:


<details>
<summary>Executable SSpec</summary>

Runnable source: 74 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should skip cleanly, or match ref_vm on every debug vector field")
val probe_result = _probe()

if probe_result.starts_with("skip:"):
    print "[metal_debug_session_conformance] SKIPPED: {probe_result} -- the DEVICE-RAN branch did NOT run"
    if _require_gpu():
        assert_equal("SKIPPED: " + probe_result, "DEVICE-RAN: metal")
    expect(probe_result).to_equal(_EXPECTED_HOST_SKIP)
else:
    print "[metal_debug_session_conformance] DEVICE-RAN: probe() returned no skip reason; the live-device branch is executing"
    val kernel_msl = file_read_text(_KERNEL_MSL_PATH)
    expect(kernel_msl.len()).to_be_greater_than(0)

    val vectors = all_debug_vectors()
    expect(vectors.len()).to_be_greater_than(0)
    var checked = 0

    for v in vectors:
        step("Vector: " + v.name)
        # Fresh session per vector -- see the header note on the
        # dispatch-timeout latch.
        var sess = MetalDebugSession.create()
        val opts = AttachOpts(
            step_budget: v.step_budget, entry_pc: v.entry_pc,
            log_cap: DEFAULT_LOG_CAP, profile: true)
        val err = sess.attach_kernel(kernel_msl, v.source, opts)
        assert_equal(err, "")

        val code = svmg_asm(v.source)
        var ref_arena = build_arena(code, [], v.step_budget, v.entry_pc, DEFAULT_LOG_CAP)

        if v.name == _BUDGET_EXPIRY_VECTOR:
            # NOT a skip, and NOT a kernel defect: an explicit,
            # asserted statement of a known LANE-LAYER limitation,
            # the exact Metal analogue of the CUDA and Vulkan ones.
            #
            # The kernel correctly writes SENTINEL_TIMEOUT
            # (0xDEAD0000) on budget exhaustion -- a normal, expected
            # SVM-G outcome. But MetalLaneSession decodes that same
            # sentinel as a DEVICE timeout
            # (METAL_LANE_TIMEOUT_SENTINEL is the same constant), so
            # the SVM-G budget sentinel is indistinguishable from a
            # real device hang at the lane layer.
            #
            # Asserting the exact failure mode (rather than skipping)
            # means this test goes RED the moment the conflation is
            # fixed, which is when the real diff below should start
            # running. Do NOT "fix" the lane to make this pass.
            print "[metal_debug_session_conformance] DEVICE-RAN: known lane-layer limitation -- SVM-G budget sentinel is read as a device timeout"
            val lone = v.launches[0]
            val devt = sess.launch(lone.resume, lone.single_step, lone.set_breakpoints, lone.breakpoints)
            assert_true(devt.timed_out or not devt.ok)
            sess.shutdown()
            continue

        var li = 0
        for lch in v.launches:
            val dev = sess.launch(lch.resume, lch.single_step, lch.set_breakpoints, lch.breakpoints)
            assert_equal(dev.error, "")
            assert_true(dev.ok)
            val ref_r = _ref_launch(code, ref_arena, lch)
            ref_arena = ref_r.arena
            _diff_device_vs_ref(v.name, li, dev, ref_r, lch)
            li = li + 1
            checked = checked + 1

        val shut = sess.shutdown()
        assert_equal(shut, "")

    print "[metal_debug_session_conformance] DEVICE-RAN: total launches diffed device-vs-ref: {checked}"
    expect(checked).to_be_greater_than(0)
    # Launch-count floor -- unreachable from the skip branch (count 0).
    expect(checked).to_be_greater_than(_MIN_DEVICE_LAUNCHES - 1)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 2 |
| Active scenarios | 2 |
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

- Canonical SPipe generation for source `83070fe9c0238a2288db9a01d28c99e7ca5b18123204590a244e84d4cf3709ac`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `83070fe9c0238a2288db9a01d28c99e7ca5b18123204590a244e84d4cf3709ac`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `83070fe9c0238a2288db9a01d28c99e7ca5b18123204590a244e84d4cf3709ac`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gpu_lane/metal_debug_session_conformance_spec.spl
mirror: doc/06_spec/03_system/gpu_lane/metal_debug_session_conformance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gpu_lane/metal_debug_session_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gpu_lane/metal_debug_session_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gpu_lane/metal_debug_session_conformance_spec.spl:212:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should ship an MSL kernel and a non-empty debug vector table on every host' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/metal_debug_session_conformance_spec.spl:212:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should ship an MSL kernel and a non-empty debug vector table on every host' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu_lane/metal_debug_session_conformance_spec.spl:228:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should skip cleanly, or match ref_vm on every debug vector field' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/metal_debug_session_conformance_spec.spl:228:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should skip cleanly, or match ref_vm on every debug vector field' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
