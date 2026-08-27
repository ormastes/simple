# cuda_vm_executor_conformance_spec

> Runs every D3 conformance vector through the real svmg_cuda_kernel.ptx

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# cuda_vm_executor_conformance_spec

Runs every D3 conformance vector through the real svmg_cuda_kernel.ptx

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Runs every D3 conformance vector through the real svmg_cuda_kernel.ptx
    kernel on a live Cuda device, and separately confirms that a call-
    stack-overflow ("recursion depth") program produces a TRAP record
    (sentinel 0xCAFE007F, record{passed:0,value:3}) rather than a device
    loss / hang.

## Scenarios

### CudaVmExecutor -- SVM-G D3 conformance vectors on a live device

#### should skip cleanly, or run every conformance vector on a live device

- should skip cleanly, or run every conformance vector on a live device
- Probe for a Cuda-capable device
- cuda
- Load the checked-in svmg_cuda_kernel.ptx artifact
- Initialize the executor
- CUDA executor init failed on a live-GPU host:
- Run every D3 conformance vector and tally pass/fail
- Cuda device conformance: {passed}/{vectors.len() - 2} vectors passed
- Separately verify the excluded vector produces the DEVICE-correct
- Shut the executor down cleanly
   - Expected: executor.shutdown() equals ``
- Run budget_exhaustion_timeout as its own final step, through a
- budget_exhaustion_timeout: ok={timeout_outcome.ok}
- Shut the timed-out executor down: the latch surfaces as the


<details>
<summary>Executable SSpec</summary>

Runnable source: 96 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should skip cleanly, or run every conformance vector on a live device")
step("Probe for a Cuda-capable device")
val probe_result = _probe()

if probe_result.starts_with("skip:"):
    # Fail closed -- see lane_probe_verdict.spl. The old
    # `assert_true(probe_result.starts_with("skip:"))` passed BECAUSE
    # the probe skipped, so a lane that never touched a device reported
    # the same verdict as one that did.
    step(gpu_lane_probe_verdict_reason("cuda", probe_result))
    gpu_lane_report_skip("cuda vm executor lane", probe_result)
    assert_equal(gpu_lane_probe_verdict("cuda", probe_result), "skip")
else:
    step("Load the checked-in svmg_cuda_kernel.ptx artifact")
    val kernel_bytes = file_read_bytes(_KERNEL_PTX)
    expect(kernel_bytes.len()).to_be_greater_than(0)

    step("Initialize the executor")
    var executor = CudaVmExecutor.create()
    val init_err = executor.init(kernel_bytes)
    # A non-empty init_err on a host that got PAST the skip: probe is a
    # real defect, not a reason to pass. This host has two healthy
    # NVIDIA GPUs (RTX A6000 + TITAN RTX) on driver 580.126.16 with
    # libcuda.so.1 -> libcuda.so.580.126.16 (no userspace/kernel skew),
    # yet init fails with `cuda-lane-device-identity-unavailable`, so
    # this spec stays legitimately RED until that is fixed. See
    # doc/08_tracking/bug/cuda_lane_probe_misses_device_unavailable_2026-08-08.md
    if init_err != "":
        step("CUDA executor init failed on a live-GPU host: " + init_err)
        assert_equal(init_err, "")
    else:
        step("Run every D3 conformance vector and tally pass/fail")
        val vectors = all_vectors()
        var passed = 0
        var failed = 0
        var failed_names = ""
        for v in vectors:
            if v.name == _SELF_MODIFYING_CODE_DIVERGENCE_VECTOR:
                continue
            if v.name == _BUDGET_EXHAUSTION_TIMEOUT_VECTOR:
                continue
            val outcome = _run_vector(executor, v)
            val ok = (outcome.ok and outcome.trapped == v.expected_trapped and
                outcome.timed_out == v.expected_timed_out and
                outcome.sentinel == v.expected_sentinel and
                outcome.log_text == v.expected_log and
                outcome.records.len() == v.expected_records.len())
            if ok:
                passed = passed + 1
            else:
                failed = failed + 1
                failed_names = failed_names + v.name + " "
        step("Cuda device conformance: {passed}/{vectors.len() - 2} vectors passed " +
            "(2 excluded: {_SELF_MODIFYING_CODE_DIVERGENCE_VECTOR}, " +
            "{_BUDGET_EXHAUSTION_TIMEOUT_VECTOR}, see comments above)" +
            (if failed > 0: " (failed: " + failed_names + ")" else: ""))
        assert_equal(failed, 0)
        assert_equal(passed, vectors.len() - 2)

        step("Separately verify the excluded vector produces the DEVICE-correct " +
            "self-modified result (not ref_vm's host-side expectation)")
        var divergent_vector = vectors[0]
        for v in vectors:
            if v.name == _SELF_MODIFYING_CODE_DIVERGENCE_VECTOR:
                divergent_vector = v
        val divergent_outcome = _run_vector(executor, divergent_vector)
        assert_true(divergent_outcome.ok)
        assert_equal(divergent_outcome.records.len(), 1)
        if divergent_outcome.records.len() > 0:
            assert_equal(divergent_outcome.records[0].passed, _SELF_MODIFYING_CODE_DIVERGENT_PASS)
            assert_equal(divergent_outcome.records[0].value, 200)

        step("Shut the executor down cleanly")
        expect(executor.shutdown()).to_equal("")

        step("Run budget_exhaustion_timeout as its own final step, through a " +
            "FRESH session -- never sharing a session with any other vector, " +
            "because a genuine device timeout permanently latches the session " +
            "into completion_unknown/release_pending")
        var timeout_vector = vectors[0]
        for v in vectors:
            if v.name == _BUDGET_EXHAUSTION_TIMEOUT_VECTOR:
                timeout_vector = v
        var timeout_executor = CudaVmExecutor.create()
        val timeout_init_err = timeout_executor.init(kernel_bytes)
        assert_equal(timeout_init_err, "")
        val timeout_outcome = _run_vector(timeout_executor, timeout_vector)
        step("budget_exhaustion_timeout: ok={timeout_outcome.ok} " +
            "timed_out={timeout_outcome.timed_out}")
        # A real device timeout correctly makes ok:false -- this is the
        # DESIGNED outcome for this vector, not a defect.
        assert_false(timeout_outcome.ok)
        step("Shut the timed-out executor down: the latch surfaces as the " +
            "real, legitimate cleanup-pending message")
        assert_equal(timeout_executor.shutdown(), "cuda-lane-session-cleanup-pending")
```

</details>

#### should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)

- should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)
- Probe for a Cuda-capable device
- cuda
- Load the checked-in svmg_cuda_kernel.ptx artifact
- CUDA executor init failed on a live-GPU host:
- Run the call-stack-overflow program on the live device
- sentinel=0x{outcome.sentinel} trapped={outcome.trapped}
   - Expected: executor.shutdown() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 58 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)")
step("Probe for a Cuda-capable device")
val probe_result = _probe()

if probe_result.starts_with("skip:"):
    # Fail closed -- see lane_probe_verdict.spl. The old
    # `assert_true(probe_result.starts_with("skip:"))` passed BECAUSE
    # the probe skipped, so a lane that never touched a device reported
    # the same verdict as one that did.
    step(gpu_lane_probe_verdict_reason("cuda", probe_result))
    gpu_lane_report_skip("cuda vm executor lane", probe_result)
    assert_equal(gpu_lane_probe_verdict("cuda", probe_result), "skip")
else:
    step("Load the checked-in svmg_cuda_kernel.ptx artifact")
    val kernel_bytes = file_read_bytes(_KERNEL_PTX)
    var executor = CudaVmExecutor.create()
    val init_err = executor.init(kernel_bytes)
    # As above: past the skip: probe, a non-empty init_err is a real
    # defect on a live-GPU host, not a reason to pass. Stays RED until
    # doc/08_tracking/bug/cuda_lane_probe_misses_device_unavailable_2026-08-08.md
    # is fixed.
    if init_err != "":
        step("CUDA executor init failed on a live-GPU host: " + init_err)
        assert_equal(init_err, "")
    else:
        # 33 back-to-back CALLs into the very next instruction (each
        # CALL is 3 bytes: opcode+u16 target), pushing a return address
        # every time without ever RET-ing -- the 33rd CALL observes
        # csp==32 (CALL_STACK_SIZE) and must TRAP with TRAP_CALLOF(3),
        # not hang or crash the device. Vector not present by this name
        # in D3's table (no dedicated recursion-depth vector there);
        # constructed directly against the design's documented
        # call-stack-overflow trap contract (ref_vm.step's OP_CALL
        # panics host-side on overflow -- a device cannot panic, so it
        # maps to TRAP_CALLOF=3, matching svmg_cuda_kernel.ptx's
        # L_CALLSTACK_OVERFLOW convention that this kernel mirrors).
        var source = ""
        var i = 0
        while i < 33:
            source = source + "CALL {(i + 1) * 3}\n"
            i = i + 1
        source = source + "HALT 0"

        step("Run the call-stack-overflow program on the live device")
        val outcome = executor.run_source(source, 10000, 0)
        step("sentinel=0x{outcome.sentinel} trapped={outcome.trapped} " +
            "timed_out={outcome.timed_out} records={outcome.records.len()}")

        assert_true(outcome.ok)
        assert_false(outcome.timed_out)
        assert_true(outcome.trapped)
        assert_equal(outcome.sentinel, 0xCAFE007F)
        assert_equal(outcome.records.len(), 1)
        assert_equal(outcome.records[0].passed, 0)
        assert_equal(outcome.records[0].value, 3)

        expect(executor.shutdown()).to_equal("")
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

- Canonical SPipe generation for source `922e91cfeeca92f6aced5c28d0d494a90cd481a01ba5a6f04b5d942edb62b40c`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `922e91cfeeca92f6aced5c28d0d494a90cd481a01ba5a6f04b5d942edb62b40c`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `922e91cfeeca92f6aced5c28d0d494a90cd481a01ba5a6f04b5d942edb62b40c`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl
mirror: doc/06_spec/03_system/gpu_lane/cuda_vm_executor_conformance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gpu_lane/cuda_vm_executor_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gpu_lane/cuda_vm_executor_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl:104:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should skip cleanly, or run every conformance vector on a live device' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl:104:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should skip cleanly, or run every conformance vector on a live device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl:202:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/cuda_vm_executor_conformance_spec.spl:202:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
