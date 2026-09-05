# vulkan_vm_executor_conformance_spec

> Runs every D3 conformance vector through the real svmg_vulkan_kernel.spv

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_vm_executor_conformance_spec

Runs every D3 conformance vector through the real svmg_vulkan_kernel.spv

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Runs every D3 conformance vector through the real svmg_vulkan_kernel.spv
    shader on a live Vulkan device, and separately confirms that a call-
    stack-overflow ("recursion depth") program produces a TRAP record
    (sentinel 0xCAFE007F, record{passed:0,value:3}) rather than a device
    loss / hang.

## Scenarios

### VulkanVmExecutor -- SVM-G D3 conformance vectors on a live device

#### should skip cleanly, or run every conformance vector on a live device

- should skip cleanly, or run every conformance vector on a live device
- Probe for a Vulkan-capable device
- vulkan
- Load the checked-in svmg_vulkan_kernel.spv artifact
- Initialize the executor
   - Expected: init_err equals ``
- Run every D3 conformance vector and tally pass/fail
- Vulkan device conformance: {passed}/{vectors.len() - 1} vectors passed
- Separately verify the excluded vector produces the DEVICE-correct
- Shut the executor down cleanly
   - Expected: executor.shutdown() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 62 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should skip cleanly, or run every conformance vector on a live device")
step("Probe for a Vulkan-capable device")
val probe_result = _probe()

if probe_result.starts_with("skip:"):
    # Fail closed -- see lane_probe_verdict.spl. The old
    # `assert_true(probe_result.starts_with("skip:"))` passed BECAUSE
    # the probe skipped, so a lane that never touched a device reported
    # the same verdict as one that did.
    step(gpu_lane_probe_verdict_reason("vulkan", probe_result))
    gpu_lane_report_skip("vulkan vm executor lane", probe_result)
    assert_equal(gpu_lane_probe_verdict("vulkan", probe_result), "skip")
else:
    step("Load the checked-in svmg_vulkan_kernel.spv artifact")
    val kernel_bytes = file_read_bytes(_KERNEL_SPV)
    expect(kernel_bytes.len()).to_be_greater_than(0)

    step("Initialize the executor")
    var executor = VulkanVmExecutor.create()
    val init_err = executor.init(kernel_bytes)
    expect(init_err).to_equal("")

    step("Run every D3 conformance vector and tally pass/fail")
    val vectors = all_vectors()
    var passed = 0
    var failed = 0
    var failed_names = ""
    for v in vectors:
        if v.name == _SELF_MODIFYING_CODE_DIVERGENCE_VECTOR:
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
    step("Vulkan device conformance: {passed}/{vectors.len() - 1} vectors passed " +
        "(1 excluded: {_SELF_MODIFYING_CODE_DIVERGENCE_VECTOR}, see comment above)" +
        (if failed > 0: " (failed: " + failed_names + ")" else: ""))
    assert_equal(failed, 0)
    assert_equal(passed, vectors.len() - 1)

    step("Separately verify the excluded vector produces the DEVICE-correct " +
        "self-modified result (not ref_vm's host-side expectation)")
    var divergent_vector = vectors[0]
    for v in vectors:
        if v.name == _SELF_MODIFYING_CODE_DIVERGENCE_VECTOR:
            divergent_vector = v
    val divergent_outcome = _run_vector(executor, divergent_vector)
    assert_true(divergent_outcome.ok)
    assert_equal(divergent_outcome.records.len(), 1)
    assert_equal(divergent_outcome.records[0].passed, _SELF_MODIFYING_CODE_DIVERGENT_PASS)
    assert_equal(divergent_outcome.records[0].value, 200)

    step("Shut the executor down cleanly")
    expect(executor.shutdown()).to_equal("")
```

</details>

#### should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)

- should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)
- Probe for a Vulkan-capable device
- vulkan
- Load the checked-in svmg_vulkan_kernel.spv artifact
   - Expected: init_err equals ``
- Run the call-stack-overflow program on the live device
- sentinel=0x{outcome.sentinel} trapped={outcome.trapped}
   - Expected: executor.shutdown() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 52 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)")
step("Probe for a Vulkan-capable device")
val probe_result = _probe()

if probe_result.starts_with("skip:"):
    # Fail closed -- see lane_probe_verdict.spl. The old
    # `assert_true(probe_result.starts_with("skip:"))` passed BECAUSE
    # the probe skipped, so a lane that never touched a device reported
    # the same verdict as one that did.
    step(gpu_lane_probe_verdict_reason("vulkan", probe_result))
    gpu_lane_report_skip("vulkan vm executor lane", probe_result)
    assert_equal(gpu_lane_probe_verdict("vulkan", probe_result), "skip")
else:
    step("Load the checked-in svmg_vulkan_kernel.spv artifact")
    val kernel_bytes = file_read_bytes(_KERNEL_SPV)
    var executor = VulkanVmExecutor.create()
    val init_err = executor.init(kernel_bytes)
    expect(init_err).to_equal("")

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
    # L_CALLSTACK_OVERFLOW convention that this shader mirrors).
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

- Canonical SPipe generation for source `d248a3c4f1d378632ec53b16736c5b6e6b0d4c5a72a64625e0f8f969e0e8cd8a`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `d248a3c4f1d378632ec53b16736c5b6e6b0d4c5a72a64625e0f8f969e0e8cd8a`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `d248a3c4f1d378632ec53b16736c5b6e6b0d4c5a72a64625e0f8f969e0e8cd8a`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **92/100**; effective score: **92/100**; blockers: **0**.

SSpec documentization score: 92/100
source: test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl
mirror: doc/06_spec/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=90 oracle=100
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl:91:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should skip cleanly, or run every conformance vector on a live device' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl:91:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should skip cleanly, or run every conformance vector on a live device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl:155:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/vulkan_vm_executor_conformance_spec.spl:155:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
