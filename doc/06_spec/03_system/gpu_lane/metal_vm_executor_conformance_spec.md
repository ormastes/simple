# metal_vm_executor_conformance_spec

> Either SKIPS with a named, asserted reason (every non-macOS host), or runs

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 4 | 4 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# metal_vm_executor_conformance_spec

Either SKIPS with a named, asserted reason (every non-macOS host), or runs

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Either SKIPS with a named, asserted reason (every non-macOS host), or runs
    every D3 conformance vector through the checked-in svmg_metal_kernel.metal
    on a live Metal device and proves the run was real via a launch-count
    floor. The spec output always states which of the two happened.

## Scenarios

### MetalVmExecutor -- SVM-G D3 conformance vectors on a live Metal device

#### should skip cleanly with a named reason, or run every conformance vector on a live device

- should skip cleanly with a named reason, or run every conformance vector on a live device
- Probe for a Metal-capable device
- Load the checked-in svmg_metal_kernel.metal source
- Initialize the executor (compiles MSL + builds the compute pipeline)
   - Expected: init_err equals ``
- Run every D3 conformance vector and tally pass/fail
- DEVICE-RAN: {launches} real device launches, {passed}/{vectors.len() - 1}
- Separately verify the excluded vector produces the DEVICE-correct
- Shut the executor down cleanly
   - Expected: executor.shutdown() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 74 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should skip cleanly with a named reason, or run every conformance vector on a live device")
step("Probe for a Metal-capable device")
val probe_result = _probe()

if probe_result.starts_with("skip:"):
    print("[metal_vm_executor_conformance] SKIPPED: " + probe_result +
        " (conformance-vector table) -- no Metal device on this host; " +
        "the DEVICE-RAN branch did NOT run")
    # Assert the SPECIFIC reason, not merely "some skip": a Mac that
    # skips for a different reason must not look identical to this.
    assert_equal(probe_result, _EXPECTED_HOST_SKIP)
else:
    print("[metal_vm_executor_conformance] DEVICE-RAN: live Metal device present " +
        "(conformance-vector table)")
    step("Load the checked-in svmg_metal_kernel.metal source")
    val kernel_msl = file_read_text(_KERNEL_MSL_PATH)
    expect(kernel_msl.len()).to_be_greater_than(0)

    step("Initialize the executor (compiles MSL + builds the compute pipeline)")
    var executor = MetalVmExecutor.create()
    val init_err = executor.init(kernel_msl)
    expect(init_err).to_equal("")

    step("Run every D3 conformance vector and tally pass/fail")
    val vectors = all_vectors()
    var launches = 0
    var passed = 0
    var failed = 0
    var failed_names = ""
    for v in vectors:
        if v.name == _SELF_MODIFYING_CODE_DIVERGENCE_VECTOR:
            continue
        val outcome = executor.run_source(v.source, v.step_budget, v.entry_pc)
        launches = launches + 1
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

    print("[metal_vm_executor_conformance] DEVICE-RAN: {launches} launches, " +
        "{passed} vectors passed")
    step("DEVICE-RAN: {launches} real device launches, {passed}/{vectors.len() - 1} " +
        "vectors passed (1 excluded: {_SELF_MODIFYING_CODE_DIVERGENCE_VECTOR})" +
        (if failed > 0: " (failed: " + failed_names + ")" else: ""))

    # POSITIVE PROOF the device branch really drove the device: a skip
    # path reaches zero launches, and no plausible short-circuit
    # reaches this floor.
    expect(launches).to_be_greater_than(_MIN_DEVICE_LAUNCHES)
    assert_equal(failed, 0)
    assert_equal(passed, vectors.len() - 1)

    step("Separately verify the excluded vector produces the DEVICE-correct " +
        "self-modified result (not ref_vm's host-side expectation)")
    var divergent_vector = vectors[0]
    for v in vectors:
        if v.name == _SELF_MODIFYING_CODE_DIVERGENCE_VECTOR:
            divergent_vector = v
    val divergent_outcome = executor.run_source(
        divergent_vector.source, divergent_vector.step_budget, divergent_vector.entry_pc)
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
- Probe for a Metal-capable device
   - Expected: init_err equals ``
- DEVICE-RAN: sentinel=0x{outcome.sentinel} trapped={outcome.trapped}
   - Expected: executor.shutdown() equals ``


<details>
<summary>Executable SSpec</summary>

Runnable source: 48 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)")
step("Probe for a Metal-capable device")
val probe_result = _probe()

if probe_result.starts_with("skip:"):
    print("[metal_vm_executor_conformance] SKIPPED: " + probe_result +
        " (call-stack-overflow trap) -- NOT verified on a device")
    assert_equal(probe_result, _EXPECTED_HOST_SKIP)
else:
    print("[metal_vm_executor_conformance] DEVICE-RAN: call-stack-overflow trap " +
        "on a live device")
    val kernel_msl = file_read_text(_KERNEL_MSL_PATH)
    var executor = MetalVmExecutor.create()
    val init_err = executor.init(kernel_msl)
    expect(init_err).to_equal("")

    # 33 back-to-back CALLs into the very next instruction (each CALL
    # is 3 bytes: opcode + u16 target), pushing a return address every
    # time without ever RET-ing -- the 33rd CALL observes
    # csp == CALL_STACK_SIZE (32) and must TRAP with TRAP_CALLOF(3),
    # not hang or lose the device. ref_vm.step PANICS here (a host/
    # assembler bug); a device cannot panic, so it maps to trap value
    # 3, matching svmg_cuda_kernel.ptx's L_CALLSTACK_OVERFLOW and the
    # SPIR-V sibling's %c_TRAP_CALLOF.
    var source = ""
    var i = 0
    while i < 33:
        source = source + "CALL {(i + 1) * 3}\n"
        i = i + 1
    source = source + "HALT 0"

    val outcome = executor.run_source(source, 10000, 0)
    step("DEVICE-RAN: sentinel=0x{outcome.sentinel} trapped={outcome.trapped} " +
        "timed_out={outcome.timed_out} records={outcome.records.len()}")

    assert_true(outcome.ok)
    assert_false(outcome.timed_out)
    assert_true(outcome.trapped)
    assert_equal(outcome.sentinel, 0xCAFE007F)
    # A trap is NOT a debug break, even though both live in the
    # 0xCAFE00xx family -- see metal_vm_executor.debug_break_of.
    assert_false(outcome.debug_break)
    assert_equal(outcome.records.len(), 1)
    assert_equal(outcome.records[0].passed, 0)
    assert_equal(outcome.records[0].value, 3)

    expect(executor.shutdown()).to_equal("")
```

</details>

#### should report the Metal probe reason unchanged through the executor wrapper

- should report the Metal probe reason unchanged through the executor wrapper
- MetalVmExecutor.probe forwards MetalLaneSession.probe verbatim, so a


<details>
<summary>Executable SSpec</summary>

Runnable source: 16 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should report the Metal probe reason unchanged through the executor wrapper")
step("MetalVmExecutor.probe forwards MetalLaneSession.probe verbatim, so a " +
    "caller can decide to skip before building anything device-side")
var executor = MetalVmExecutor.create()
val via_executor = executor.probe()
val via_session = _probe()
assert_equal(via_executor, via_session)

if via_executor.starts_with("skip:"):
    print("[metal_vm_executor_conformance] SKIPPED: " + via_executor +
        " (probe routing) -- routing verified on the skip path")
    assert_equal(via_executor, _EXPECTED_HOST_SKIP)
else:
    print("[metal_vm_executor_conformance] DEVICE-RAN: probe reports a usable device")
    assert_equal(via_executor, "")
```

</details>

#### should refuse to run before init, on ANY host (no device required)

- should refuse to run before init, on ANY host (no device required)
- This assertion runs on EVERY host, Metal or not: a run_source


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should refuse to run before init, on ANY host (no device required)")
step("This assertion runs on EVERY host, Metal or not: a run_source " +
    "before init must fail closed, never dispatch, never silently no-op")
var executor = MetalVmExecutor.create()
val outcome = executor.run_source("HALT 0", 1000, 0)
assert_false(outcome.ok)
assert_equal(outcome.error, "metal-vm-entry-not-loaded")
assert_equal(outcome.out_arena.len(), 0)
assert_false(outcome.debug_break)
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 4 |
| Active scenarios | 4 |
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

- Canonical SPipe generation for source `930ecf869de353801d3a776aceef7dd785677084b1600084386a91f69784b077`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `930ecf869de353801d3a776aceef7dd785677084b1600084386a91f69784b077`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `930ecf869de353801d3a776aceef7dd785677084b1600084386a91f69784b077`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **89/100**; effective score: **89/100**; blockers: **0**.

SSpec documentization score: 89/100
source: test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl
mirror: doc/06_spec/03_system/gpu_lane/metal_vm_executor_conformance_spec.md (current)
findings: 9 blockers: 0
  narrative=100 structure=80 oracle=100
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gpu_lane/metal_vm_executor_conformance_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gpu_lane/metal_vm_executor_conformance_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl:106:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should skip cleanly with a named reason, or run every conformance vector on a live device' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should skip cleanly with a named reason, or run every conformance vector on a live device' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl:182:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl:182:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should TRAP (not hang/device-lose) on call-stack overflow (33 nested CALLs, csp cap 32)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl:232:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should report the Metal probe reason unchanged through the executor wrapper' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl:232:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should report the Metal probe reason unchanged through the executor wrapper' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu_lane/metal_vm_executor_conformance_spec.spl:250:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should refuse to run before init, on ANY host (no device required)' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
