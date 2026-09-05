# vulkan_jit_hello_spec

> Vector-add-equivalent "hello" dispatch through jit(remote(vulkan(...))):

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 2 | 2 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# vulkan_jit_hello_spec

Vector-add-equivalent "hello" dispatch through jit(remote(vulkan(...))):

## At a Glance

| Field | Value |
|-------|-------|
| Category | Other |
| Status | Active |
| Source | `test/03_system/gpu_lane/vulkan_jit_hello_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Vector-add-equivalent "hello" dispatch through jit(remote(vulkan(...))):
    on a live Vulkan host this lowers the kernel via the existing SPIR-V
    emitter, assembles + optionally validates it, dispatches, fences, and
    drains the expected GMB-1 RECORD plus exit sentinel `0xCAFE0000` from
    the arena. On a host without a usable Vulkan device it SKIPs cleanly --
    matching the `probe().starts_with("skip:")` contract C1's own spec
    established.

## Scenarios

### vulkan_jit lane executor -- vector-add-equivalent hello dispatch (Task C2 verify)

#### computes a+b on a live Vulkan host and records RECORD(value=a+b) + sentinel 0xCAFE0000; SKIPs cleanly elsewhere

- computes a+b on a live Vulkan host and records RECORD(value=a+b) + sentinel 0xCAFE0000; SKIPs cleanly elsewhere
- Probe for a Vulkan-capable device before doing any real work
- vulkan
- Live Vulkan device found: create the executor and prepare() (lower to SPIR-V via the existing emitter, assemble with spirv-as, optionally validate with spirv-val, init the C1 session)
- prepare() failed for a reason other than device-absence (already handled above by the probe branch) -- this IS a real failure, not a skip
   - Expected: prepare_result.unwrap_err() equals ``
- Dispatch the hello kernel with operands a=7, b=35 (expected sum=42)
- Decode the RECORD ring + exit sentinel from the readback via A2's mailbox helpers
- Confirm the RECORD: seq=0, pass=true, value=42
   - Expected: records.len() equals `1`
   - Expected: records[0].seq equals `0`
   - Expected: records[0].value equals `42`
- Confirm the GMB-1 exit sentinel decodes to Exit with exit_code=0
   - Expected: sentinel_state equals `SentinelState.Exit`
   - Expected: exit_code equals `0`
- Tear down the session cleanly


<details>
<summary>Executable SSpec</summary>

Runnable source: 45 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("computes a+b on a live Vulkan host and records RECORD(value=a+b) + sentinel 0xCAFE0000; SKIPs cleanly elsewhere")
step("Probe for a Vulkan-capable device before doing any real work")
var probe_session = VulkanLaneSession.create()
val probe_result = probe_session.probe()

if probe_result.starts_with("skip:"):
    # Fail closed -- see lane_probe_verdict.spl. The old
    # `assert_true(probe_result.starts_with("skip:"))` passed BECAUSE
    # the probe skipped, so a lane that never touched a device reported
    # the same verdict as one that did.
    step(gpu_lane_probe_verdict_reason("vulkan", probe_result))
    gpu_lane_report_skip("vulkan jit hello lane", probe_result)
    assert_equal(gpu_lane_probe_verdict("vulkan", probe_result), "skip")
else:
    step("Live Vulkan device found: create the executor and prepare() (lower to SPIR-V via the existing emitter, assemble with spirv-as, optionally validate with spirv-val, init the C1 session)")
    var executor = VulkanJitLaneExecutor.create()
    val prepare_result = executor.prepare("vulkan_jit_hello")

    if not prepare_result.is_ok():
        step("prepare() failed for a reason other than device-absence (already handled above by the probe branch) -- this IS a real failure, not a skip")
        expect(prepare_result.unwrap_err()).to_equal("")
    else:
        step("Dispatch the hello kernel with operands a=7, b=35 (expected sum=42)")
        val blob = _u32_le(7) + _u32_le(35)
        val run_result = executor.run_program(blob)
        assert_true(run_result.is_ok())

        if run_result.is_ok():
            step("Decode the RECORD ring + exit sentinel from the readback via A2's mailbox helpers")
            val readback = run_result.unwrap()
            val (records, sentinel_state, exit_code) = decode_hello_result(readback)

            step("Confirm the RECORD: seq=0, pass=true, value=42")
            expect(records.len()).to_equal(1)
            expect(records[0].seq).to_equal(0)
            assert_true(records[0].pass)
            expect(records[0].value).to_equal(42)

            step("Confirm the GMB-1 exit sentinel decodes to Exit with exit_code=0")
            expect(sentinel_state).to_equal(SentinelState.Exit)
            expect(exit_code).to_equal(0)

        step("Tear down the session cleanly")
        assert_true(executor.teardown())
```

</details>

#### the assembled hello kernel validates cleanly with spirv-val when the tool is present on this host (host-aware optional)

- the assembled hello kernel validates cleanly with spirv-val when the tool is present on this host (host-aware optional)
- Probe for a Vulkan-capable device (spirv-val itself needs no device, but this spec only assembles the real kernel on a live-probe pass to avoid duplicating the prepare() path)
- vulkan
- skip: spirv-val not found on this host (host-aware optional check)
- prepare() already runs spirv-val internally and would have returned Err on a validation failure -- a successful prepare() is itself the positive proof


<details>
<summary>Executable SSpec</summary>

Runnable source: 26 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("the assembled hello kernel validates cleanly with spirv-val when the tool is present on this host (host-aware optional)")
step("Probe for a Vulkan-capable device (spirv-val itself needs no device, but this spec only assembles the real kernel on a live-probe pass to avoid duplicating the prepare() path)")
var probe_session = VulkanLaneSession.create()
val probe_result = probe_session.probe()

if probe_result.starts_with("skip:"):
    # Fail closed -- see lane_probe_verdict.spl. The old
    # `assert_true(probe_result.starts_with("skip:"))` passed BECAUSE
    # the probe skipped, so a lane that never touched a device reported
    # the same verdict as one that did.
    step(gpu_lane_probe_verdict_reason("vulkan", probe_result))
    gpu_lane_report_skip("vulkan jit hello lane", probe_result)
    assert_equal(gpu_lane_probe_verdict("vulkan", probe_result), "skip")
elif not spirv_tool_present("spirv-val"):
    step("skip: spirv-val not found on this host (host-aware optional check)")
    # Assert the branch's own precondition rather than a tautology, so
    # this example cannot silently pass if the branch is ever entered
    # for the wrong reason.
    assert_false(spirv_tool_present("spirv-val"))
else:
    step("prepare() already runs spirv-val internally and would have returned Err on a validation failure -- a successful prepare() is itself the positive proof")
    var executor = VulkanJitLaneExecutor.create()
    val prepare_result = executor.prepare("vulkan_jit_hello_spirv_val_check")
    assert_true(prepare_result.is_ok())
    assert_true(executor.teardown())
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

- Canonical SPipe generation for source `5eca2ec6c9415f241258730b3f05f97ade74515ce2ecfda2980fec8bc7ca72fa`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `5eca2ec6c9415f241258730b3f05f97ade74515ce2ecfda2980fec8bc7ca72fa`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `5eca2ec6c9415f241258730b3f05f97ade74515ce2ecfda2980fec8bc7ca72fa`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **88/100**; effective score: **88/100**; blockers: **0**.

SSpec documentization score: 88/100
source: test/03_system/gpu_lane/vulkan_jit_hello_spec.spl
mirror: doc/06_spec/03_system/gpu_lane/vulkan_jit_hello_spec.md (current)
findings: 5 blockers: 0
  narrative=100 structure=100 oracle=70
  traceability=100 evidence=80 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/03_system/gpu_lane/vulkan_jit_hello_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/gpu_lane/vulkan_jit_hello_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, primary workflow, evidence, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/gpu_lane/vulkan_jit_hello_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-30): 4 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/03_system/gpu_lane/vulkan_jit_hello_spec.spl:59:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'computes a+b on a live Vulkan host and records RECORD(value=a+b) + sentinel 0xCAFE0000; SKIPs cleanly elsewhere' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/gpu_lane/vulkan_jit_hello_spec.spl:106:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'the assembled hello kernel validates cleanly with spirv-val when the tool is present on this host (host-aware optional)' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
