# simpleos_arm64_unified_live_adapter_spec

> Static contract for the one-guest ARM64 Vulkan/input/audio adapter.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 11 | 11 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# simpleos_arm64_unified_live_adapter_spec

Static contract for the one-guest ARM64 Vulkan/input/audio adapter.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Hardware & OS |
| Status | Active |
| Source | `test/01_unit/os/simpleos_arm64_unified_live_adapter_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Static contract for the one-guest ARM64 Vulkan/input/audio adapter.

## Scenarios

### ARM64 unified SimpleOS primitive adapter

#### launches all primitive devices in one QEMU process

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- launches all primitive devices in one QEMU process


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("launches all primitive devices in one QEMU process")
val source = file_read(WRAPPER)
expect(source).to_contain("guest_process_count=1")
expect(source).to_contain("-device ivshmem-plain,memdev=hostgpu")
expect(source).to_contain("-device virtio-keyboard-device")
expect(source).to_contain("-device virtio-mouse-device")
expect(source).to_contain("-device virtio-sound-device,audiodev=audio0")
expect(source).to_contain("--processing-backend=vulkan")
expect(source).to_contain("-device virtio-blk-device,drive=fontdisk")
expect(source).to_contain("readonly=on")
expect(source).to_contain("disk_sha256=")
```

</details>

#### uses the canonical audio probe before the canonical desktop

- uses the canonical audio probe before the canonical desktop


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("uses the canonical audio probe before the canonical desktop")
val source = file_read(ENTRY)
val audio = source.index_of("simpleos_virtio_snd_probe(\"aarch64\"")
val desktop = source.index_of("gui_entry_desktop_start(0u64")
expect(audio >= 0).to_be(true)
expect(desktop > audio).to_be(true)
expect(source).to_contain("SIMPLEOS_UNIFIED_PRIMITIVE_FAIL reason=audio")
```

</details>

#### injects modifier, click, drag, and wheel primitives

- injects modifier, click, drag, and wheel primitives


<details>
<summary>Executable SSpec</summary>

Runnable source: 13 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("injects modifier, click, drag, and wheel primitives")
val source = file_read(INPUT_INJECTOR)
expect(source).to_contain('"data": "ctrl"')
expect(source).to_contain('"data": "ctrl_r"')
expect(source).to_contain('"data": "alt"')
expect(source).to_contain('"data": "alt_r"')
expect(source).to_contain('"button": "left"')
expect(source).to_contain('"button": "wheel-up"')
expect(source).to_contain('"axis": "x", "value": 11')

val wrapper = file_read(WRAPPER)
expect(wrapper).to_contain("sequence=pointer_move,pointer_down,pointer_drag,pointer_up,pointer_wheel,left_ctrl_down,left_ctrl_up,right_ctrl_down,right_ctrl_up,left_alt_down,left_alt_up,right_alt_down,right_alt_up delivered=true")
```

</details>

#### exposes device identity only after strict DrawIR receipt validation

- exposes device identity only after strict DrawIR receipt validation


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("exposes device identity only after strict DrawIR receipt validation")
val source = file_read(EXECUTOR)
val validation = source.index_of("host_gpu_ivshmem_device_receipt_valid")
val evidence = source.index_of("host-gpu-device-evidence")
expect(validation >= 0).to_be(true)
expect(evidence > validation).to_be(true)
expect(source).to_contain("readback=device")
expect(source).to_contain("identity={" + "receipt.device_identity}")
expect(source).to_contain("submit_id={" + "receipt.submit_id}")
expect(source).to_contain("fence_completed={" + "receipt.fence_signaled}")
expect(source).to_contain("device_frame_id={" + "receipt.device_frame_id}")
```

</details>

#### carries submit, fence completion, and device frame identity on the wire

- carries submit, fence completion, and device frame identity on the wire


<details>
<summary>Executable SSpec</summary>

Runnable source: 10 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("carries submit, fence completion, and device frame identity on the wire")
val protocol = file_read(PROTOCOL)
val bridge = file_read(BRIDGE)
val host = file_read(HOST)
expect(protocol).to_contain("SIMPLEOS_HOST_GPU_WIRE_COMPLETION_FENCE_SIGNALED")
expect(protocol).to_contain("simpleos_host_gpu_submission_correlation_valid")
expect(bridge).to_contain("receipt.submit_id == expected_generation")
expect(bridge).to_contain("receipt.device_frame_id == expected_frame_id")
expect(host).to_contain("fence_completed=true")
```

</details>

#### enforces the primitive performance and memory budgets

- enforces the primitive performance and memory budgets


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("enforces the primitive performance and memory budgets")
val source = file_read(WRAPPER)
expect(source).to_contain("test \"$p95_us\" -le 16700")
expect(source).to_contain("test \"$max_rss_kib\" -le \"$showcase_combined_rss_budget_kib\"")
expect(source).to_contain("SIMPLEOS_ARM64_COMBINED_RSS_BUDGET_KIB:-1048576")
expect(source).to_contain("showcase-submit-fence-device-frame-correlation")
```

</details>

#### freezes the animated guest before correlating the PPM frame

- freezes the animated guest before correlating the PPM frame


<details>
<summary>Executable SSpec</summary>

Runnable source: 7 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("freezes the animated guest before correlating the PPM frame")
val source = file_read(INPUT_INJECTOR)
val stop = source.index_of("execute(sock, \"stop\")")
val dump = source.index_of("execute(sock, \"screendump\"")
expect(stop).to_be_greater_than(0)
expect(dump).to_be_greater_than(stop)
```

</details>

#### versions the extended submit and completion wire ABI

- versions the extended submit and completion wire ABI


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("versions the extended submit and completion wire ABI")
val source = file_read(PROTOCOL)
expect(source).to_contain("SIMPLEOS_HOST_GPU_PROTOCOL_VERSION: i64 = 2")
expect(source).to_contain("SIMPLEOS_HOST_GPU_WIRE_DEVICE_FRAME_ID: i64 = 336")
```

</details>

#### keeps an exact primitive pixel fixture against the canonical CPU oracle

- keeps an exact primitive pixel fixture against the canonical CPU oracle
   - Expected: source).to_contain("expect(core.buf[5] equals `expected)"`
   - Expected: source).to_contain("expect(core.buf[0] equals `0xFF102030u32)"`


<details>
<summary>Executable SSpec</summary>

Runnable source: 6 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("keeps an exact primitive pixel fixture against the canonical CPU oracle")
val source = file_read(CPU_ORACLE_FIXTURE)
expect(source).to_contain("oracle_src_over")
expect(source).to_contain("expect(core.buf[5]).to_equal(expected)")
expect(source).to_contain("expect(core.buf[0]).to_equal(0xFF102030u32)")
```

</details>

#### delegates final promotion to both environment profile admissions

- delegates final promotion to both environment profile admissions


<details>
<summary>Executable SSpec</summary>

Runnable source: 8 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("delegates final promotion to both environment profile admissions")
val source = file_read(VALIDATOR)
expect(source).to_contain("validate_arm64_simpleos_qemu_primitives")
expect(source).to_contain("validate_ui_environment_evidence")
expect(source).to_contain("UiEnvironmentEvidenceClass.LiveGuest")
expect(source).to_contain("primitive.status == UiEnvironmentAdmissionStatus.Pass")
expect(source).to_contain("combined.status == UiEnvironmentAdmissionStatus.Pass")
```

</details>

#### passes its no-QEMU launcher self test

- passes its no-QEMU launcher self test
   - Expected: result.2 equals `0`


<details>
<summary>Executable SSpec</summary>

Runnable source: 5 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-OS
step("passes its no-QEMU launcher self test")
val result = process_run("/bin/sh", [WRAPPER, "--self-test"])
expect(result.2).to_equal(0)
expect(result.0).to_contain("simpleos_arm64_unified_live_self_test=pass")
```

</details>

## Scenario Summary

| Metric | Count |
|--------|------:|
| Total scenarios | 11 |
| Active scenarios | 11 |
| Slow scenarios | 0 |
| Skipped scenarios | 0 |
| Pending scenarios | 0 |


</details>

<!-- sspec-maintain:traceability:start -->
## Traceability

Requirements covered by the scenarios in this manual:

- `REQ-SSPEC-OS`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `57f7c211d14fbfa17e066b0549268c400ad9a0353f18284e566a7fbc90d451a1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `57f7c211d14fbfa17e066b0549268c400ad9a0353f18284e566a7fbc90d451a1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `57f7c211d14fbfa17e066b0549268c400ad9a0353f18284e566a7fbc90d451a1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **90/100**; effective score: **90/100**; blockers: **0**.

SSpec documentization score: 90/100
source: test/01_unit/os/simpleos_arm64_unified_live_adapter_spec.spl
mirror: doc/06_spec/01_unit/os/simpleos_arm64_unified_live_adapter_spec.md (current)
findings: 6 blockers: 0
  narrative=100 structure=100 oracle=90
  traceability=100 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
doc/06_spec/01_unit/os/simpleos_arm64_unified_live_adapter_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/01_unit/os/simpleos_arm64_unified_live_adapter_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/01_unit/os/simpleos_arm64_unified_live_adapter_spec.spl:1:1: advice SSDOC-ORA-003 [oracle] (-10): 1 unexplained numeric expected value(s)
  why: Reviewers need to know why a magic expected value is authoritative.
  improve: Name the authoritative expected value or add a '# oracle:' explanation.
test/01_unit/os/simpleos_arm64_unified_live_adapter_spec.spl:29:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'launches all primitive devices in one QEMU process' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_arm64_unified_live_adapter_spec.spl:43:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'uses the canonical audio probe before the canonical desktop' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/01_unit/os/simpleos_arm64_unified_live_adapter_spec.spl:53:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'injects modifier, click, drag, and wheel primitives' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
<!-- sspec-maintain:scorecard:end -->
