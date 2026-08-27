# gpu_external_environment_qualification_spec

> Aggregate external-dependency qualification for GPU processing/rendering.

| Tests | Active | Skipped | Pending |
|-------|--------|---------|--------:|
| 6 | 6 | 0 | 0 |

<details>
<summary>Full Scenario Manual</summary>

# gpu_external_environment_qualification_spec

Aggregate external-dependency qualification for GPU processing/rendering.

## At a Glance

| Field | Value |
|-------|-------|
| Category | Application |
| Status | Active |
| Source | `test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl` |
| Updated | 2026-08-26 |
| Generator | `simple spipe-docgen` (Simple) |

Aggregate external-dependency qualification for GPU processing/rendering.

Presence and loadability never satisfy this spec. Physical rows require retained
execution/readback parity. Emulator rows remain typed as emulator. Missing
macOS Metal or Windows DirectX evidence deliberately keeps the aggregate red.

## Scenarios

### GPU external environment qualification

#### should define fail-closed external environment evidence in the glossary

**Manual warnings:**
- invalid manual visibility metadata: # @manual scenario evidence (expected show, folded, detail, or skip)


- should define fail-closed external environment evidence in the glossary
- Probe backend environment and wrapper ownership


<details>
<summary>Executable SSpec</summary>

Runnable source: 11 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should define fail-closed external environment evidence in the glossary")
step("Probe backend environment and wrapper ownership")
val glossary = file_read("doc/glossary.md")
expect(glossary).to_contain("## Environment Test")
expect(glossary).to_contain("presence")
expect(glossary).to_contain("loadability")
expect(glossary).to_contain("fully environment-qualified")
expect(glossary).to_contain("physical-device")
expect(glossary).to_contain("emulator")
expect(glossary).to_contain("CPU/GPU Communication Qualification")
```

</details>

#### should qualify physical Vulkan through its HAL and exact readback receipts

- should qualify physical Vulkan through its HAL and exact readback receipts
- Upload CPU input through the HAL
- Dispatch offloaded GPU rendering logic


<details>
<summary>Executable SSpec</summary>

Runnable source: 37 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should qualify physical Vulkan through its HAL and exact readback receipts")
step("Upload CPU input through the HAL")
val environment = file_read(VULKAN_ENV)
val communication = file_read(VULKAN_COMM)
expect(environment).to_contain("evidence_class=physical-device")
expect(environment).to_contain("owner=VulkanSession+Engine2D")
expect(environment).to_contain("loader=")
expect(environment).to_contain("loader_sha256=")
expect(environment).to_contain("validator=spirv-val")
expect(environment).to_contain("readiness=ready")
step("Dispatch offloaded GPU rendering logic")
expect(communication).to_contain("dispatch_count=2")
expect(communication).to_contain("byte_parity=pass")
expect(communication).to_contain("backend_handle=")
expect(communication).to_contain("device_identity=")
val compiler = file_read(VULKAN_COMPILER)
expect(compiler).to_contain("artifact_sha256=")
expect(compiler).to_contain("device_name=NVIDIA RTX A6000")
expect(compiler).to_contain("mismatch_count=0")
expect(compiler).to_contain("parity=pass")
val web = file_read(VULKAN_WEB)
expect(web).to_contain("producer=SimpleWebLayout+DrawIR+Engine2D")
expect(web).to_contain("readback_source=device_readback")
expect(web).to_contain("image_path=" + VULKAN_WEB_IMAGE)
expect(web).to_contain("event_log_path=" + VULKAN_WEB_EVENTS)
expect(web).to_contain("mismatch_count=0")
expect(web).to_contain("parity=pass")
val events = file_read(VULKAN_WEB_EVENTS)
expect(events).to_contain("\"sequence\":1,\"stage\":\"producer\"")
expect(events).to_contain("\"sequence\":2,\"stage\":\"draw_ir\"")
expect(events).to_contain("\"sequence\":3,\"stage\":\"engine2d\"")
expect(events).to_contain("\"sequence\":4,\"stage\":\"gpu_dispatch\"")
expect(events).to_contain("\"sequence\":5,\"stage\":\"device_readback\"")
expect(events).to_contain("\"backend_handle\":")
expect(events).to_contain("\"device_identity\":")
expect(events).to_contain("\"checksum\":248204808491526")
```

</details>

#### should qualify physical CUDA upload dispatch download and invalid transfers

- should qualify physical CUDA upload dispatch download and invalid transfers
- Download GPU output through the HAL


<details>
<summary>Executable SSpec</summary>

Runnable source: 12 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should qualify physical CUDA upload dispatch download and invalid transfers")
step("Download GPU output through the HAL")
val receipt = file_read(CUDA_RECEIPT)
expect(receipt).to_contain("PROCESSING_CUDA_HAL_HAPPY status=pass")
expect(receipt).to_contain("output=8,9,17,107")
expect(receipt).to_contain("PROCESSING_CUDA_HAL_REPEAT status=pass")
expect(receipt).to_contain("stable_identity=true")
expect(receipt).to_contain("PROCESSING_CUDA_HAL_ERROR status=pass")
expect(receipt).to_contain("invalid_upload_status=-1")
expect(receipt).to_contain("invalid_download_status=-1")
expect(receipt).to_contain("cpu_fallback=false")
```

</details>

<details>
<summary>Advanced: should retain the external environment classification matrix contract</summary>

#### should retain the external environment classification matrix contract

- should retain the external environment classification matrix contract
- Classify physical emulated and blocked evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should retain the external environment classification matrix contract")
step("Classify physical emulated and blocked evidence")
val matrix = "linux-vulkan=physical-device\nlinux-cuda=physical-device\nmetal-emulator=emulator\nmacos-metal=blocked\nwindows-directx=blocked\n"
expect(matrix).to_contain("linux-vulkan=physical-device")
expect(matrix).to_contain("linux-cuda=physical-device")
expect(matrix).to_contain("metal-emulator=emulator")
expect(matrix).to_contain("macos-metal=blocked")
expect(matrix).to_contain("windows-directx=blocked")
```

</details>


</details>

#### should classify Metal emulation without promoting it to physical execution

- should classify Metal emulation without promoting it to physical execution
- Classify physical emulated and blocked evidence


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should classify Metal emulation without promoting it to physical execution")
step("Classify physical emulated and blocked evidence")
val receipt = file_read(METAL_EMULATOR)
expect(receipt).to_contain("evidence_class=emulator")
expect(receipt).to_contain("native_device=false")
expect(receipt).to_contain("hal_owner=std.gc_async_mut.processing.metal_emulator")
expect(receipt).to_contain("rendering_parity=exact")
expect(receipt).to_contain("reason=ok")
```

</details>

<details>
<summary>Advanced: should keep the external matrix incomplete until native Metal and DirectX pass</summary>

#### should keep the external matrix incomplete until native Metal and DirectX pass

- should keep the external matrix incomplete until native Metal and DirectX pass
- Verify communication and rendering parity


<details>
<summary>Executable SSpec</summary>

Runnable source: 9 lines folded for reproduction.
Reproduction: this block contains the complete executable scenario source.

```simple
# @req REQ-SSPEC-SYSTEM
step("should keep the external matrix incomplete until native Metal and DirectX pass")
step("Verify communication and rendering parity")
val todos = file_read("doc/08_tracking/todo/todo_db.sdn")
expect(todos).to_contain("652, TODO, gpu, P1")
expect(todos).to_contain("653, TODO, gpu, P1")
expect(todos).to_contain("macOS")
expect(todos).to_contain("Windows x86_64")
fail_test("BLOCKED external environment matrix: native macOS Metal and Windows DirectX physical evidence remain open under TODO 652/653")
```

</details>


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

- `REQ-SSPEC-SYSTEM`
- `REQ-013`
- `REQ-014`
- `REQ-015`
<!-- sspec-maintain:traceability:end -->

<!-- sspec-maintain:provenance:start -->
## Generation history

- Canonical SPipe generation for source `a5a356f589d691d57133a56c5fed92ea44c7cabbfe171d8c3a0ab27528dee0b1`; maintenance tool `1`, rules `ssdoc-rules/1`.

Source SHA-256: `a5a356f589d691d57133a56c5fed92ea44c7cabbfe171d8c3a0ab27528dee0b1`.
<!-- sspec-maintain:provenance:end -->

<!-- sspec-maintain:scorecard:start -->
## SSpec documentization scorecard

Source SHA-256: `a5a356f589d691d57133a56c5fed92ea44c7cabbfe171d8c3a0ab27528dee0b1`  
Analyzer: `1`; rules: `ssdoc-rules/1`  
Raw score: **82/100**; effective score: **49/100**; blockers: **1**.

SSpec documentization score: 49/100
source: test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl
mirror: doc/06_spec/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.md (current)
findings: 12 blockers: 1
  narrative=100 structure=70 oracle=100
  traceability=60 evidence=70 coverage=100 maintainability=70
  cache=not-used suppressed=0
  lint-owned related rules=SPIPE001,SPIPE002,SPIPE003,SPIPE004,SPIPE005,SPIPE006,SPIPE007
  raw=82; blocker cap makes effective=49
doc/06_spec/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.md:1:1: advice SSDOC-MNT-005 [maintainability] (-10): generated manual lacks verification or troubleshooting guidance
  why: Operators need recovery and evidence interpretation guidance.
  improve: Author verification and recovery facts in SSpec and regenerate.
doc/06_spec/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.md:1:1: warning SSDOC-MNT-008 [maintainability] (-20): manual is missing: purpose, audience, scope, assumptions/preconditions, primary workflow, unsupported/limitations, recovery/troubleshooting
  why: A test dump is not a complete professional specification manual.
  improve: Author the missing facts in SSpec and regenerate through canonical SPipe docgen.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:1:1: blocker SSDOC-TRC-003 [traceability] (-40): 3 declared requirement(s) have no scenario binding
  why: A requirement list without scenario evidence is inventory, not traceability.
  improve: Bind the stable requirement ID inside its executable scenario or explicit blocked case.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:31:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should define fail-closed external environment evidence in the glossary' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:31:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should define fail-closed external environment evidence in the glossary' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:44:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should qualify physical Vulkan through its HAL and exact readback receipts' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:44:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should qualify physical Vulkan through its HAL and exact readback receipts' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:83:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should qualify physical CUDA upload dispatch download and invalid transfers' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:83:1: warning SSDOC-EVD-001 [evidence] (-10): visible scenario 'should qualify physical CUDA upload dispatch download and invalid transfers' has no retained capture or evidence
  why: Professional manuals need retained observable evidence.
  improve: Capture typed user/operator-facing evidence or explain why the oracle is complete.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:97:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should retain the external environment classification matrix contract' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:108:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should classify Metal emulation without promoting it to physical execution' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
test/03_system/app/simple_2d/feature/gpu_external_environment_qualification_spec.spl:119:1: advice SSDOC-BEH-002 [structure] (-5): scenario name 'should keep the external matrix incomplete until native Metal and DirectX pass' describes the test rather than its outcome
  why: Outcome names describe product behavior rather than test mechanics.
  improve: Rename it to the observable product outcome.
<!-- sspec-maintain:scorecard:end -->
